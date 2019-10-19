mtype = {disconn, disable, enable, idle, preini, ini, postini, reqConn, 
	succGetWtr, failGetWtr, succUseWtr, failUseWtr, getNewWtr, useNewWtr, reqUpdate};

typedef clienttoCMComm {
	int client_id;
	mtype reqMessage;
}

chan CMtoWCP = [5] of {mtype};
chan WCPtoCM = [5] of {mtype};
chan clientstoCMOverall = [5] of {clienttoCMComm};	// overall channel for all clients to talk to CM to initialise
chan CMtoclients[10] = [5] of {mtype};
chan clientstoCM[10] = [5] of {mtype};

proctype client(int client_id) {
	bool getWtrSucc = 0;
	bool useWtrSucc = 0;
	mtype status = disconn;
	mtype message;
	
	clienttoCMComm req;
	req.client_id = client_id;

	do
	:: if
		:: (status == disconn) ->
			req.reqMessage = reqConn;
			clientstoCMOverall ! req;
		fi;
	
	:: CMtoclients[client_id] ? message -> 
		if
			:: (message == disconn) ->
				skip;
			:: (message == preini) ->
				status = preini;
			:: (message == ini) ->
				status = ini;

			:: (message == getNewWtr) ->
				if 
					:: (getWtrSucc == 1) ->
						getWtrSucc = 0;
						clientstoCM[client_id] ! succGetWtr;
					
					:: (getWtrSucc == 0) ->
						getWtrSucc = 1;
						clientstoCM[client_id] ! failGetWtr;
				fi;

			:: (message == useNewWtr) ->
				if
					:: (useWtrSucc == 1) ->
						useWtrSucc = 0;
						clientstoCM[client_id] ! succUseWtr;
					
					:: (useWtrSucc == 0) ->
						useWtrSucc = 1;
						clientstoCM[client_id] ! failUseWtr;
				fi;
		fi;
	od;
}

proctype CM() {
	mtype status = idle;
	clienttoCMComm clientReq;
	
	do
	:: clientstoCMOverall ? clientReq ->
		int client_id = clientReq.client_id;
		
		if
			:: (status == idle) ->
				status = preini;
				CMtoclients[client_id] ! preini;
				CMtoWCP ! disable;
			
			:: (status != idle) ->
				CMtoclients[client_id] ! disconn;
		fi;
				
		if 
			:: (status == preini) ->
				CMtoclients[client_id] ! getNewWtr;
				status = ini;
				CMtoclients[client_id] ! ini;
				mtype succOrFailGetWtr;
				
				do
				:: clientstoCM[client_id] ? succOrFailGetWtr ->
					if
						:: (succOrFailGetWtr == succGetWtr) ->
							CMtoclients[client_id] ! postini;
							status = postini;
							CMtoclients[client_id] ! useNewWtr;
							mtype succOrFailUseWtr;

							do
							:: clientstoCM[client_id] ? succOrFailUseWtr ->
								if
									:: (succOrFailUseWtr == succUseWtr) ->
										status = idle;
										CMtoclients[client_id] ! idle;
										CMtoWCP ! enable;
									
									:: (succOrFailUseWtr == failUseWtr) ->
										CMtoclients[client_id] ! disconn;
										CMtoWCP ! enable;
										status = idle;
								fi;
							od;

						:: (succOrFailGetWtr == failGetWtr) ->
							CMtoclients[client_id] ! disconn;
							status = idle;
					fi;
				od;
		fi;

	od
}

proctype WCP() {
	mtype status = enable;
	mtype message;
	
	do
	:: CMtoWCP ? message ->
		if 
		:: (message == disable) ->
			status = disable;
		fi;
	
	:: if
		:: (status == enable) ->
			WCPtoCM ! reqUpdate;
		fi;
	
	od;
}

init {
	run WCP();
	run client(0);
	run client(1);
	run client(2);
	run CM();
}