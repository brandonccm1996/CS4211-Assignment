mtype = {disconn, disable, enable, idle, preini, ini, postini, reqConn, 
	succGetWtr, failGetWtr, succUseWtr, failUseWtr, getNewWtr, useNewWtr, reqUpdate};

typedef clienttoCMComm {
	int client_id;
	mtype reqMessage;
}

chan CMtoWCP = [5] of {mtype};
chan WCPtoCM = [5] of {mtype};
chan CMtoclients[5] = [5] of {mtype};
chan clientstoCM[5] = [5] of {mtype};

// overall channel for all clients to talk to CM to initialise
// need to have this if not at the start when listening for reqConn messages, CM won't know which clientsToCM channel to listen to
chan clientstoCMOverall = [5] of {clienttoCMComm};

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

			CMtoclients[client_id] ? message -> 
			if
			:: (message == disconn) ->
				status = disconn;
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
		fi;
	od;
}

proctype CM() {
	mtype status = idle;
	clienttoCMComm clientReq;
	mtype message;
	
	do
	:: clientstoCMOverall ? clientReq ->
		int client_id = clientReq.client_id;
		
		if
		:: (status == idle && clientReq.reqMessage == reqConn) ->
			status = preini;
			CMtoclients[client_id] ! preini;
			CMtoWCP ! disable;
		
		:: (status != idle && clientReq.reqMessage == reqConn) ->
			CMtoclients[client_id] ! disconn;
		fi;
				
		if 
		:: (status == preini) ->
			CMtoclients[client_id] ! getNewWtr;
			status = ini;
			CMtoclients[client_id] ! ini;
			
			clientstoCM[client_id] ? message ->
			if
			:: (message == succGetWtr) ->
				CMtoclients[client_id] ! postini;
				status = postini;
				CMtoclients[client_id] ! useNewWtr;

				clientstoCM[client_id] ? message ->
				if
				:: (message == succUseWtr) ->
					status = idle;
					CMtoclients[client_id] ! idle;
					CMtoWCP ! enable;
				
				:: (message == failUseWtr) ->
					CMtoclients[client_id] ! disconn;
					CMtoWCP ! enable;
					status = idle;
				fi;

			:: (message == failGetWtr) ->
				CMtoclients[client_id] ! disconn;
				status = idle;
			fi;
		fi;
	od;
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