#define ARRAY_SIZE	20
#define NUM_CLIENTS	5

mtype = {disconn, disable, enable, idle, preini, ini, postini, reqConn, 
	succGetWtr, failGetWtr, succUseNewWtr, failUseNewWtr, getNewWtr, useNewWtr, reqUpdate,
	preupd, upd, postupd, postrev};

typedef clienttoCMReqRep {	// client to CM request/report
	int client_id;
	mtype message;
}

chan CMtoWCP = [ARRAY_SIZE] of {mtype};
chan WCPtoCM = [ARRAY_SIZE] of {mtype};
chan CMtoclients[NUM_CLIENTS] = [ARRAY_SIZE] of {mtype};

// overall channel for all clients to request/report to CM
chan clientstoCM = [ARRAY_SIZE] of {clienttoCMReqRep};

proctype client(int client_id) {
	bool getWtrSucc = 1;
	bool useWtrSucc = 1;
	mtype status = disconn;
	mtype CMInmessage;	// CM incoming message
	
	clienttoCMReqRep req_rep;
	req_rep.client_id = client_id;

	do
	:: (status == disconn) ->
		req_rep.message = reqConn;
		clientstoCM ! req_rep;
		
		do
		:: CMtoclients[client_id] ? CMInmessage ->
			if
			:: (CMInmessage == idle) ->
				status = idle;
			:: (CMInmessage == disconn) ->
				status = disconn;
				break;
			:: (CMInmessage == preini) ->
				status = preini;
			:: (CMInmessage == ini) ->
				status = ini;
			:: (CMInmessage == postini) ->
				status = postini;
			:: (CMInmessage == getNewWtr) ->
				if 
				:: (getWtrSucc == 1) ->
					getWtrSucc = 0;
					req_rep.message = succGetWtr;
					clientstoCM ! req_rep;
				
				:: (getWtrSucc == 0) ->
					getWtrSucc = 1;
					req_rep.message = failGetWtr;
					clientstoCM ! req_rep;
				fi;
			
			:: (CMInmessage == useNewWtr) -> 
				if
				:: (useWtrSucc == 1) ->
					useWtrSucc = 0;
					req_rep.message = succUseNewWtr;
					clientstoCM ! req_rep;
				
				:: (useWtrSucc == 0) ->
					useWtrSucc = 1;
					req_rep.message = failUseNewWtr;
					clientstoCM ! req_rep;
				fi;
			fi;
		od;
	od;
}

proctype CM() {
	mtype status = idle;
	clienttoCMReqRep clientInReqRep;	// client incoming request/report
	mtype message;
	int clientConnecting;
	int clientToRefuse;
	
	do
	:: clientstoCM ? clientInReqRep ->
		if
		:: (status == idle && clientInReqRep.message == reqConn) ->
			clientConnecting = clientInReqRep.client_id;	// clientConnecting can only be changed here i.e. if CM status is idle and it gets reqConn from client
			status = preini;
			CMtoclients[clientConnecting] ! preini;
			CMtoWCP ! disable;

			(status == preini) ->
				CMtoclients[clientConnecting] ! getNewWtr;
				status = ini;
				CMtoclients[clientConnecting] ! ini;
		
		:: (status != idle && clientInReqRep.message == reqConn) ->
			clientToRefuse = clientInReqRep.client_id;
			CMtoclients[clientToRefuse] ! disconn;

		// :: (status == preini) ->
		// 	CMtoclients[clientConnecting] ! getNewWtr;
		// 	status = ini;

		:: (clientInReqRep.message == succGetWtr) ->
			CMtoclients[clientConnecting] ! useNewWtr;
			status = postini;
			CMtoclients[clientConnecting] ! postini;
		
		:: (clientInReqRep.message == failGetWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			status = idle;

		:: (clientInReqRep.message == succUseNewWtr) ->
			status = idle;
			CMtoclients[clientConnecting] ! idle;
			CMtoWCP ! enable;

		:: (clientInReqRep.message == failUseNewWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			CMtoWCP ! enable;
			status = idle;
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
		:: (message == enable) ->
			status = enable;
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