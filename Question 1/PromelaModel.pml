#define ARRAY_SIZE	20
#define NUM_CLIENTS	5

mtype = {disconn, disable, enable, idle, preini, ini, postini, reqConn, 
	succGetWtr, failGetWtr, succUseNewWtr, failUseNewWtr, succUseOldWtr, failUseOldWtr, 
	getNewWtr, useNewWtr, useOldWtr, reqUpdate, preupd, upd, postupd, postrev};

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
	bool useNewWtrSucc = 1;
	bool useOldWtrSucc = 1;
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
			:: (CMInmessage == preupd) ->
				status = preupd;
			:: (CMInmessage == upd) ->
				status = upd;
			:: (CMInmessage == postupd) ->
				status = postupd;
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
				:: (useNewWtrSucc == 1) ->
					useNewWtrSucc = 0;
					req_rep.message = succUseNewWtr;
					clientstoCM ! req_rep;
				
				:: (useNewWtrSucc == 0) ->
					useNewWtrSucc = 1;
					req_rep.message = failUseNewWtr;
					clientstoCM ! req_rep;
				fi;

			:: (CMInmessage == useOldWtr) -> 
				if
				:: (useOldWtrSucc == 1) ->
					useOldWtrSucc = 0;
					req_rep.message = succUseOldWtr;
					clientstoCM ! req_rep;
				
				:: (useOldWtrSucc == 0) ->
					useOldWtrSucc = 1;
					req_rep.message = failUseOldWtr;
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

	int clientsConnected [NUM_CLIENTS];
	int numClientsConnected = 0;
	int dummy = 0;
	int dummy2 = 0;
	int numClientsReportSuccGetWtr = 0;
	int numClientsReportSuccUseNewWtr = 0;
	int numClientsReportSuccUseOldWtr = 0;

	mtype WCPInMessage;
	
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

		:: (status == ini && clientInReqRep.message == succGetWtr) ->
			CMtoclients[clientConnecting] ! useNewWtr;
			status = postini;
			CMtoclients[clientConnecting] ! postini;
		
		:: (status == ini && clientInReqRep.message == failGetWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			status = idle;

		:: (status == postini && clientInReqRep.message == succUseNewWtr) ->
			status = idle;
			CMtoclients[clientConnecting] ! idle;
			CMtoWCP ! enable;
			clientsConnected[numClientsConnected] = clientConnecting;
			numClientsConnected = numClientsConnected + 1;

		:: (status == postini && clientInReqRep.message == failUseNewWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			CMtoWCP ! enable;
			status = idle;

		:: (status == upd && clientInReqRep.message == succGetWtr) ->
			numClientsReportSuccGetWtr = numClientsReportSuccGetWtr + 1;
			(numClientsReportSuccGetWtr == numClientsConnected) ->
				do
				:: CMtoclients[clientsConnected[dummy2]] ! useNewWtr;
					dummy2 = dummy2 + 1;
					(dummy2 == numClientsConnected) ->
						dummy2 = 0;
						break;
				od;
				status = postupd;
				do
				:: CMtoclients[clientsConnected[dummy2]] ! postupd;
					dummy2 = dummy2 + 1;
					(dummy2 == numClientsConnected) ->
						dummy2 = 0;
						break;
				od;
				numClientsReportSuccGetWtr = 0;	// reset
		
		:: (status == upd && clientInReqRep.message == failGetWtr) ->
			numClientsReportSuccGetWtr = 0;	// reset
			do
			:: CMtoclients[clientsConnected[dummy2]] ! useOldWtr;
				dummy2 = dummy2 + 1;
				(dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
			od;
			status = postrev;
			do
			:: CMtoclients[clientsConnected[dummy2]] ! postrev;
				dummy2 = dummy2 + 1;
				(dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
			od;
		
		:: (status == postupd && clientInReqRep.message == succUseNewWtr) ->
			numClientsReportSuccUseNewWtr = numClientsReportSuccUseNewWtr + 1;
			(numClientsReportSuccGetWtr == numClientsConnected) ->
				status = idle;
				do
				:: CMtoclients[clientsConnected[dummy2]] ! idle;
					dummy2 = dummy2 + 1;
					(dummy2 == numClientsConnected) ->
						dummy2 = 0;
						break;
				od;
				CMtoWCP ! enable;
				numClientsReportSuccUseNewWtr = 0;	// reset

		:: (status == postupd && clientInReqRep.message == failUseNewWtr) ->
			numClientsReportSuccUseNewWtr = 0;	// reset
			do
			:: CMtoclients[clientsConnected[dummy2]] ! disconn;
				dummy2 = dummy2 + 1;
				(dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
			od;
			numClientsConnected = 0;	// reset
			CMtoWCP ! enable;
			status = idle;

		:: (status == postrev && clientInReqRep.message == succUseOldWtr) ->
			numClientsReportSuccUseOldWtr = numClientsReportSuccUseOldWtr + 1;
			(numClientsReportSuccUseOldWtr == numClientsConnected) ->
				status = idle;
				do
				:: CMtoclients[clientsConnected[dummy2]] ! idle;
					dummy2 = dummy2 + 1;
					(dummy2 == numClientsConnected) ->
						dummy2 = 0;
						break;
				od;
				CMtoWCP ! enable;

		:: (status == postrev && clientInReqRep.message == failUseOldWtr) ->
			numClientsReportSuccUseOldWtr = 0;	// reset
			do
			:: CMtoclients[clientsConnected[dummy2]] ! disconn;
				dummy2 = dummy2 + 1;
				(dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
			od;
			numClientsConnected = 0;	// reset
			CMtoWCP ! enable;
			status = idle;
		fi;
	
	:: WCPtoCM ? WCPInMessage ->
		if
		:: (status == idle && WCPInMessage == reqUpdate) ->
			status = preupd;
			do
			:: CMtoclients[clientsConnected[dummy]] ! preupd;
				dummy = dummy + 1;
				(dummy == numClientsConnected) -> 
					dummy = 0;
					break;
			od;
			
			CMtoWCP ! disable;
			(status == preupd) ->
				do
				:: CMtoclients[clientsConnected[dummy]] ! getNewWtr;
					dummy = dummy + 1;
					(dummy == numClientsConnected) -> 
						dummy = 0;
						break;
				od;
		fi;
	od;
}

proctype WCP() {
	mtype status = enable;
	mtype message;
	
	do
	:: (status == enable) ->
		WCPtoCM ! reqUpdate;
		
		do
		:: CMtoWCP ? message ->
			if
			:: (message == disable) ->
				status = disable;
			:: (message == enable) ->
				status = enable;
				break;
			fi;
		od;
	od;
}

init {
	run WCP();
	run client(1);
	run client(2);
	run client(3);
	run CM();
}