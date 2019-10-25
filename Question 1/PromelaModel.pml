#define ARRAY_SIZE	7
#define NUM_CLIENTS	5

mtype = {disconn, disable, enable, idle, preini, ini, postini, reqConn, 
	succGetWtr, failGetWtr, succUseNewWtr, failUseNewWtr, succUseOldWtr, failUseOldWtr, 
	getNewWtr, useNewWtr, useOldWtr, reqUpdate, preupd, upd, postupd, postrev};

typedef clienttoCMReqRep {	// client to CM request/report
	int client_id;
	mtype message;
}

chan WCPtoCM = [ARRAY_SIZE] of {mtype};
chan CMtoclients[NUM_CLIENTS] = [ARRAY_SIZE] of {mtype};

// overall channel for all clients to request/report to CM
chan clientstoCM = [ARRAY_SIZE] of {clienttoCMReqRep};

mtype WCPstatus = enable;
mtype clientsStatus[NUM_CLIENTS] = {disconn, disconn, disconn, disconn, disconn};

proctype client(int client_id) {
	mtype CMInmessage;	// CM incoming message
	
	clienttoCMReqRep req_rep;
	req_rep.client_id = client_id;

	do
	// A disconnected weather-aware client can establish a connection by sending a connecting request to the CM.
	:: (clientsStatus[client_id] == disconn) ->
		req_rep.message = reqConn;
		clientstoCM ! req_rep;
		
		do
		:: CMtoclients[client_id] ? CMInmessage ->
			if
			:: (CMInmessage == disconn) ->
				clientsStatus[client_id] = disconn;
				break;

			:: (CMInmessage == getNewWtr) ->
				if
				:: req_rep.message = succGetWtr;
				:: req_rep.message = failGetWtr;
				fi;
				clientstoCM ! req_rep;
			
			:: (CMInmessage == useNewWtr) -> 
				if
				:: req_rep.message = succUseNewWtr;
				:: req_rep.message = failUseNewWtr;
				fi;
				clientstoCM ! req_rep;

			:: (CMInmessage == useOldWtr) -> 
				if
				:: req_rep.message = succUseOldWtr;
				:: req_rep.message = failUseOldWtr;
				fi;
				clientstoCM ! req_rep;
			fi;
		od;
	od;
}

proctype CM() {
	mtype status = idle;
	clienttoCMReqRep clientInReqRep;	// client incoming request/report
	int clientConnecting;

	int clientsConnected [NUM_CLIENTS];
	int numClientsConnected = 0;
	int dummy = 0;
	int dummy2 = 0;
	int numClientsReportSuccGetWtr = 0;
	int numClientsReportSuccUseNewWtr = 0;
	int numClientsReportSuccUseOldWtr = 0;

	mtype WCPInMessage;
	
	do
	:: // When the CM is pre-initializing, it will send a message to instruct the newly connected client to get
		// the new weather information, and then set both its own status and the clients status to initializing.
		(status == preini) ->
			CMtoclients[clientConnecting] ! getNewWtr;
			status = ini;
			clientsStatus[clientConnecting] = ini;

	:: // When CMs status is pre-updating, it will send messages to instruct all connected clients to get the new
		// weather information, and then set its own status and the clients status to updating.
		(status == preupd) ->
			do
			:: (dummy != numClientsConnected) ->
				CMtoclients[clientsConnected[dummy]] ! getNewWtr;
				dummy = dummy + 1;
			:: (dummy == numClientsConnected) -> 
				dummy = 0;
				break;
			od;
			status = upd;
			do
			:: (dummy != numClientsConnected) ->
				clientsStatus[clientsConnected[dummy]] = upd;
				dummy = dummy + 1;
			:: (dummy == numClientsConnected) -> 
				dummy = 0;
				break;
			od;
	
	:: clientstoCM ? clientInReqRep ->
		if
		
		/* ********** CLIENT INITIALIZATION ********** */

		// If the CMs status is idle when the connecting request is received, it will set both its own status and the 
		// connecting clients status to pre-initializing, and disable the weather control panel
		:: (status == idle && clientInReqRep.message == reqConn) ->
			clientConnecting = clientInReqRep.client_id;	// clientConnecting can only be changed here i.e. if CM status is idle and it gets reqConn from client
			status = preini;
			clientsStatus[clientConnecting] = preini;
			WCPstatus = disable;

		// Otherwise (CMs status is not idle), the CM will send a message to the client to refuse the connection,
		// and the client remains disconnected.
		:: (status != idle && clientInReqRep.message == reqConn) ->
			CMtoclients[clientInReqRep.client_id] ! disconn;

		// If the client reports success for getting the new weather, the CM will send another message to inform
		// the client to use the weather information, and then set both its own status and the clients status to post-initializing.
		:: (status == ini && clientInReqRep.message == succGetWtr) ->
			CMtoclients[clientConnecting] ! useNewWtr;
			status = postini;
			clientsStatus[clientConnecting] = postini;
		
		// Otherwise, if getting new weather fails, the CM will disconnect the client and set its own status back to idle.
		:: (status == ini && clientInReqRep.message == failGetWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			status = idle;

		// If the client reports success for using the new weather, this initialization process is completed. the
		// CM will set both its own status and the clients status to idle, and re-enable the WCP
		:: (status == postini && clientInReqRep.message == succUseNewWtr) ->
			status = idle;
			clientsStatus[clientConnecting] = idle;
			WCPstatus = enable;
			clientsConnected[numClientsConnected] = clientConnecting;
			numClientsConnected = numClientsConnected + 1;

		// Otherwise, if using new weather fails, the CM will disconnect the client, re-enable the WCP, and set its own status back to idle.
		:: (status == postini && clientInReqRep.message == failUseNewWtr) ->
			CMtoclients[clientConnecting] ! disconn;
			WCPstatus = enable;
			status = idle;


		/* ********** WEATHER UPDATE ********** */

		// If all the clients report success for getting the new weather, the CM will send messages to inform
		// the clients to use the new weather information, and then set its own status and the clients status to post-updating.
		:: (clientInReqRep.message == succGetWtr) ->
			numClientsReportSuccGetWtr = numClientsReportSuccGetWtr + 1;
			if
			:: (numClientsReportSuccGetWtr == numClientsConnected) ->
				do
				:: (dummy2 != numClientsConnected) ->
					CMtoclients[clientsConnected[dummy2]] ! useNewWtr;
					dummy2 = dummy2 + 1;
				:: (dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
				od;
				status = postupd;
				do
				:: (dummy2 != numClientsConnected) ->
					clientsStatus[clientsConnected[dummy2]] = postupd;
					dummy2 = dummy2 + 1;
				:: (dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
				od;
				numClientsReportSuccGetWtr = 0;	// reset
			:: (numClientsReportSuccGetWtr != numClientsConnected) ->
				skip;
			fi;
		
		// Otherwise, if any of the connected clients reports failure for getting the new weather, the CM will send messages to 
		// all clients to use their old weather information, and then set its own status and the clients status to post-reverting.
		:: (clientInReqRep.message == failGetWtr) ->
			numClientsReportSuccGetWtr = 0;	// reset
			do
			:: (dummy2 != numClientsConnected) ->
				CMtoclients[clientsConnected[dummy2]] ! useOldWtr;
				dummy2 = dummy2 + 1;
			:: (dummy2 == numClientsConnected) ->
				dummy2 = 0;
				break;
			od;
			status = postrev;
			do
			:: (dummy2 != numClientsConnected) ->
				clientsStatus[clientsConnected[dummy2]] = postrev;
				dummy2 = dummy2 + 1;
			:: (dummy2 == numClientsConnected) ->
				dummy2 = 0;
				break;
			od;
		
		// When CMs status is post-updating, if all the clients report success for using the new weather, the
		// updating is completed. The CM will set its own status and the clients status to idle, and re-enable the WCP.
		:: (status == postupd && clientInReqRep.message == succUseNewWtr) ->
			numClientsReportSuccUseNewWtr = numClientsReportSuccUseNewWtr + 1;
			if
			:: (numClientsReportSuccUseNewWtr == numClientsConnected) ->
				status = idle;
				do
				:: (dummy2 != numClientsConnected) ->
					clientsStatus[clientsConnected[dummy2]] = idle;
					dummy2 = dummy2 + 1;
				:: (dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
				od;
				WCPstatus = enable;
				numClientsReportSuccUseNewWtr = 0;	// reset
			:: (numClientsReportSuccUseNewWtr != numClientsConnected) ->
				skip;
			fi;

		// Otherwise, if any of the connected clients reports failure for using the new weather, the CM
		// will disconnect all connected clients, re-enable the WCP, and set its own status back to idle.
		:: (status == postupd && clientInReqRep.message == failUseNewWtr) ->
			numClientsReportSuccUseNewWtr = 0;	// reset
			do
			:: (dummy2 != numClientsConnected) ->
				CMtoclients[clientsConnected[dummy2]] ! disconn;
				clientsConnected[dummy2] = 0;	// for clarity
				dummy2 = dummy2 + 1;
			:: (dummy2 == numClientsConnected) ->
				dummy2 = 0;
				break;
			od;
			numClientsConnected = 0;	// reset
			WCPstatus = enable;
			status = idle;

		// When CMs status is post-reverting, if all the clients report success for using the old weather, the
		// reverting is completed. The CM will set its own status and the clients status to idle, and re-enable the WCP.
		:: (status == postrev && clientInReqRep.message == succUseOldWtr) ->
			numClientsReportSuccUseOldWtr = numClientsReportSuccUseOldWtr + 1;
			if
			:: (numClientsReportSuccUseOldWtr == numClientsConnected) ->
				status = idle;
				do
				:: (dummy2 != numClientsConnected) ->
					clientsStatus[clientsConnected[dummy2]] = idle;
					dummy2 = dummy2 + 1;
				:: (dummy2 == numClientsConnected) ->
					dummy2 = 0;
					break;
				od;
				WCPstatus = enable;
				numClientsReportSuccUseOldWtr = 0;	// reset
			:: (numClientsReportSuccUseOldWtr != numClientsConnected) ->
				skip;
			fi;

		// Otherwise, if any of the connected clients reports failure for using the old weather, the CM will
		// disconnect all connected clients, re-enable the WCP, and set its own status back to idle.
		:: (status == postrev && clientInReqRep.message == failUseOldWtr) ->
			numClientsReportSuccUseOldWtr = 0;	// reset
			do
			:: (dummy2 != numClientsConnected) ->
				CMtoclients[clientsConnected[dummy2]] ! disconn;
				clientsConnected[dummy2] = 0;	// for clarity
				dummy2 = dummy2 + 1;
			:: (dummy2 == numClientsConnected) ->
				dummy2 = 0;
				break;
			od;
			numClientsConnected = 0;	// reset
			WCPstatus = enable;
			status = idle;
		
		:: else -> skip;
		fi;
	
	:: WCPtoCM ? WCPInMessage ->
		if

		// When the CM is idle and receives update request from the WCP, it will set its own status and all
		// the connected weather-aware clients status to pre-updating, and disable the WCP
		:: (status == idle && WCPInMessage == reqUpdate) ->
			status = preupd;
			do
			:: (dummy != numClientsConnected) ->
				clientsStatus[clientsConnected[dummy]] = preupd;
				dummy = dummy + 1;
			:: (dummy == numClientsConnected) -> 
				dummy = 0;
				break;
			od;
			
			WCPstatus = disable;

		:: else -> skip;
		fi;
	od;
}

proctype WCP() {
	do
	
	// User can manually update new weather information only when the WCP is enabled. By clicking the
	// update button on the WCP, a update message is sent to the CM.
	:: (WCPstatus == enable) ->
		WCPtoCM ! reqUpdate;
	od;
}

init {
	run WCP();
	// clients are put with ids 2,3,4 to match their process ids
	run client(2);
	run client(3);
	run client(4);
	run CM();
}