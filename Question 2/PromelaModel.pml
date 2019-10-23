#define NUM_STATIONS	6
#define ARRAY_SIZE		10
#define NUM_SHUTTLES	3

typedef orderType {
	int start;
	int end;
	int load;
	bool offerOrAssign;	// 0 for offer, 1 for assign
}

typedef shuttleReply {
	int shuttleId;
	bool offerOrRefuse;	// 0 for refuse, 1 for offer
	int payment;
}

// int stations[NUM_STATIONS];
bool tracks[NUM_STATIONS];	// indicates whether track is occupied
chan managementToShuttles = [ARRAY_SIZE] of {orderType};
chan shuttlesToManagement[NUM_SHUTTLES] = [ARRAY_SIZE] of {shuttleReply};

proctype shuttle(int shuttleId; int capacity; int startStation; int charge) {
	orderType order;
	orderType orders[ARRAY_SIZE];	// list of all orders shuttle is carrying
	int currLoad = 0;
	int currStation = startStation;

	do
	:: managementToShuttles ? order ->
		if 
		:: (order.load + currLoad <= capacity) -> skip;

		fi;
	od;

}

proctype management() {
	orderType order;
	orderType assignmt;
	int lowestOfferReceived = -1;
	int shuttleToOffer = 0;
	int numShuttlesReplied = 0;
	shuttleReply reply;

	do
	:: managementToShuttles ! order ->
		do
		:: shuttlesToManagement[numShuttlesReplied] ? reply ->
			numShuttlesReplied = numShuttlesReplied + 1;
			if 
			:: (reply.offerOrRefuse == 0) -> skip;
			:: (reply.offerOrRefuse != 0 && reply.payment <= lowestOfferReceived) -> skip;
			:: (reply.offerOrRefuse != 0 && reply.payment > lowestOfferReceived) ->
				lowestOfferReceived = reply.payment;
				shuttleToOffer = reply.shuttleId;
			fi;
			
			if 
			:: (numShuttlesReplied == NUM_SHUTTLES) ->
				numShuttlesReplied = 0;
				break;
			:: (numShuttlesReplied != NUM_SHUTTLES) -> skip;
			fi;
		od;

		if 
		:: (lowestOfferReceived == -1) -> skip;	// all shuttles refused
		:: (lowestOfferReceived != -1) ->
			assignmt.start = order.start;
			assignmt.end = order.end;
			assignmt.load = order.load;
			assignmt.offerOrAssign = 1;
			managementToShuttles ! assignmt;
		fi;
	od;
}