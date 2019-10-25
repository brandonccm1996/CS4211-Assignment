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

typedef track {
	int origin;
	int dest;
}

// keeps track of where each shuttle is. if shuttle with id 1 is at station3, shuttlePos[1] will be (3,3)
// if shuttle with id 1 is on track going from station1 to station2, shuttlePos[1] will be (1,2)
track shuttlePos[NUM_SHUTTLES+1];

chan managementToShuttles[NUM_SHUTTLES] = [ARRAY_SIZE] of {orderType};
chan shuttlesToManagement = [ARRAY_SIZE] of {shuttleReply};

proctype shuttle(int shuttleId; int capacity; int startStation; int charge) {
	orderType order;
	orderType shuttleOrders[ARRAY_SIZE];	// list of all orders shuttle is carrying
	int numOrdersCarrying = 0;
	int currLoad = 0;

	shuttlePos[shuttleId].origin = startStation;
	shuttlePos[shuttleId].dest = startStation;

	shuttleReply reply;
	reply.shuttleId = shuttleId;
	reply.payment = charge;

	// When an order is received, a shuttle should make an offer only if (a) current loaded size plus the order size does not exceed
	// the capacity, and (b) the start destination of the order is within two stations away from its current position
	// (if it is on a track, its current position is its arriving station). Otherwise the shuttle should refuse to make an offer.
	do
	:: managementToShuttles[shuttleId] ? order ->
		if 
		:: (order.offerOrAssign == 0) ->
			if 
			:: (order.load + currLoad <= capacity) ->
				int difference = shuttlePos[shuttleId].end - order.start;
				if
				:: (difference < 2 && difference > -2) ->
					reply.offerOrRefuse = 1;
					shuttlesToManagement[shuttleId] ! reply;
				:: (difference > 2 || difference < -2) ->
					reply.offerOrRefuse = 0;
					shuttlesToManagement[shuttleId] ! reply;
				fi;
			:: (order.load + currLoad > capacity) ->
				reply.offerOrRefuse = 0;
				shuttlesToManagement[shuttleId] ! reply;
			fi;
		:: (order.offerOrAssign == 1) ->
			currLoad = currLoad + order.load;
			shuttleOrders[numOrdersCarrying] = order;
			numOrdersCarrying = numOrdersCarrying + 1;
		fi;
	
	:: if 
		:: (shuttlePos[shuttleId].origin != shuttlePos[shuttleId].dest) ->
			shuttlePos[shuttleId].origin = shuttlePos[shuttleId].dest;
		
		:: (shuttlePos[shuttleId].origin == shuttlePos[shuttleId.dest]) ->
	od;

}

proctype management() {
	orderType orders[ARRAY_SIZE];
	orderType order;
	orderType assignmt;
	int lowestOfferReceived = -1;
	int shuttleToOffer = 0;
	int numShuttlesReplied = 0;
	int numShuttlesSent = 0;
	shuttleReply reply;
	int dummy = 0;

	order[0].start = 1;
	order[0].end = 3;
	order[0].load = 4;
	order[0].offerOrAssign = 0;
	order[1].start = 2;
	order[1].end = 3;
	order[1].load = 1;
	order[1].offerOrAssign = 0;

	do
	:: order = orders[dummy];
		dummy = dummy + 1;

		// Orders are made known to all shuttles by the management system.
		do
		:: managementToShuttles[numShuttlesSent] ! order ->
			numShuttlesSent = numShuttlesSent + 1;
			if 
			:: (numShuttlesSent == NUM_SHUTTLES) ->
				numShuttlesSent = 0;
				break;
			:: (numShuttlesSent != NUM_SHUTTLES) ->
				skip;
			fi;
		od;

		// After all shuttles are informed of the new order, each shuttle must reply with either an offer or refuse message.
		// The shuttle having made the lowest offer will receive the assignment. In the event of two equal offers, the assignment will
		// go to the shuttle that first made the offer.
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
			managementToShuttles[shuttleToOffer] ! assignmt;
		fi;
	od;
}

init {
	run management();
	run shuttle(1, 5, 1, 2);
	run shuttle(2, 8, 1, 4);
	run shuttle(3, 10, 2, 3);
}