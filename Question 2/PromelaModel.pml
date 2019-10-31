#define NUM_STATIONS	6
#define ARRAY_SIZE		3
#define NUM_SHUTTLES	3

typedef orderType {
	int start;
	int end;
	int load;
	bool orderOrAssign;	// 0 for order, 1 for assign
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

// keeps track of where each shuttle is -> if shuttle with id 1 is at station3, shuttlePos[1] will be (3,3)
// if shuttle with id 1 is on track going from station1 to station2, shuttlePos[1] will be (1,2); 0th cell in array won't be used
track shuttlePos[NUM_SHUTTLES+1];

// keeps track of each track's availability -> 1st and 2nd cells of array are tracks 6->1 and 2->1, 3rd and 4th cells are tracks 1->2 and 3->2 etc...
// 0th cell in array won't be used
bool trackAvail[(NUM_STATIONS*2) + 1];

chan managementToShuttles[NUM_SHUTTLES] = [ARRAY_SIZE] of {orderType};
chan shuttlesToManagement = [ARRAY_SIZE] of {shuttleReply};

proctype shuttle(int shuttleId; int capacity; int startStation; int charge) {
	orderType order;
	orderType ordersAssigned[ARRAY_SIZE];	// list of all orders shuttle has accepted and needs to execute but hasn't loaded yet
	orderType ordersBeingExecuted[ARRAY_SIZE];	// list of all orders shuttle is currently executing (transporting)
	int numOrdersAssigned = 0;
	int numOrdersBeingExecuted = 0;
	int currLoad = 0;
	int dummy;
	int dummy2;
	int nextDest1;
	int nextDest2;
	int difference1;
	int difference2;

	shuttlePos[shuttleId].origin = startStation;
	shuttlePos[shuttleId].dest = startStation;

	shuttleReply reply;
	reply.shuttleId = shuttleId;
	reply.payment = charge;

	do
	
	// When an order is received,
	:: managementToShuttles[shuttleId] ? order ->
		if 

		// a shuttle should make an offer only if (a) current loaded size plus the order size does not exceed
		// the capacity, and (b) the start destination of the order is within two stations away from its current position
		// (if it is on a track, its current position is its arriving station). Otherwise the shuttle should refuse to make an offer.
		:: (order.orderOrAssign == 0) ->
			if 
			:: (order.load + currLoad <= capacity) ->
				int difference = shuttlePos[shuttleId].dest - order.start;
				if
				:: (difference <= 2 && difference >= -2) ->
					reply.offerOrRefuse = 1;
				:: (difference > 2 || difference < -2) ->
					if
					:: (difference < 0 && (difference + NUM_STATIONS <= 2)) ->
						reply.offerOrRefuse = 1;
					:: (difference > 0 && (difference - NUM_STATIONS >= -2)) ->
						reply.offerOrRefuse = 1;
					:: else ->
						reply.offerOrRefuse = 0;
					fi;
				fi;				
			:: (order.load + currLoad > capacity) ->
				reply.offerOrRefuse = 0;
			fi;
			
			shuttlesToManagement ! reply;
		:: (order.orderOrAssign == 1) ->
			ordersAssigned[numOrdersAssigned].start = order.start;
			ordersAssigned[numOrdersAssigned].end = order.end;
			ordersAssigned[numOrdersAssigned].load = order.load;
			ordersAssigned[numOrdersAssigned].orderOrAssign = order.orderOrAssign;
			numOrdersAssigned = numOrdersAssigned + 1;
		fi;
	
	// Shuttle traveling on a track can neither change direction nor choose another destination.
	:: (shuttlePos[shuttleId].origin != shuttlePos[shuttleId].dest) ->

		// make track it was previously travelling on now available again
		if
		:: (shuttlePos[shuttleId].origin < shuttlePos[shuttleId].dest && shuttlePos[shuttleId].dest != NUM_STATIONS) ->
			trackAvail[(shuttlePos[shuttleId].dest * 2) - 1] = 1;

		:: (shuttlePos[shuttleId].origin < shuttlePos[shuttleId].dest && shuttlePos[shuttleId].dest == NUM_STATIONS) ->
			if 
			:: (shuttlePos[shuttleId].origin == 1) ->
				trackAvail[(shuttlePos[shuttleId].dest * 2)] = 1;
			:: (shuttlePos[shuttleId].origin != 1) ->
				trackAvail[(shuttlePos[shuttleId].dest * 2) - 1] = 1;
			fi;

		:: (shuttlePos[shuttleId].origin > shuttlePos[shuttleId].dest && shuttlePos[shuttleId].dest != 1) ->
			trackAvail[(shuttlePos[shuttleId].dest * 2)] = 1;

		:: (shuttlePos[shuttleId].origin > shuttlePos[shuttleId].dest && shuttlePos[shuttleId].dest == 1) ->
			if
			:: (shuttlePos[shuttleId].origin == NUM_STATIONS) ->
				trackAvail[(shuttlePos[shuttleId].dest * 2) - 1] = 1;
			:: (shuttlePos[shuttleId].origin != NUM_STATIONS) ->
				trackAvail[(shuttlePos[shuttleId].dest * 2)] = 1;
			fi;
		fi;

		shuttlePos[shuttleId].origin = shuttlePos[shuttleId].dest; 
			
	// Shuttle at station (not on track)
	:: (shuttlePos[shuttleId].origin == shuttlePos[shuttleId].dest) ->
		if

		// 1. NO ORDERS BEING EXECUTED, NO ORDERS ASSIGNED
		:: (numOrdersBeingExecuted == 0 && numOrdersAssigned == 0) ->
			skip;

		// 2. MOVE TO STATION TO LOAD ORDER (IF I AM NOT EXECUTING ANY ORDER BUT HAVE ORDERS ASSIGNED)
		:: (numOrdersBeingExecuted == 0 && numOrdersAssigned != 0 && shuttlePos[shuttleId].dest != ordersAssigned[0].start) ->

			// 2.1 find the next station to go to that would make the journey to the loading station the shortest
			nextDest1 = shuttlePos[shuttleId].dest + 1;
			if
			:: (nextDest1 > NUM_STATIONS) ->
				nextDest1 = 1;
			:: else -> skip;
			fi;
			nextDest2 = shuttlePos[shuttleId].dest - 1;
			if
			:: (nextDest2 == 0) ->
				nextDest2 = NUM_STATIONS;
			:: else -> skip;
			fi;

			difference1 = nextDest1 - ordersAssigned[0].start;
			if
			:: (-difference1 < (-NUM_STATIONS/2)) ->
				difference1 = difference1 + NUM_STATIONS;
			:: (difference1 > (NUM_STATIONS/2)) ->
				difference1 = difference1 - NUM_STATIONS;
			:: else -> skip;
			fi;
			if
			:: (difference1 < 0) ->
				difference1 = 0 - difference1;
			:: else -> skip;
			fi;

			difference2 = nextDest2 - ordersAssigned[0].start;
			if
			:: (-difference2 < (-NUM_STATIONS/2)) ->
				difference2 = difference2 + NUM_STATIONS;
			:: (difference2 > (NUM_STATIONS/2)) ->
				difference2 = difference2 + NUM_STATIONS;
			:: else -> skip;
			fi;
			if
			:: (difference2 < 0) ->
				difference2 = 0 - difference2;
			:: else -> skip;
			fi;

			// 2.2 go onto the track that leads to the station that would make the journey to the loading station shortest 
			// IF the track is available
			if
			:: (difference1 <= difference2) ->
				if
				:: (shuttlePos[shuttleId].origin < nextDest1 && nextDest1 != NUM_STATIONS && trackAvail[(nextDest1 * 2) - 1] == 1) ->
					trackAvail[(nextDest1 * 2) - 1] = 0;
					shuttlePos[shuttleId].dest = nextDest1;
				
				:: (shuttlePos[shuttleId].origin < nextDest1 && nextDest1 == NUM_STATIONS) ->
					if 
					:: (shuttlePos[shuttleId].origin == 1 && trackAvail[(nextDest1 * 2)] == 1) ->
						trackAvail[(nextDest1 * 2)] = 0;
						shuttlePos[shuttleId].dest = nextDest1;
					:: (shuttlePos[shuttleId].origin != 1 && trackAvail[(nextDest1 * 2) - 1] == 1) ->
						trackAvail[(nextDest1 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest1;
					:: else -> skip;
					fi;
				
				:: (shuttlePos[shuttleId].origin > nextDest1 && nextDest1 != 1 && trackAvail[(nextDest1 * 2)] == 1) ->
					trackAvail[(nextDest1 * 2)] = 0;
					shuttlePos[shuttleId].dest = nextDest1;
				
				:: (shuttlePos[shuttleId].origin > nextDest1 && nextDest1 == 1) ->
					if
					:: (shuttlePos[shuttleId].origin == NUM_STATIONS && trackAvail[(nextDest1 * 2) - 1] == 1) ->
						trackAvail[(nextDest1 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest1;

					:: (shuttlePos[shuttleId].origin != NUM_STATIONS && trackAvail[(nextDest1 * 2)] == 1) ->
						trackAvail[(nextDest1 * 2)] = 1;
						shuttlePos[shuttleId].dest = nextDest1;
						
					:: else -> skip;
					fi;
				
				:: else -> skip;
				fi;
				
			:: (difference1 > difference2) ->
				if
				:: (shuttlePos[shuttleId].origin < nextDest2 && nextDest2 != NUM_STATIONS && trackAvail[(nextDest2 * 2) - 1] == 1) ->
					trackAvail[(nextDest2 * 2) - 1] = 0;
					shuttlePos[shuttleId].dest = nextDest2;
				
				:: (shuttlePos[shuttleId].origin < nextDest2 && nextDest2 == NUM_STATIONS) ->
					if 
					:: (shuttlePos[shuttleId].origin == 1 && trackAvail[(nextDest2 * 2)] == 1) ->
						trackAvail[(nextDest2 * 2)] = 0;
						shuttlePos[shuttleId].dest = nextDest2;
					:: (shuttlePos[shuttleId].origin != 1 && trackAvail[(nextDest2 * 2) - 1] == 1) ->
						trackAvail[(nextDest2 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest2;
					:: else -> skip;
					fi;
				
				:: (shuttlePos[shuttleId].origin > nextDest2 && nextDest2 != 1 && trackAvail[(nextDest2 * 2)] == 1) ->
					trackAvail[(nextDest2 * 2)] = 0;
					shuttlePos[shuttleId].dest = nextDest2;
				
				:: (shuttlePos[shuttleId].origin > nextDest2 && nextDest2 == 1) ->
					if
					:: (shuttlePos[shuttleId].origin == NUM_STATIONS && trackAvail[(nextDest2 * 2) - 1] == 1) ->
						trackAvail[(nextDest2 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest2;

					:: (shuttlePos[shuttleId].origin != NUM_STATIONS && trackAvail[(nextDest2 * 2)] == 1) ->
						trackAvail[(nextDest2 * 2)] = 1;
						shuttlePos[shuttleId].dest = nextDest2;
						
					:: else -> skip;
					fi;
				
				:: else -> skip;
				fi;
			fi;
			
		// 3. LOAD ORDER (IF I AM NOT EXECUTING ANY ORDER BUT HAVE ORDERS ASSIGNED)
		:: (numOrdersBeingExecuted == 0 && numOrdersAssigned != 0 && shuttlePos[shuttleId].dest == ordersAssigned[0].start && ordersAssigned[0].load + currLoad <= capacity) ->			
			
			ordersBeingExecuted[numOrdersBeingExecuted].start = ordersAssigned[0].start;
			ordersBeingExecuted[numOrdersBeingExecuted].end = ordersAssigned[0].end;
			ordersBeingExecuted[numOrdersBeingExecuted].load = ordersAssigned[0].load;
			ordersBeingExecuted[numOrdersBeingExecuted].orderOrAssign = ordersAssigned[0].orderOrAssign;
			currLoad = currLoad + ordersBeingExecuted[0].load;

			numOrdersBeingExecuted = numOrdersBeingExecuted + 1;
			numOrdersAssigned = numOrdersAssigned - 1;

			dummy = numOrdersAssigned;
			dummy2 = 0;

			// 3.1 move all ordersAssigned one element forward to cover up the 1st order (that has been loaded and moved from ordersAssigned to ordersBeingExecuted)
			do
			:: (dummy != 0) ->
				ordersAssigned[dummy2].start = ordersAssigned[dummy2 + 1].start;
				ordersAssigned[dummy2].end = ordersAssigned[dummy2 + 1].end;
				ordersAssigned[dummy2].load = ordersAssigned[dummy2 + 1].load;
				ordersAssigned[dummy2].orderOrAssign = ordersAssigned[dummy2 + 1].orderOrAssign;
				dummy2 = dummy2 + 1;
				dummy = dummy - 1;
			
			:: (dummy == 0) ->
				ordersAssigned[numOrdersAssigned].start = 0;
				ordersAssigned[numOrdersAssigned].end = 0;
				ordersAssigned[numOrdersAssigned].load = 0;
				ordersAssigned[numOrdersAssigned].orderOrAssign = 0;
				break;
			od;

		// 4. MOVE TO STATION TO UNLOAD ORDER (IF I AM EXECUTING AN ORDER)
		:: (numOrdersBeingExecuted != 0 && shuttlePos[shuttleId].dest != ordersBeingExecuted[0].end) ->
			
			// 4.1 find the next station to go to that would make the journey to the unloading station the shortest
			nextDest1 = shuttlePos[shuttleId].dest + 1;
			if
			:: (nextDest1 > NUM_STATIONS) ->
				nextDest1 = 1;
			:: else -> skip;
			fi;
			nextDest2 = shuttlePos[shuttleId].dest - 1;
			if
			:: (nextDest2 == 0) ->
				nextDest2 = NUM_STATIONS;
			:: else -> skip;
			fi;

			difference1 = nextDest1 - ordersBeingExecuted[0].end;
			if
			:: (-difference1 < (-NUM_STATIONS/2)) ->
				difference1 = difference1 + NUM_STATIONS;
			:: (difference1 > (NUM_STATIONS/2)) ->
				difference1 = difference1 - NUM_STATIONS;
			:: else -> skip;
			fi;
			if
			:: (difference1 < 0) ->
				difference1 = 0 - difference1;
			:: else -> skip;
			fi;

			difference2 = nextDest2 - ordersBeingExecuted[0].end;
			if
			:: (-difference2 < (-NUM_STATIONS/2)) ->
				difference2 = difference2 + NUM_STATIONS;
			:: (difference2 > (NUM_STATIONS/2)) ->
				difference2 = difference2 + NUM_STATIONS;
			:: else -> skip;
			fi;
			if
			:: (difference2 < 0) ->
				difference2 = 0 - difference2;
			:: else -> skip;
			fi;

			// 4.2 go onto the track that leads to the station that would make the journey to the unloading station shortest 
			// IF the track is available
			if
			:: (difference1 <= difference2) ->
				if
				:: (shuttlePos[shuttleId].origin < nextDest1 && nextDest1 != NUM_STATIONS && trackAvail[(nextDest1 * 2) - 1] == 1) ->
					trackAvail[(nextDest1 * 2) - 1] = 0;
					shuttlePos[shuttleId].dest = nextDest1;
				
				:: (shuttlePos[shuttleId].origin < nextDest1 && nextDest1 == NUM_STATIONS) ->
					if 
					:: (shuttlePos[shuttleId].origin == 1 && trackAvail[(nextDest1 * 2)] == 1) ->
						trackAvail[(nextDest1 * 2)] = 0;
						shuttlePos[shuttleId].dest = nextDest1;
					:: (shuttlePos[shuttleId].origin != 1 && trackAvail[(nextDest1 * 2) - 1] == 1) ->
						trackAvail[(nextDest1 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest1;
					:: else -> skip;
					fi;
				
				:: (shuttlePos[shuttleId].origin > nextDest1 && nextDest1 != 1 && trackAvail[(nextDest1 * 2)] == 1) ->
					trackAvail[(nextDest1 * 2)] = 0;
					shuttlePos[shuttleId].dest = nextDest1;
				
				:: (shuttlePos[shuttleId].origin > nextDest1 && nextDest1 == 1) ->
					if
					:: (shuttlePos[shuttleId].origin == NUM_STATIONS && trackAvail[(nextDest1 * 2) - 1] == 1) ->
						trackAvail[(nextDest1 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest1;

					:: (shuttlePos[shuttleId].origin != NUM_STATIONS && trackAvail[(nextDest1 * 2)] == 1) ->
						trackAvail[(nextDest1 * 2)] = 1;
						shuttlePos[shuttleId].dest = nextDest1;
						
					:: else -> skip;
					fi;
				
				:: else -> skip;
				fi;
				
			:: (difference1 > difference2) ->
				if
				:: (shuttlePos[shuttleId].origin < nextDest2 && nextDest2 != NUM_STATIONS && trackAvail[(nextDest2 * 2) - 1] == 1) ->
					trackAvail[(nextDest2 * 2) - 1] = 0;
					shuttlePos[shuttleId].dest = nextDest2;
				
				:: (shuttlePos[shuttleId].origin < nextDest2 && nextDest2 == NUM_STATIONS) ->
					if 
					:: (shuttlePos[shuttleId].origin == 1 && trackAvail[(nextDest2 * 2)] == 1) ->
						trackAvail[(nextDest2 * 2)] = 0;
						shuttlePos[shuttleId].dest = nextDest2;
					:: (shuttlePos[shuttleId].origin != 1 && trackAvail[(nextDest2 * 2) - 1] == 1) ->
						trackAvail[(nextDest2 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest2;
					:: else -> skip;
					fi;
				
				:: (shuttlePos[shuttleId].origin > nextDest2 && nextDest2 != 1 && trackAvail[(nextDest2 * 2)] == 1) ->
					trackAvail[(nextDest2 * 2)] = 0;
					shuttlePos[shuttleId].dest = nextDest2;
				
				:: (shuttlePos[shuttleId].origin > nextDest2 && nextDest2 == 1) ->
					if
					:: (shuttlePos[shuttleId].origin == NUM_STATIONS && trackAvail[(nextDest2 * 2) - 1] == 1) ->
						trackAvail[(nextDest2 * 2) - 1] = 0;
						shuttlePos[shuttleId].dest = nextDest2;

					:: (shuttlePos[shuttleId].origin != NUM_STATIONS && trackAvail[(nextDest2 * 2)] == 1) ->
						trackAvail[(nextDest2 * 2)] = 1;
						shuttlePos[shuttleId].dest = nextDest2;
						
					:: else -> skip;
					fi;
				
				:: else -> skip;
				fi;
			fi;
		
		// 5. UNLOAD ORDER (IF I AM EXECUTING AN ORDER) 
		:: (numOrdersBeingExecuted != 0 && shuttlePos[shuttleId].dest == ordersBeingExecuted[0].end) ->
			numOrdersBeingExecuted = numOrdersBeingExecuted - 1;
			currLoad = currLoad - ordersBeingExecuted[0].load;

			dummy = numOrdersBeingExecuted;
			dummy2 = 0;

			// 5.1 move all ordersBeingExecuted one element forward to cover up the 1st order (that has been unloaded and should be removed from ordersBeingExecuted)
			do
			:: (dummy != 0) ->
				ordersBeingExecuted[dummy2].start = ordersBeingExecuted[dummy2 + 1].start;
				ordersBeingExecuted[dummy2].end = ordersBeingExecuted[dummy2 + 1].end;
				ordersBeingExecuted[dummy2].load = ordersBeingExecuted[dummy2 + 1].load;
				ordersBeingExecuted[dummy2].orderOrAssign = ordersBeingExecuted[dummy2 + 1].orderOrAssign;
				dummy2 = dummy2 + 1;
				dummy = dummy - 1;
			
			:: (dummy == 0) ->
				ordersBeingExecuted[numOrdersBeingExecuted].start = 0;
				ordersBeingExecuted[numOrdersBeingExecuted].end = 0;
				ordersBeingExecuted[numOrdersBeingExecuted].load = 0;
				ordersBeingExecuted[numOrdersBeingExecuted].orderOrAssign = 0;
				break;
			od;
		fi;
	od;
}

proctype management() {
	orderType orders[ARRAY_SIZE];
	orderType order;
	int lowestOfferReceived = -1;
	int shuttleToOffer = 0;
	int numShuttlesReplied = 0;
	int numShuttlesSent = 0;
	shuttleReply reply;
	int dummy = 0;
	int NUM_ORDERS = 2;

	orders[0].start = 1;
	orders[0].end = 3;
	orders[0].load = 4;
	orders[0].orderOrAssign = 0;
	orders[1].start = 2;
	orders[1].end = 3;
	orders[1].load = 1;
	orders[1].orderOrAssign = 0;

	// initialise trackAvail array
	do
	:: (dummy != (NUM_STATIONS*2)+1) ->
		trackAvail[dummy] = 1;
		dummy = dummy + 1;
	:: (dummy == (NUM_STATIONS*2)+1) ->
		dummy = 0;
		break;
	od;

	do
	:: (dummy == NUM_ORDERS) ->
		break;
	:: (dummy != NUM_ORDERS) ->
		order.start = orders[dummy].start;
		order.end = orders[dummy].end;
		order.load = orders[dummy].load;
		order.orderOrAssign = orders[dummy].orderOrAssign;
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
		:: shuttlesToManagement ? reply ->
			numShuttlesReplied = numShuttlesReplied + 1;
			if 
			:: (reply.offerOrRefuse == 0) -> skip;
			:: (reply.offerOrRefuse == 1 && lowestOfferReceived == -1) ->
				lowestOfferReceived = reply.payment;
				shuttleToOffer = reply.shuttleId;
			:: (reply.offerOrRefuse == 1 && lowestOfferReceived != -1 && reply.payment >= lowestOfferReceived) -> skip;
			:: (reply.offerOrRefuse == 1 && lowestOfferReceived != -1 && reply.payment < lowestOfferReceived) ->
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
			order.orderOrAssign = 1;
			managementToShuttles[shuttleToOffer] ! order;
			lowestOfferReceived = -1;
		fi;
	od;
}

init {
	run management();
	run shuttle(0, 5, 1, 2);
	run shuttle(1, 8, 1, 4);
	run shuttle(2, 10, 2, 3);
}