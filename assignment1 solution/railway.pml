#define noShuttles 3
#define noOrders 2
#define noStations 6
#define max 10
#define trackLength 3
#define minLength 2

#define Reject 0
#define Clockwise 1
#define AntiClockwise -1

#define get_min(x, y) ((x) < (y) -> (x) : (y))
#define get_max(x, y) ((x) > (y) -> (x) : (y))
#define get_abs(x, y) ((x) > (y) -> (x)-(y) : (y)-(x))

bool track_clockwise[noStations];
bool track_anti_clockwise[noStations];

typedef Order {
	int start;
	int end;
	int size;
};

typedef Request {
	int track;
	int direction;
	int shuttle_id;
};


chan order_stack = [max] of {Order};
chan shuttleTOrailway = [noShuttles] of {Request};
chan railwayTOshuttle[noShuttles] = [1] of {bool};
chan shuttleTOmanagement = [noShuttles] of {int, int};
chan managementTOshuttle[noShuttles] = [1] of {Order};


inline get_distance(){
    int distance_a = get_abs(temp_station, recieve_order.start); 
    int distance_b = noStations - get_max(temp_station, recieve_order.start) + get_min(temp_station, recieve_order.start);
    station_distance = get_min(distance_a, distance_b);
}

inline get_direction(){
	if
	:: (current_station + (noStations / 2)) % noStations >= destination -> direction = Clockwise;
	:: else -> direction = AntiClockwise;
	fi
}

inline shuttle_offer(){
    int temp_station;

	if
	:: isMoving -> temp_station = next_station;
	:: else -> temp_station = current_station;
	fi
    
    get_distance();

    if
    :: current_cap + recieve_order.size <= max_cap && station_distance <= minLength -> om_out!charge,id;
    :: else -> om_out!Reject,id;
    fi

    om_in?recieve_order;

    if
    :: recieve_order.size != 0 -> order_queue!recieve_order;
    :: else -> skip;
    fi

}

inline shuttle_process_order(){
	order_queue?current_order;	
	isFree = false;
	destination = current_order.start;
	printf("[Shuttle %d] Starting new order from station %d to station %d\n", id, current_order.start, current_order.end);
	get_direction();
}


inline shuttle_move(){

	if
	:: current_station == destination && destination == current_order.end && !isMoving -> 
		current_cap = current_cap - current_order.size;
		isFree = true;
		isMoving = false;
		printf("[Shuttle %d] Unloading %d passengers at station %d \n", id, current_order.size, current_order.end);
		goto L2;
	:: current_station == destination  && destination == current_order.start && !isMoving ->
		destination = current_order.end;
		get_direction();
		current_cap = current_cap + current_order.size;
		isFree = false;
		isMoving = false;
		track_distance = trackLength;
		printf("[Shuttle %d] Loading %d passengers from station %d \n", id, current_order.size, current_order.start);
		goto L1;
	:: else -> goto L1;
    fi

L1:	if
	:: !isMoving -> 
		if
		:: direction == Clockwise -> next_station = (current_station + 1) % noStations;
		:: direction == AntiClockwise -> next_station =  (current_station - 1 + noStations) % noStations;
		fi

		track_req.direction = direction;
		if
		:: current_station == noStations - 1 -> track_req.track = current_station;
		:: else -> track_req.track = get_min(current_station, next_station);
		fi
				
		bool got_track;

		do
		:: rm_out!track_req; 
			rm_in?got_track;
			if
			:: got_track -> track_distance = trackLength; isMoving = true; break;
			:: else -> skip;
			fi
		od

	:: isMoving && track_distance > 0 -> 
			track_distance = track_distance - 1;
			printf("[Shuttle %d] Moving from station %d to station %d\n", id, current_station, next_station);
	:: isMoving && track_distance == 0 -> 
			current_station = next_station; 			
			if
			:: direction == Clockwise -> track_clockwise[track_req.track] = false; 
			:: direction == AntiClockwise -> track_anti_clockwise[track_req.track] = false; 
			fi
			isMoving = false;

L2:	fi

}

proctype Shuttle(int max_cap; int charge; int init_pos; int id; chan om_out; chan om_in; chan rm_out; chan rm_in) {
	chan order_queue = [max] of {Order};
	Order current_order;
	Order recieve_order;
	Request track_req;
	bool isMoving = false;
	bool isFree = true;
	int current_cap;
	int current_station = init_pos;
	int next_station;
	int destination;
	int track_distance;
	int direction;
	int station_distance;

	track_req.shuttle_id = id;

L0:	do
    ::  om_in?recieve_order -> shuttle_offer();
    ::  isMoving || !isFree -> shuttle_move();
    ::  isFree && nempty(order_queue) -> shuttle_process_order();       
    od;
}


proctype RailwayNetwork() {
	Request req;
	int shuttle_id;
	do
	::  nempty(shuttleTOrailway) ->
			shuttleTOrailway?req;
			if
			:: req.direction == Clockwise ->
				if
				:: atomic{ !track_clockwise[req.track] -> track_clockwise[req.track] = true; railwayTOshuttle[req.shuttle_id]!true;}
				:: else -> railwayTOshuttle[shuttle_id]!false;
				fi
			:: req.direction == AntiClockwise ->
				if
				:: atomic{ !track_anti_clockwise[req.track] -> track_anti_clockwise[req.track] = true; railwayTOshuttle[req.shuttle_id]!true;}
				:: else -> railwayTOshuttle[shuttle_id]!false;
				fi
			fi
	od
}

proctype ManagementSystem() {
	int i;
	Order current;
	Order reject;
	int min_charge = 100;
	int offer_id;
	int shuttle_id;
	int shuttle_charge;
	do
	:: nempty(order_stack) -> 
			printf("[Management System]: Broadcasting New Order\n");
			order_stack?current;
			for (i:0 .. noShuttles-1){
				managementTOshuttle[i]!current;
			}
			i = 0;
			printf("[Management System]: Waiting for replies\n");
			for (i:0 .. noShuttles-1){
				shuttleTOmanagement?shuttle_charge,shuttle_id;
				if
				:: shuttle_charge < min_charge -> min_charge = shuttle_charge; offer_id = shuttle_id;
				:: else -> skip;
				fi
			}
			i = 0;
			printf("[Management System]: New Order assigned to Shuttle %d\n", offer_id);
			for (i:0 .. noShuttles-1){				
				if
				:: i == offer_id -> managementTOshuttle[i]!current;
				:: else -> managementTOshuttle[i]!reject;
				fi
			}

	od

}

proctype OrderGenerator(){
	Order first; first.start = 1; first.end = 3; first.size = 4;
    Order second; second.start = 2; second.end = 3; second.size = 1;
    order_stack!first;
    order_stack!second;
}

init{
	atomic{
		run Shuttle(5, 2, 1, 0, shuttleTOmanagement, managementTOshuttle[0], shuttleTOrailway, railwayTOshuttle[0]); 
		run Shuttle(8, 4, 1, 1, shuttleTOmanagement, managementTOshuttle[1], shuttleTOrailway, railwayTOshuttle[1]); 
		run Shuttle(10, 3, 2, 2, shuttleTOmanagement, managementTOshuttle[2], shuttleTOrailway, railwayTOshuttle[2]);
		run OrderGenerator();
		run RailwayNetwork();
		run ManagementSystem();
	}
}