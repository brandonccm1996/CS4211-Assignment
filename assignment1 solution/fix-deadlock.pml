#define noClients 3

mtype = {success, fail, update};
mtype = {get_new_weather, use_new_weather, use_old_weather};
mtype = {establish, refuse, disconnect};
mtype = {initializing, pre_initialization, post_initialization, idle, pre_updating, updating, post_reverting, post_updating};

bit allowedManualUpdate = 1;
bit connected[noClients];
mtype status[noClients+2];

chan cmTOcp = [0] of { mtype };
chan cpTOcm = [0] of { mtype };
chan cmTOclient[noClients] = [1] of { mtype };
chan clientTOcm[noClients] = [1] of { mtype };

active [noClients] proctype client(){
    mtype response;
    mtype request;

 L1:do
	:: !connected[_pid] -> 
		clientTOcm[_pid]!establish;
		cmTOclient[_pid]?response;
		if
		:: (response == refuse) -> goto L1;
		:: (response == get_new_weather) ->
			do
			::	clientTOcm[_pid]!fail;						     	
			   	goto L1;
			::	clientTOcm[_pid]!success;
			   	cmTOclient[_pid]?use_new_weather;
				do
				::	clientTOcm[_pid]!fail; 		
					goto L1;
				::	clientTOcm[_pid]!success;
					goto L1;	
				od
			od
		fi

L2: :: connected[_pid] -> 
		cmTOclient[_pid]?request;
		if
		:: request == disconnect -> 
		   connected[_pid] = 0;
		   goto L1;
		:: else -> skip;
		fi
		do
		::	clientTOcm[_pid]!fail;
			goto L2;
		::	clientTOcm[_pid]!success;										  			    
			goto L2;							  									  	
		od
	od

}


inline establish_connection(){
	atomic{
		status[_pid] = pre_initialization;
		status[client_id] = pre_initialization;
		connected[client_id] = 1;
		allowedManualUpdate = 0;
	} 
	goto L1;
}


active proctype communicationManager(){
    mtype response;
    bit allSuccess;
    int i;
    int client_id;
    bit atleastOneConnection = 0;
    status[_pid] = idle;
  

  L1:do
	:: (status[_pid] == idle) -> 
		do
		::	cpTOcm?update -> 
				atomic{
					allowedManualUpdate = 0;
					status[_pid] = pre_updating;
				}
				
				for (i : 0 .. noClients - 1) {
					if
					:: (connected[i] == 1) -> 
						status[i] = pre_updating; 
					:: else -> skip;
					fi
				}
				
				goto L1;

		::	clientTOcm[0]?establish -> 
				client_id = 0;
				establish_connection();

		::	clientTOcm[1]?establish -> 
				client_id = 1;	
				establish_connection();
				

		::	clientTOcm[2]?establish -> 
				client_id = 2;	
				establish_connection();

		od		   


	::	(status[_pid] == pre_initialization) ->
			cmTOclient[client_id]!get_new_weather;
			atomic{
				status[_pid] = initializing;
				status[client_id] = initializing;												
			}

	:: (status[_pid] == initializing) ->
			clientTOcm[client_id]?response;
			if
			:: (response == success) -> 
				cmTOclient[client_id]!use_new_weather;
				atomic{
					status[_pid] = post_initialization;
					status[client_id] = post_initialization;	
				}
			:: (response == fail) -> 
				atomic {					
					cmTOclient[client_id]!disconnect;													       								
					status[_pid] = idle;
				}
			fi

	:: (status[_pid] == post_initialization) ->  
			clientTOcm[client_id]?response;
			if
			:: (response == success) -> 
				atomic {
					status[_pid] = idle;
					status[client_id] = idle;
					atleastOneConnection = 1;
					allowedManualUpdate = 1;
				}

			:: (response == fail) -> 
				atomic {
					status[_pid] = idle;					
					cmTOclient[client_id]!disconnect;	
					allowedManualUpdate = 1;
				}
			fi

    :: (status[_pid] == pre_updating) ->   
            if
    		:: (atleastOneConnection == 1) -> status[_pid] = updating;
    		:: else -> allowedManualUpdate = 1;
					   status[_pid] = idle;
					   goto L1;
    		fi
			for (i : 0 .. noClients - 1) {
				if
				:: (connected[i] == 1) -> 
					cmTOclient[i]!get_new_weather;
					status[i] = updating;
				:: else -> skip;
				fi
			}	

	:: (status[_pid] == updating) -> 	
			allSuccess = 1;				    				
			for (i : 0 .. noClients - 1) {	
				if
				:: (connected[i] == 1) -> clientTOcm[i]?response;
					if												
					:: (response == fail) -> allSuccess = 0;
					:: else -> skip;																	
					fi
				:: else -> skip;
				fi				    						
			}

			if
			:: (allSuccess == 1) ->		
				status[_pid] = post_updating;
				for (i : 0 .. noClients - 1) {
					if
					:: (connected[i] == 1) -> 
						cmTOclient[i]!use_new_weather;
						status[i] = post_updating;
					:: else -> skip;
					fi
				}
																		
			:: (allSuccess == 0) ->	
				status[_pid] = post_reverting;
				for (i : 0 .. noClients - 1) {
					if
					:: (connected[i] == 1) -> 
						cmTOclient[i]!use_old_weather;
						status[i] = post_reverting;
					:: else -> skip;
					fi
				}
			fi

	:: (status[_pid] == post_updating) || (status[_pid] == post_reverting) -> 

		allSuccess = 1;
		for (i : 0 .. noClients - 1) {		
			if
			:: (connected[i] == 1) -> 
				clientTOcm[i]?response;
				if												
				:: (response == fail) -> 
					allSuccess = 0;
					break;												
				:: else -> skip;						 						
				fi
			:: else -> skip;
			fi			    						
		}

		if
		:: (allSuccess == 1) ->	
			atomic{
				allowedManualUpdate = 1;																			
				status[_pid] = idle;
			}

			for (i : 0 .. noClients - 1) {
				if
				:: (connected[i] == 1) -> status[i] = idle;
				:: else -> skip;
				fi
			}


		:: (allSuccess == 0) -> 
			atomic{				
				allowedManualUpdate = 1;
				status[_pid] = idle;
			}	

			for (i : 0 .. noClients -1) {
				if
				:: (connected[i] == 1) -> cmTOclient[i]!disconnect; atleastOneConnection = 0;
				:: else -> skip;
				fi
			}																	
																		
		fi
    od
	
	

}

active proctype controlPanel(){
	do
	::  (allowedManualUpdate == 1) -> cpTOcm!update;
	od

}


#define p1 (allowedManualUpdate == 1)
ltl deadlock { [] (!p1 -> <> p1) }

/* Following LTL can be used to test the model for client initialization 

   s - will produce a sequence where one client successfuly connects
   u1 - will produce a sequence where a client is unsuccessful due to failure in getting new weather
   u2 - will produce a sequence where a client is unsuccessful due to failure in using new weather

   s1, s2, s3, s4 - checks if state transition is correct

*/

#define a (status[0] == idle)
#define b (status[0] == pre_initialization)
#define c (status[0] == initializing)
#define d (status[0] == post_initialization)
#define e (status[0])
#define x (allowedManualUpdate == 1)
#define y (connected[0] == 1)
#define z (status[3] == idle)
  
ltl s { [] !((!y) -> <> b -> <> c -> <> d -> <> (x && y && z && a)) }

     
ltl u1 { <>c -> <> d}
ltl u2 { <>d -> <> (a && x) }

ltl s1 { <> a -> <> b }
ltl s2 { <> b -> <> (c || a)  }
ltl s3 { <> c -> <> (d || !y)  }
ltl s4 { <> d -> <> (a || !y)  }
