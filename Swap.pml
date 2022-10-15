/*
    CS 4710 - Model Driven Software Development
    FALL 2022 - R01
    SPIN Project 1 - Parallel Swap 
    Last Modified On: 10/15/2022

    Team Members: 
        - Akshay Kumar Dosapati
        - Justin Milliman

    ============ Project Description ============
    Here we define a shared memory program with N
    processes that have access to an array A[] of
    distinct non-negative integers. Each process
    has access to A, and can perform swaps on A
    as long as no two processes are trying 
    attempting to access similar cells within A. 

    ============ Specifications =================
    1). Follow SIMD
    2). Specify safety and liveness as LTL expressions
    3). The 'Swap code' cannot be in atomic blocks
    4). Processes should be able to perform 
            asynchronously (non-serialzable)
*/

#define N 10 

#define NoDuplication (duplicates == 0)
#define SwapCount (sCount == N)
#define Termination (np_ == 0) // referemce -> https://www.cse.msu.edu/~cse470/PromelaManual/np_.html

// Specification : An array A[] of distinct non-negative integers of size N
int A[N]; 

// willingness to go to CS
bool activePids[N];

//for duplication finding
int duplicates;
int pidNum[N];
bool startSwapProcs = false; // When set to true, all processes will fire
int sCount = 0;

// Main swap
active [N] proctype Swap() {
	int j = 0;
	int currentPid = _pid; // Parametrize by '_pid', not using _pid directly because it's a protected keyword
	int i = currentPid;

    // Track active PIDS 
	activePids[currentPid] = false;
    startSwapProcs == true; // I really love that we can halt things like this
    TRY: do
            ::  (activePids[currentPid] == false) -> 
                        // Select reference -> http://spinroot.com/spin/Man/select.html
                        select (j: 0 .. N);

                        // The atomic blocks set our active pids; atomic so no two pids get set to the same address in 'activePids'
                        atomic {
                            if  // Set current PID 'i' to be an active boi
                                :: activePids[pidNum[i]] == false -> pidNum[i] = currentPid;
                                :: else -> skip;
                            fi;
                        }
                        do      // i is already (hopefully) set as active, and j should be < N 
                            :: ((j == i) || (j == N)) -> select (j: 0 .. N);
                            :: else -> break;
                        od;
                        atomic {
                            if  // Set current PID 'j' to be an active boi
                                :: activePids[pidNum[j]] == false -> pidNum[j] = currentPid;
                                :: else -> skip;
                            fi;
                        }
                        atomic {
                            if  // If we have a valid swap, set it active
                                :: ((pidNum[i] == currentPid) && (pidNum[j] == currentPid)) -> activePids[currentPid] = true;
                                :: else -> skip;
                            fi;
                        }
            // If we are swapping, let it be
            :: (activePids[currentPid] == true) && 
                ( pidNum[i] == currentPid) && (pidNum[j] == currentPid) 
                    -> break;
            // If the PIDS are done, free them from service
            // Running atomically so we can force kill it from service before performing another swap and clashing with an inactive boi
            :: atomic {
                ( pidNum[i] != currentPid) || 
                    (pidNum[j] != currentPid) 
                        -> activePids[currentPid] = false;
            }
        od;

    // Do the swap
    int swap;
    CS: swap = A[j];
        A[j] = A[i];
        A[i] = swap;
        activePids[currentPid] = false;
        sCount++;
}

//ltl dup { [] (Termination -> NoDuplication) }
ltl SwapLTL { [] (Termination -> SwapCount) }

init {
	int j = 0;
	int i = 0;

    // Assign integers to A from [0-(N-1)]
	do
		:: i < N ->    
			A[i] = i;
			pidNum[i] = i;	
			i++;
		:: i >= N -> 
			startSwapProcs = true;
			break;
	od;

    /*
        Once we have performed N swaps, each process has terminated, so check our results for clashes
        This should be replaced with logic to perform any number of swaps for the extra credit, 
        but for now just testing the functional logic
    */
	sCount == N; 

    // Identify duplicates
	do 
		:: (j < N) -> 		
			i = j + 1;
			duplicates = 0;
			do
				:: (i < N) -> 
						if
							:: A[i] == A[j] -> duplicates++;
							:: else -> skip;
						fi;
						i++;
				:: else -> break;
			od;
			if
				:: (duplicates >= 1) -> break; 
				:: else -> skip;
			fi;
			j++;
		:: else -> break;
	od;

}