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
    as long as no two processes are attempting
    to access similar cells within A. 

    ============ Specifications =================
    1). Follow SIMD
    2). Specify safety and liveness as LTL expressions
    3). The 'Swap code' cannot be in atomic blocks
    4). Processes should be able to perform 
            asynchronously (non-serialzable)
*/

#define N 10 // Number of process + Size of A

// Set LTL Definitions
#define NoDuplication (duplicates == 0)
#define SwapCount (sCount == N)
#define Termination (np_ == 0) // docs -> https://www.cse.msu.edu/~cse470/PromelaManual/np_.html

// Specification : An array A[] of distinct non-negative integers of size N
int A[N]; 

// Tracks active pids
bool activePids[N];
int pidNum[N];
bool startSwapProcs = false; // When set to true, all processes will fire

// LTL determinates
int duplicates = 0;
int sCount = 0;

// Instatiate Swap Processes - Currently each process performs a single swap
active [N] proctype Swap() {
	int j = 0;
	int currentPid = _pid; // Parametrize by '_pid', not using _pid directly because it's protected
	int i = currentPid;

    // Track active PIDS 
	activePids[currentPid] = false;
    startSwapProcs == true; // I really love that we can halt things like this
    do
        // Since we are using our own PID as the index for the first cell to access, wait for whoever is currently accessing it
        ::  (activePids[currentPid] == false) -> 
                    select (j: 0 .. N); // Select docs -> http://spinroot.com/spin/Man/select.html

                    // The atomic blocks set our active pids; atomic so no two pids get set to the same address in 'activePids'
                    atomic {
                        if  // Set current PID 'i' to be an active boi
                            :: activePids[pidNum[i]] == false -> pidNum[i] = currentPid;
                            :: else -> skip;
                        fi;
                    }
                    do      // i is already (hopefully) set as active, and j should be in the range of [0 - N] 
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
        /*  
            If the swap is done, free cells from service
            Running atomically so we can force termination before another process clashes and retries 
            even though the cell in A is not being accessed
        */
        :: atomic {
            ( pidNum[i] != currentPid) || 
                (pidNum[j] != currentPid) 
                    -> activePids[currentPid] = false;
        }
    od;

    // Do the roar
    int swap;
    swap = A[j];
    A[j] = A[i];
    A[i] = swap;
    activePids[currentPid] = false;
    sCount++;
}

// All processes should terminate, and no duplicates should exist within A
ltl SwapLTL { [] ( (Termination && NoDuplication) -> SwapCount) }

init {
	int j = 0;
	int i = 0;

	do
        // Assign integers to A from [0-(N-1)]
		:: i < N ->    
			A[i] = i;
			pidNum[i] = i;	
			i++;
        
        // Force start all swap processes
		:: i >= N -> 
			startSwapProcs = true;
			break;
	od;

    /*
        Once we have performed N swaps, each process has terminated, so check our results for clashes
        This should be replaced with logic to perform any number of swaps for the extra credit, 
        but for now just testing the functional bits
    */
	sCount == N; // Wait until all processes are done

    // Identify duplicates
	do 
		:: (j < N) -> 		
			i = j + 1;
			duplicates = 0;
            printf("\n%d", A[j])
			do
				:: (i < N) -> 
						if // If we found one, log it
							:: A[i] == A[j] -> duplicates++;
                            printf("\nDUPE??\n"); // At this stage, this print statement is unreachable
							:: else -> skip;
						fi;
						i++;
				:: else -> break;
			od;
			if  // Fail on any duplicates, as this breaks specification
				:: (duplicates > 0) -> break; 
				:: else -> skip;
			fi;
			j++;
		:: else -> break;
	od;
    printf("\nDuplicates: %d \n", duplicates);
}
