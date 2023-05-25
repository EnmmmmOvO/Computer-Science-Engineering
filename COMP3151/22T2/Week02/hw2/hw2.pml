#define MutexDontCare
#include "critical2.h"

bit wantp = 0;
bit wantq = 0;
bit wantX = 0;

/*  
turn = 0 (p)
turn = 1 (q)
turn = 2 (X)
turn = 3 (except p, q X)
turn = 4 (except q, p X)
turn = 5 (except X, p q)
*/
bit turn = 0;

proctype P() {
    do
    :: non_critical_section();
waitp: wantp = true
    do
    :: wantq && wantX ->
        if
        :: turn == 0 -> 
            wantp = false;
            turn == 3;
            wantp = true;
        :: turn == 4 ->
            wantp = false;
            turn == 2;
            wantp = true;
        :: turn == 5 ->
            wantp = false;
            turn == 1;
            wantp = true;
        :: else -> skip
        fi
    :: wantq -> 
        if
        :: (turn == 0 || turn == 5) -> 
            wantp = false;
            turn == 1;
            wantp = true;
        :: else -> skip
        fi
    :: wantX -> 
        if
        :: (turn == 0 || turn == 4) -> 
            wantp = false;
            turn == 2;
            wantp = true;
        :: else -> skip
        fi
    :: else -> break
    od
csp: critical_section();
    turn = 0;
    wantp = false;
    od
}

proctype Q() {
    do
    :: non_critical_section();
waitq: wantq = true
    do
    :: wantp && wantX ->
        if
        :: turn == 1 -> 
            wantq = false;
            turn == 4;
            wantq = true;
        :: turn == 3 ->
            wantq = false;
            turn == 2;
            wantq = true;
        :: turn == 5 ->
            wantq = false;
            turn == 0;
            wantq = true;
        :: else -> skip
        fi
    :: wantp -> 
        if
        :: (turn == 1 || turn == 5) -> 
            wantq = false;
            turn == 0;
            wantq = true;
        :: else -> skip
        fi
    :: wantX -> 
        if
        :: (turn == 0 || turn == 3) -> 
            wantq = false;
            turn == 2;
            wantq = true;
        :: else -> skip
        fi
    :: else -> break
    od
csq: critical_section();
    turn = 1;
    wantq = false;
    od
}

proctype X() {
    do
    :: non_critical_section();
waitX: wantX = true
    do
    :: wantp && wantq ->
        if
        :: turn == 2 -> 
            wantX = false;
            turn == 5;
            wantX = true;
        :: turn == 3 ->
            wantX = false;
            turn == 0;
            wantX = true;
        :: turn == 4 ->
            wantX = false;
            turn == 1;
            wantX = true;
        :: else -> skip
        fi
    :: wantq -> 
        if
        :: (turn == 2 || turn == 4) -> 
            wantX = false;
            turn == 1;
            wantX = true;
        :: else -> skip
        fi
    :: wantp -> 
        if
        :: (turn == 2 || turn == 3) -> 
            wantX = false;
            turn == 0;
            wantX = true;
        :: else -> skip
        fi
    :: else -> break
    od
csX: critical_section();
    turn = 2;
    wantX = false;
    od
}

init { run P(); run Q(); run X();}

ltl mutex { [] !(P@csp && Q@csq && X@csX)}
ltl waitp { [] (P@waitp implies (eventually P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }
ltl waitX { [] (X@waitX implies (<> X@csX))  }