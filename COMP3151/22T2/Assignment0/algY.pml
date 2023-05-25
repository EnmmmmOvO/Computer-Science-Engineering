#include "critical2.h"

bit b[2] = {0};

proctype P() {
    do
    :: non_critical_section();
wantp: b[0] = 1;
    do
    :: b[1] == 1 ->
        b[0] = 1;
        b[0] == 1;
        b[0] = 1; 
    :: else -> break;
    od
csp: critical_section();
    b[0] = 0;
    od
}

proctype Q() {
    do
    :: non_critical_section();
wantq: b[1] = 1;
    do
    :: b[0] == 1 ->
        b[1] = 0;
        b[0] == 0;
        b[1] = 1; 
    :: else -> break;
    od
csq: critical_section();
    b[1] = 0;
    od
}

init { run P(); run Q(); }

ltl mutex { [] !(P@csp && Q@csq)}
ltl waitp { [] (P@waitp implies (<> P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }