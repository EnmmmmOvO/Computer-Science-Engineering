#include "critical.h"

bit wantp = 0;
bit wantq = 0;

proctype P() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
     wantp = true;
waitp: wantq == false;
csp: critical_section();
     wantp = false;
  od
}
proctype Q() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
     wantq = true;
waitq: wantp == false;
csq: critical_section();
     wantq = false;
  od
}

init { run P(); run Q(); }

ltl mutex { [] !(P@csp && Q@csq)}
ltl waitp { [] (P@waitp implies (eventually P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }
