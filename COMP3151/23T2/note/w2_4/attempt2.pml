
#include "critical.h"

bit wantp = 0;
bit wantq = 0;

proctype P() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
     waitp: wantq == false;
     wantp = true;
     csp: critical_section();
     wantp = false;
  od
}
proctype Q() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
     waitq: wantp == false;
     wantq = true;
csq: critical_section();
     wantp = true;
  od
}

init { run P(); run Q(); }

ltl mutex { [] !(P@csp && Q@csq)}
ltl mutexv2 { [] !(P:inCritical && Q:inCritical) }
ltl waitp { [] (P@waitp implies (eventually P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }
