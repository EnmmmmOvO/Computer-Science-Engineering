
#include "critical.h"

bit wantp = 0;
bit wantq = 0;
bit turn = 0;

proctype P() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
waitp: wantp = true
     do
     :: wantq -> 
       if
       :: turn == 1 -> 
            wantp = false;
            turn == 0;
            wantp = true;
       :: else -> skip
       fi
     :: else -> break
     od
csp: critical_section();
     turn = 1;
     wantp = false;
  od
}

proctype Q() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
waitq: wantq = true
     do
     :: wantp -> 
          if
          :: turn == 0 -> 
               wantq = false;
               turn == 1;
               wantq = true;
          :: else -> skip
          fi
     :: else -> break
     od
csq: critical_section();
     turn = 0;
     wantq = false;
  od
}

init { run P(); run Q(); }

ltl mutex { [] !(P@csp && Q@csq)}
ltl waitp { [] (P@waitp implies (eventually P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }
