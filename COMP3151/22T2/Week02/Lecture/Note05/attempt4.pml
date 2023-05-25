#define MutexDontCare
#include "critical2.h"

bit wantp = 0;
bit wantq = 0;

proctype P() {
  do
  :: non_critical_section();
waitp: wantp = true
     do
     :: wantq -> 
          wantp = false;
          wantp = true;
     :: else ->
          break
     od
csp: critical_section();
     wantp = false;
  od
}
proctype Q() {
  do
  :: non_critical_section();
waitq: wantq = true
     do
     :: wantp -> 
          wantq = false;
          wantq = true;
     :: else ->
          break
     od
csq: critical_section();
     wantq = false;
  od
}

init { run P(); run Q(); }

ltl mutex { [] !(P@csp && Q@csq)}
ltl waitp { [] (P@waitp implies (eventually P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }