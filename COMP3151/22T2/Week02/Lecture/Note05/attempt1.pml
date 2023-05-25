#define MutexDontCare
#include "critical2.h"

bit turn = 0;

proctype P() {
  do
  :: non_critical_section();
waitp: turn == 0;
csp: critical_section();
     turn = 1
  od
}
proctype Q() {
  do
  :: non_critical_section();
waitq: turn == 1;
csq: critical_section();
     turn = 0
  od
}

init { run P(); run Q(); }

ltl mutex { always !(P@csp && Q@csq)}
ltl waitp { [] (P@waitp implies (<> P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }