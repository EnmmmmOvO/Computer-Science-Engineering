
#include "critical.h"

bit turn = 0;

/* We use variables inCritical,inNonCritical only to make error traces easier to understand
   They are set in routines non_critical_section() and critical_section() in critical.h
*/ 

proctype P() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ; 
  do
  :: non_critical_section();
     waitp: turn == 0;
     csp: critical_section();
     turn = 1
  od
}
proctype Q() {
  bit inNonCritical = 1 ;
  bit inCritical = 0 ;  
  do
  :: non_critical_section();
     waitq: turn == 1;
     csq: critical_section();
     turn = 0
  od
}

init { run P(); run Q(); }

ltl mutex { always !(P@csp && Q@csq)}
ltl mutexv2 { always !(P:inCritical && Q:inCritical)}

ltl waitp { [] (P@waitp implies (<> P@csp))  }
ltl waitq { [] (Q@waitq implies (<> Q@csq))  }

/* Note that the following does not hold, even with weak fairness enabled */
ltl eventually_want { [] ((P:inNonCritical == 1) implies <> (P:inNonCritical == 0)) } 
