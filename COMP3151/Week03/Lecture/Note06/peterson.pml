#define MutexDontCare
#include "critical2.h"

#define PROCS 3

byte in[PROCS];
byte last[PROCS-1];

proctype P(byte i) {
  byte j = 0;
  byte k = 0;
  do
  :: non_critical_section();
waitp:  for (j : 2 .. PROCS) {
       in[i-1] = j;
       last[j-2] = i;
       for (k : 1 .. PROCS) {
         (k == i || in[k-1] < j || last[j-2] != i)
       }
     }
csp: critical_section();
     in[i-1] = 0;
  od
}

init {
  byte pr = 0;
  atomic {
  for(pr : 1 .. PROCS) {
    in[pr-1] = 0;
    if
    :: pr != PROCS -> last[pr-1] = 0;
    :: else -> skip;
    fi;
    run P(pr);
  }
  }
}

/* Similar eventual entry properties for the other three processes elided
   Since most algorithms aren't entirely symmetric, it's nonetheless recommended
   to check all.
 */
ltl eventual_entry { []((P[1]@waitp) implies eventually (P[1]@csp))}

#define occupied (!P[1]@csp && P[2]@csp)
#define not_occupied (!P[1]@csp && !P[2]@csp)

/* This property states that while process 1 is in the first waiting room,
   process 2 can enter the critical section at most once.

   Similar linear wait properties for the other process permutations elided */
ltl linear_wait
  { []((in[0] == 2 && in[1] == 0)
       implies
       not_occupied U (occupied U (not_occupied U P[1]@csp)))
  }
ltl mutex { [](!(P[1]@csp && P[2]@csp) && !(P[1]@csp && P[3]@csp) && !(P[2]@csp && P[3]@csp))}