/* Almost correct fast algorithm for solving the CS problem */

#define PID
#define NPROC 2
#include "critical2.h"

/* need OPEN to be different from all the PIDs 0..NPROC-1 */
#define OPEN NPROC

byte gate1 = OPEN, gate2 = OPEN;

active[NPROC] proctype p() {
  do
    :: non_critical_section();
waitp:   gate1 = _pid;
       if
         :: gate2 != OPEN -> goto waitp
         :: else -> skip
       fi;
       gate2 = _pid;
       if
         :: gate1 != _pid -> 
            if
              :: gate2 != _pid -> goto waitp
              :: else -> skip
            fi
         :: else -> skip
       fi;
csp:   critical_section();
       gate2 = OPEN
  od
}
