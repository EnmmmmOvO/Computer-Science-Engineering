/* Lamport's fast algorithm for solving the CS problem */

#define PID
#define NPROC 2
#include "critical2.h"

/* need OPEN to be different from all the PIDs 0..NPROC-1 */
#define OPEN NPROC

byte gate1 = OPEN, gate2 = OPEN;
bool want[NPROC] = false;

active[NPROC] proctype p() {
  do
    :: non_critical_section();
waitp:   gate1 = _pid;
       want[_pid] = true;
       printf ("MSC: %d passed gate 1.\n", _pid);
       if
         :: gate2 != OPEN ->
            want[_pid] = false;
            printf ("MSC: %d found gate 2 closed and loops.\n", _pid);
            goto waitp
         :: else ->
            printf ("MSC: %d found gate 2 open.\n", _pid);
       fi;
       gate2 = _pid;
       printf ("MSC: %d passed gate 2.\n", _pid);
       if
         :: gate1 != _pid ->
            want[_pid] = false;
            printf ("MSC: %d looked back at a changed gate 1 and waits.\n", _pid);
            want[1 - _pid] == false;     /* await;  only ok for NPROC = 2 */
            printf ("MSC: %d is done sitting in gate 2.\n", _pid);
            if
              :: gate2 != _pid ->
                 printf ("MSC: %d found gate 2 closed and loops.\n", _pid);
                 goto waitp
              :: else -> want[_pid] = true
            fi
         :: else
       fi;
csp:   critical_section();
       gate2 = OPEN;
       want[_pid] = false
  od
}

/* made for NPROC = 2 */
#define pwaitp	p[0]@waitp
#define pcsp	p[0]@csp
#define qwaitp	p[1]@waitp
#define qcsp	p[1]@csp
#define qbored  !want[1]

ltl mutex { !<>(pcsp && qcsp) }
ltl dlf   { [](pwaitp && qwaitp -> <>(pcsp || qcsp)) }
ltl aud   { [](pwaitp && ([]qbored) -> <>pcsp) }
ltl ee    { [](pwaitp -> <>pcsp) }
