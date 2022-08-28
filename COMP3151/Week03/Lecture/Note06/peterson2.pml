/* Peterson's solution to the mutual exclusion problem - 1981 */

#define PID
#define N 2
#include "critical2.h"

bool wantp = false, wantq = false, last = 1

active proctype p()
{
  do
    :: non_critical_section();
waitp:   wantp = true;
       last = 1;
       (!wantq || last == 0);
csp:   critical_section();
       wantp = false
  od
}

active proctype q()
{
  do
    :: non_critical_section();
waitq:   wantq = true;
       last = 0;
       (!wantp || last == 1);
csp:   critical_section();
       wantq = false
  od
}
