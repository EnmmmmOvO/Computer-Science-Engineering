/* Bakery algorithm for solving the CS problem */

#include "critical2.h"

byte np = 0, nq = 0;

active proctype p() {
  do
    :: non_critical_section();
waitp:   np = nq + 1;
       (nq == 0 || np <= nq);   /* await */
csp:   critical_section();
       np = 0
  od
}

active proctype q() {
  do
    :: non_critical_section();
waitq:   nq = np + 1;
       (np == 0 || nq < np);   /* await */
csq:   critical_section();
       nq = 0
  od
}

ltl growth { [](np < 255) }