#include "critical2.h"

bit shared = 0

inline test_and_set(x,y) {
  d_step {
    x = y;
    y = 1;
  }
}

proctype P() {
 bit local = 1;
 do
 :: non_critical_section()
    do
    :: /* await */ shared == 0;
       test_and_set(local,shared)
       if
       local -> break;
       else -> skip
       fi
    od;
    critical_section();
    shared = 0;
   od
}