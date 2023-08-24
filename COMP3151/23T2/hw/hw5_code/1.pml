#include "critical.h"

chan ch = [0] of  { byte };

proctype X() {
 do
 :: non_critical_section() ->
waitx:  ch?0;
csx:    critical_section();
     ch!0
 od
}

proctype Y() {
 do
 :: non_critical_section() ->
waity:  ch?0;
csy:    critical_section();
     ch!0
 od
}

proctype Z() {
 do
 :: ch!0 -> 
     ch?0
 od
}

init {
 run X();
 run Y();
 run Z();
}

ltl mutex { [] !(X@csx && Y@csy)}
ltl wait1 { [] (X@waitx implies (eventually X@csx))  }
ltl wait2 { [] (Y@waity implies (<> Y@csy))  }