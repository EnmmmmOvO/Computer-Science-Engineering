bit turn = 0

proctype P() {
  // non-critical section
  do
  :: do
     :: true -> break
     :: true -> skip
  od;
  // pre-protocol
waitp: turn == 0;
  // critical section
csp: skip
  // post-protocol
  turn = 1
  od
}

proctype Q() {
  do
  :: do
     :: true -> break
     :: true -> skip
     od;
waitq: turn == 1;
csq: skip
  turn = 0
  od
}

init {
      run P();
      run Q();
}

ltl mutex {[]!(P@csp && Q@csq)}
ltl eeP {[](P@waitp implies <>P@csp)}
ltl eeQ {[](Q@waitq implies <>Q@csq)}