/* Note that this solution may deadlock, for the same reason as the lock-based solution we considered earlier.

You may check this by using Promela to search for invalid end-states.

You can apply the same fix as before to remedy this (imposing a total order on the forks to break the symmetry).
*/
#define N 3

chan forks[N] = [0] of { bit };

inline think() {
  do
  :: true -> skip;
  :: true -> break;
  od
}

proctype philosopher(byte i) {
  do
  :: think();
     // pattern matching
     // receive the first message in the queue
     // but only if it equals true
     forks[i] ? true;
     forks[(i + 1) % N] ? true;
     // eat
     forks[i] ! true;
     forks[(i + 1) % N] ! true;
  od
}

proctype fork(byte i) {
  do
  :: forks[i] ! true;
     forks[i] ? true;
  od
}

init {
  byte i = 1;
  for(i : 1 .. N) {
    run philosopher(i-1);
    run fork(i-1);    
  }
}