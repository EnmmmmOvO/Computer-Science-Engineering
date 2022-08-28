#define N 5

chan forks[N] = [0] of { bit };

inline think() {
   do
   :: true -> skip;
   :: true -> break;
   od
}

proctype philosopher(byte i) {
   bit continue;
   do
   :: think();
      forks[i] ? continue
      if
      :: continue == true -> 
         forks[i] ! false;
         forks[(i + 1) % N] ? continue
         if 
         :: continue == true ->
            forks[(i + 1) % N] ! false;
            forks[(i + 1) % N] ! true;
            forks[i] ! true;
            
         :: else ->
            forks[i] ! true;
         fi;
      :: else -> skip;
      fi;
   od
}

proctype fork(byte i) {
   bit continue;
   forks[i] ! true;
   do
   :: forks[i] ? continue
      if 
      :: continue == true -> forks[i] ! true;
      :: else -> forks[i] ! false;
      fi;
   od
}

init {
   byte i = 1;
   for(i : 1 .. N) {
      run philosopher(i-1);
      run fork(i-1);    
   }
}