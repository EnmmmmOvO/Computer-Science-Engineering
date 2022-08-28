#define MAX 9
#define K 4

chan inC = [0] of { byte };
chan outC = [0] of { byte };
chan pipe = [0] of { byte };

proctype compress() {
  byte c = 0;
  byte previous = 0;
  byte n = 0;
  inC ? previous;
  do
  :: inC ? c;
     if
     :: c == previous && n < MAX - 1 ->
        n = n + 1;
     :: else ->
        if
        :: n > 0 ->
           pipe ! (n + 49);
           n = 0;
        :: else -> skip;
        fi;
        pipe ! previous;
        previous = c;
     fi;
  od;
}

proctype output() {
  byte c = 0;
  byte m = 0;
  do
  :: pipe ? c;
     outC ! c;
     m = m + 1;
     if
     :: m >= K ->
        outC ! 10;
        m = 0;
     :: else -> skip
     fi;
  od;
}

/* The sink just prints any characters it receives to stdout */
proctype sink() {
  byte c = 0;
  do
  :: outC ? c ->
     printf("%c",c);
  od;
}

/* Transmit the character sequence AAAAABC over and over */
proctype source() {
  do
  :: inC ! 65;
     inC ! 65;
     inC ! 65;
     inC ! 65;
     inC ! 65;     
     inC ! 66;
     inC ! 67;
  od;
}

init {
  run compress();
  run output();

  run source();
  run sink();
}