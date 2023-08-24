# define N 5

byte philosophers[N];
byte forks[N];
chan waiter = [0] of { byte };

proctype P(byte i) {    
    do
    :: philosophers[i] = 1 ->
        waiter?i;
        philosophers[i] = 0
        printf("%d is eating!\n", _pid);
        forks[i] = 0;
        forks[(i + 1) % N] = 0;
    od
}

proctype W() {    
    do
    :: philosophers[0] == 1 && forks[0] == 0 && forks[1] == 0 ->
        forks[0] = 1;
        forks[1] = 1;
        waiter!0;
    :: philosophers[1] == 1 && forks[1] == 0 && forks[2] == 0 -> 
        forks[1] = 1;
        forks[2] = 1;
        waiter!1;
    :: philosophers[2] == 1 && forks[2] == 0 && forks[3] == 0 -> 
        forks[2] = 1;
        forks[3] = 1;
        waiter!2;
    :: philosophers[3] == 1 && forks[3] == 0 && forks[4] == 0 -> 
        forks[3] = 1;
        forks[4] = 1;
        waiter!3;
    :: philosophers[4] == 1 && forks[4] == 0 && forks[0] == 0 -> 
        forks[0] = 1;
        forks[4] = 1;
        waiter!4;
    od
}

init {
    byte i;
    for (i: 0 .. N-1) {
        philosophers[i] = 0;
        forks[i] = 0;
    }
    run P(0);
    run P(1);
    run P(2);
    run P(3);
    run P(4);
    run W();
}