<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 5)</font></center>

1. **Reasoning about message passing**

   Here is a critical section algorithm that uses synchronous message passing:

   ![hw5_1](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/5_1.png)

   Only processes `x` and `y` are competing for the critical section; `z` is an auxiliary process. The critical sections are at lines `x_2` and `y_2`; `x_1` and `y_1` are the non-critical sections. The program variables x,y,z are just dummies; their values and types are unimportant. 

   The transition diagrams for these processes are as follows.

   ![hw5_2](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/5_2.png)

   (The self-loop is not depicted in the code above; it represents the ability to stay in the non-critical section forever). 

   > ```c
   > #include "critical.h"
   > 
   > chan ch = [0] of  { byte };
   > 
   > proctype X() {
   >     do
   >     :: non_critical_section() ->
   > waitx:  ch?0;
   > csx:    critical_section();
   >         ch!0
   >     od
   > }
   > 
   > proctype Y() {
   >     do
   >     :: non_critical_section() ->
   > waity:  ch?0;
   > csy:    critical_section();
   >         ch!0
   >     od
   > }
   > 
   > proctype Z() {
   >     do
   >     :: ch!0 -> 
   >         ch?0
   >     od
   >    }
   >    
   > init {
   >  run X();
   >  run Y();
   >     run Z();
   >    }
   >    
   > ltl mutex { [] !(X@csx && Y@csy)}
   > ltl wait1 { [] (X@waitx implies (eventually X@csx))  }
   > ltl wait2 { [] (Y@waity implies (<> Y@csy))  }
   > ```

   1. Construct the closed product of these transition diagrams. The initial state will be `<x_1, y_1, z_1>`. 

      > ```c
      > 
      >                 ch <= x, ch => z                   ch <= z, ch => y
      >                ----------------->                 ----------------->
      > <x_2, y_1, z_2>                    <x_1, y_1, z_1>                    <x_1, y_2, z_2>
      >       |⋀       <-----------------                 <-----------------         ⋀|
      >       ||         ch <= z, ch => x                   ch <= y, ch => z  			 ||											
      >       ||                        ch <= y, ch => x                             ||
      >       ||---------------------------------------------------------------------||           
      >       |-----------------------------------------------------------------------|            
      >                   							 ch <= x, ch => y 
      >    
      > ```

   2. It’s obvious from inspection of the closed product that this algorithm satisfies mutual exclusion. Why? 

      > Since only the program that gets the signal can enter the critical section, while ` z` sends a signal it must wait for an accepted signal before sending the next one, there will not be two identical programs in the critical section. Transition diagrams shows that only if any criticalsection returns only the state `<x_1, y_1, z_1>`, another process can enter.

   3. Does this algorithm satisfy eventual entry? Briefly motivate.

      > In my implementation, the eventual entry may not be satisfied because there may be a case where process `z` keeps selecting process `x` or `y`, resulting in another process not getting a signal to enter the critical section.

   4. Does this algorithm still work if we flip all inputs to outputs, and vice versa? Briefly motivate. 

      >I think it holds, because it is a synchronous channel, suppose `x` sends permission to enter the critical section first, `z` blocks at this state and waits for x to accept the message. Then `y` at this time `y`'s sending state will be blocked until x ends the critical section and accepts `z`'s signal after completion, waiting for z to convert to the accepted state, after that it is possible to enter, It satisfies mutual exclusion.

   5. The algorithm behaves oddly if we make **ch** asynchronous. Describe a scenario that (a) assumes an asynchronous, reliable channel; (b) goes on forever in a cycle; and (c) takes transitions other than the self-loops at `x_1` and `y_1` infinitely often; and (d) never visits locations `x_2` and `y_2`.

      > Because of the asynchronous channel, whether there is no acceptance, `z` can send a message after, when he finished sending from `z_1` to `z_2`, immediately perform `z_2` to `z_1` to accept this message, keep repeating this process, `x` and `y` will never request a message to in self-loops in `x_1` or `y_1`

2. **Philosophers**

   Develop a solution for the dining philosophers problem using only message passing, under the additional restriction that each channel must be connected to exactly one sender and exactly one receiver. By way of a hint, the following things do not work: 

   - Having only 5 processes, one for each philosopher.
   - Having only 5 channels, one for each fork. 

   Configure the solution to run forever, in a 5 philosopher scenario.

   > ```c
   > # define N 5
   > 
   > byte philosophers[N];
   > byte forks[N];
   > chan waiter = [0] of { byte };
   > 
   > proctype P(byte i) {    
   >     do
   >     :: philosophers[i] = 1 ->
   >         waiter?i;
   >   			philosophers[i] = 0
   >         printf("%d is eating!\n", _pid);
   >         forks[i] = 0;
   >         forks[(i + 1) % N] = 0;
   >     od
   > }
   > 
   > proctype W() {    
   >     do
   >     :: philosophers[0] == 1 && forks[0] == 0 && forks[1] == 0 ->
   >         forks[0] = 1;
   >         forks[1] = 1;
   >         waiter!0;
   >     :: philosophers[1] == 1 && forks[1] == 0 && forks[2] == 0 -> 
   >         forks[1] = 1;
   >         forks[2] = 1;
   >         waiter!1;
   >     :: philosophers[2] == 1 && forks[2] == 0 && forks[3] == 0 -> 
   >         forks[2] = 1;
   >         forks[3] = 1;
   >         waiter!2;
   >     :: philosophers[3] == 1 && forks[3] == 0 && forks[4] == 0 -> 
   >         forks[3] = 1;
   >         forks[4] = 1;
   >         waiter!3;
   >     :: philosophers[4] == 1 && forks[4] == 0 && forks[0] == 0 -> 
   >         forks[0] = 1;
   >         forks[4] = 1;
   >         waiter!4;
   >     od
   > }
   > 
   > init {
   >     byte i;
   >     for (i: 0 .. N-1) {
   >         philosophers[i] = 0;
   >         forks[i] = 0;
   >     }
   >     run P(0);
   >     run P(1);
   >     run P(2);
   >     run P(3);
   >     run P(4);
   >     run W();
   > }
   > ```

3. **Fair Merge**

   Develop an algorithm to merge two sequences of data. A process called `merge` is given three channel parameters of type `byte`, receives data on two input channels and interleaves the data on the output channel, such that if the two inputs are sorted (in ascending order), then the output is sorted. 

   Try to implement a fair merge that is free from starvation of both input channels when possible. This means that you should try to make sure every input stream is always eventually read from. This requirement will sometimes be impossible to reconcile with the sortedness requirement. If so, keeping the outputs sorted takes priority. For example, if the two input channels transmit infinite streams of 1:s and 2:s, respectively, no 2:s should be sent on the output channel. 

   Assume that the value 255 is a special `EOF` signal, and no further data will be sent on a channel after `EOF` is sent. Your merge process should terminate if all data has been transmitted. Assume that an `EOF` will be sent at the end of the data stream (if it ends).
   
   > ```c
   > #define SIZE 3
   > #define EOF 255
   > 
   > byte shared_array[SIZE * 2];
   > byte hasValue[2];
   > byte value[2];
   > 
   > byte array_x[SIZE];
   > byte array_y[SIZE];
   > 
   > chan ch_x = [0] of { byte };
   > chan ch_y = [0] of { byte };
   > 
   > proctype Input_x() {
   >     byte i = 0;
   >     do 
   >     :: i < SIZE ->
   >         if
   >         :: array_x[i] == EOF -> break;
   >         :: else -> 
   >             ch_x!array_x[i];
   >             i = i + 1;
   >         fi
   >     :: else -> break;
   >     od
   >     ch_x!EOF;
   > }
   > 
   > proctype Input_y() {
   >     byte i = 0;
   >     do 
   >     :: i < SIZE -> 
   >         if
   >         :: array_y[i] == EOF -> break;
   >         :: else -> 
   >             ch_y!array_y[i];
   >             i = i + 1;
   >         fi
   >     :: else -> break;
   >     od
   >     ch_y!EOF;
   > }
   > 
   > proctype Output() {
   >     byte i = 0;
   >     do 
   >     :: i < SIZE * 2 ->
   >         if 
   >         :: hasValue[0] == 2 && hasValue[1] == 2 -> break 
   >         :: hasValue[0] == 2 && hasValue[1] == 1 -> 
   >             shared_array[i] = value[1];
   >             i = i + 1;
   >             hasValue[1] = 0; 
   >         :: hasValue[0] == 1 && hasValue[1] == 2 -> 
   >             shared_array[i] = value[0];
   >             i = i + 1;
   >             hasValue[0] = 0; 
   >         :: hasValue[0] == 1 && hasValue[1] == 1 -> 
   >             if 
   >             :: value[0] < value[1] -> 
   >                 shared_array[i] = value[0];
   >                 i = i + 1;
   >                 hasValue[0] = 0;
   >             :: else -> 
   >                 shared_array[i] = value[1];
   >                 i = i + 1;
   >                 hasValue[1] = 0;
   >             fi
   >         :: hasValue[0] == 0 ->
   >             ch_x?value[0];
   >             if 
   >             :: value[0] == EOF -> hasValue[0] = 2; 
   >             :: else -> hasValue[0] = 1;
   >             fi 
   >         :: hasValue[1] == 0 ->
   >             ch_y?value[1];
   >             if 
   >             :: value[1] == EOF -> hasValue[1] = 2; 
   >             :: else -> hasValue[1] = 1;
   >             fi 
   >         fi
   >     :: else -> break;
   >     od
   > }
   > 
   > init {
   >     hasValue[0] = 0;
   >     hasValue[1] = 0;
   > 
   >     array_x[0] = 1;
   >     array_x[1] = EOF;
   >     array_x[2] = 5;
   > 
   >     array_y[0] = 2;
   >     array_y[1] = 4;
   >     array_y[2] = 6;
   > 
   >     run Input_x();
   >     run Input_y();
   >     run Output();
   > 
   >     byte i;
   >     for (i : 0 .. SIZE * 2 - 1) {
   >         printf("%d ", shared_array[i]);
   >     }
   > }
   > ```

