<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 2)</font></center>

1. Suppose $x, y, z$ are variables shared with other processes. 

   - The following statement inside a process will not run atomically in most programming languages, although that is how SPIN will treat it. Rewrite the statement as a sequence of statements that satisfy the limited critical reference restriction, so that SPIN simulates the expected behaviour:
     $$
     x=y+z
     $$

     > ```c
     > int n;
     > n = y;
     > n = n + z;
     > x = n;
     > ```

   - Explain why we should not consider the guards in the following nondeterministic program as satisfying the limited critical reference assumption:
     $$
     \begin{align*}
     &\text{if}\\
     &\text{:: }x>0\rightarrow x=0\\
     &\text{:: }y>0\rightarrow x=0\\
     &\text{:: }z>0\rightarrow y=0\\
     &\text{:: else}\rightarrow \text{skip}\\
     &\text{fi}
     \end{align*}
     $$

     > First, the guard condition of each branch involves a different variable, cannot replace all guard conditions with a check on a single variable.
     >
     > Second, The operation of differnet branches may influence other branch's guard's condition.

   - Consider two ways we could rewrite the program in (b). The first one reads the variables into local copies before the if statement. The second considers the cases one by one, using nested if statements. Do these two approaches have the same meaning in a concurrent setting?

     > - The first one reads the variables into local copies before the if statement.
     >
     > ```c
     > int x_record = x;
     > int y_record = y;
     > int z_record = z;
     > 
     > if 
     > :: (x_record > 0) -> x = 0
     > :: (y_record > 0) -> x = 0
     > :: (z_record > 0) -> y = 0
     > :: else -> skip
     > fi
     > ```
     >
     > This method can only consider the situation when `x, y, z` is recorded and cannot reflect the change of `x, y, z` after `x, y, z` is recorded and during the assignment
     >
     > - The second considers the cases one by one, using nested if statements.
     >
     > ```c
     > if
     > :: (x > 0) -> x = 0
     > :: else ->
     > 	if (y > 0) -> x = 0
     > 	:: else -> 
     > 		if 
     > 		:: (z > 0) -> y = 0
     > 		:: else -> skip;
     > 		fi
     > 	fi
     > fi
     > ```
     >
     > The original code we expected to capture as long as the guard condition was positive, but after changing to nesting,  `x > 0` is always captured first, and only if it false will continue to capture `y > 0` and `z > 0`
   
2. We discussed in class that the COUNTERS program has a run where  `n = 2` at termination. Use SPIN to discover a run on which this happens, and then write a brief explanation of how this is possible. (Don’t just repeat the whole interleaving, try to give a succinct description of what is going on.)
   >In this scenario, we need to satisfy the condition that before Proc 1 performs an assignment, Proc 2 reads this value. At this time, `x` in Proc 2 equals 0. Then, while Proc 2 completes the operation `x = x + 1`, Proc 1 continuously runs until the end of the ninth assignment. After that, Proc 2 completes the assignment, and at this point `n = 1`, which is then read by the tenth operation of Proc 1, setting `x = 1`. Then, while Proc 1 completes `x = x + 1`, Proc 2 runs all the way to the end. After Proc 1 completes the assignment `x = 2`, the value of  `n = 2`. 

3. Write SPIN specifications for the following, and use SPIN to determine whether they are true of the COUNTERS program. (Hint, in some cases, you may need to use SPIN to check the negation of the property!)

   - If ever $n = 10$, we will have $n \geq 10$ at all future times. 

     > ```c
     > # define COUNT 10
     > int n = 0;
     > 
     > proctype P() {
     >     int i = 0;
     >     int x  = 0;
     >     for (i : 1 ..COUNT) {
     >         x = n;
     >         x = x + 1;
     >         n = x;
     >     }
     > }
     > 
     > init {
     >     run P();  run P();
     >     _nr_pr ==1;
     >     printf("%d\n", n);
     > }
     > 
     > ltl p1 {[] (n ==10 implies [] (n >= 10))}
     > ```

   - If ever $n = 10$ and process 1 has terminated, then the final value of $n$ will be at least 10. 

     > ```c
     > # define COUNT 10
     > int n = 0;
     > 
     > proctype P() {
     >     int i = 0;
     >     int x  = 0;
     >     for (i : 1 ..COUNT) {
     >         x = n;
     >         x = x + 1;
     >         n = x;
     >     }
     > }
     > 
     > init {
     >     run P();  run P();
     >     _nr_pr ==1;
     >     printf("%d\n", n);
     > }
     > 
     > ltl p2 {[](n == 10 implies _nr_pr == 2) implies [] n >= 10)}
     > ```

   - There is a run where at some point of time, $n = 10$ and both processes have $i = 6$.

     > ```C
     > # define COUNT 10
     > int n = 0;
     > int i_1;
     > int i_2;
     > 
     > proctype P1() {
     >        int x = 0;
     >        for (i_1 : 1 ..COUNT) {
     >            x = n;
     >            x = x + 1;
     >            n = x;
     >     		}
     > }
     > 
     > proctype P2() {
     >        int x = 0;
     >        for (i_2 : 1 ..COUNT) {
     >            x = n;
     >            x = x + 1;
     >            n = x;
     >     		}
     > }
     > 
     > init {
     >        run P1();  run P2();
     >        _nr_pr ==1;
     >        printf("%d\n", n);
     > }
     > 
     > ltl p3 {!<> (n==10 && i_1 == 6 && i_2 == 6)}
     > ```

4. Consider a situation where a row of $n$ male frogs face off against a row of $n$ female frogs at opposite ends of a bridge, with enough space between them for one frog. They would all like to get to the other side. Frogs can make the following two types of moves: (1) if there is an empty space immediately ahead of them, move into it, and (2) if there is a frog ahead of them, and an empty space immediately after that frog, jump over the one ahead and land in the empty space. (For the purposes of this exercise frogs are not allowed to jump on top of other frogs, and can’t jump over more than one frog.) Model this scenario in Promela for $n = 3$, and use Spin’s counter-example capabilities to find a sequence of moves that get all the frogs across to the other side of the bridge from where they start. (Submit both your Promela code and a succinct description of the solution.)

   Frog Puzzle:
   ![image-20230611022021980](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/2_1.png)

   One Step of the Frog Puzzle (after the second female hops over the first) :
   ![image-20230611022043236](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/2_2.png)

   Final State of the Frog Puzzle:

   ![image-20230611022236357](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/2_3.png)

   > ```c
   > #define E 0
   > #define M 1
   > #define F 2
   > #define N 3
   > 
   > byte bridge[2 * N + 1];
   > 
   > inline move(i) {
   >        if 
   >        :: (i < N && bridge[i] == M && bridge[i + 1] == E) -> bridge[i + 1] = M; bridge[i] = E;
   >        :: (i < N - 1 && bridge[i] == M && bridge[i + 2] == E) -> bridge[i + 2] = M; bridge[i] = E;
   >        :: (i > 0 && bridge[i] == F && bridge[i - 1] == E) -> bridge[i - 1] = F; bridge[i] = E;
   >        :: (i > 1 && bridge[i] == F && bridge[i - 2] == E) -> bridge[i - 2] = F; bridge[i] = E;
   >        fi
   > }
   > 
   > init {    
   >        int j;
   >        for(j : 0 .. N - 1) {
   >            bridge[j] = M;
   >        }
   >        bridge[N] = E;
   >        for(j : N + 1 .. 2 * N) {
   >            bridge[j] = F;
   >        }
   > 
   >        do
   >        :: (bridge[0] == E && bridge[1] == M && bridge[2] == M) -> break;
   >     :: (bridge[0] == F && bridge[1] == E && bridge[2] == M && bridge[3] == M) -> break;
   >     :: (bridge[0] == F && bridge[1] == F && bridge[2] == E && bridge[3] == M && bridge[4] == M) -> break;
   >     :: (bridge[1] == F && bridge[2] == F && bridge[3] == E && bridge[4] == M && bridge[5] == M) -> break;
   >     :: (bridge[2] == F && bridge[3] == F && bridge[4] == E && bridge[5] == M && bridge[6] == M) -> break;
   >     :: (bridge[3] == F && bridge[4] == F && bridge[5] == E && bridge[6] == M) -> break;
   >     :: (bridge[4] == F && bridge[5] == F && bridge[6] == E) -> break;
   >        :: move(0);
   >        :: move(1);
   >        :: move(2);
   >        :: move(3);
   >        :: move(4);
   >        :: move(5);
   >        :: move(6);
   >        od
   > 
   >     assert(!(bridge[0] == F && bridge[1] == F && bridge[2] == F && bridge[3] == E && bridge[4] == M && bridge[5] == M && bridge[6] == M));
   > }
   > ```
   >
   > My code does not seem to find a counterexample to confirm that this has a solution when `n = 3`. 

5. Consider the following concurrent program:

   ![2_4](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/2_4.png)

   Draw its state transition diagram.

   > Define **T/F, T/F** as the status of **wantp, wantq**
   >
   > ![2_5](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/2_5.png)

   