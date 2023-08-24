<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 3)</font></center>

1. **Mutual exclusion**: Use Spin to show that the following Manna-Pnueli program, discussed in lectures, is not correct if we do not treat the if statements as atomic.

   ![3_1](/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/3_1.png)

   (To do this, rewrite the if statement so that it satisfies the **Limited Critical Reference** assumption. ) What about the **await** statements? Does it matter if they are atomic or not? (Give a reason for your answer.)

   > ```c
   > #include "critical.h"
   > 
   > int wantp = 0;
   > int wantq = 0;
   > 
   > proctype P() {
   > bit inNonCritical = 1 ;
   > bit inCritical = 0 ; 
   > do
   > :: non_critical_section();
   >  if
   >  :: wantq == -1 -> wantp = -1
   >  :: else -> wantp = 1
   >  fi
   >  waitp: wantq != wantp;
   >  csp: critical_section();
   >  wantp = 0
   > od
   > }
   > 
   > proctype Q() {
   > bit inNonCritical = 1 ;
   > bit inCritical = 0 ;  
   > do
   > :: non_critical_section();
   >  if
   >  :: wantp == -1 -> wantq = -1
   >  :: else -> wantq = 1
   >  fi
   >  waitq: wantq != -wantp;
   >  csq: critical_section();
   >  wantq = 0
   > od
   > }
   > 
   > init { run P(); run Q(); }
   > 
   > ltl mutex { always !(P@csp && Q@csq)}
   > 
   > ltl waitp { [] (P@waitp implies (<> P@csp))  }
   > ltl waitq { [] (Q@waitq implies (<> Q@csq))  }
   > ```
   >
   > The await statements mark processes `P` and `Q` as `waitp` and `waitq`, respectively. these statements block processes until the condition is true, i.e., another process does not intend to enter its critical zone. If the wait statements are atomic, this means that the check condition and subsequent code execution cannot be interrupted by another process. If they are not atomic, they may result in a race condition, i.e., two processes may pass their wait condition and enter the critical section at the same time, violating the mutual exclusion property.

2. **Hoare Logic**: Show the correctness of the following Hoare logic assertion (a variant of the example we discussed in class) 
   $$
   \{True\}\ i = 0;\ s = 0;\ \textbf{while } i ≤ n \textbf{ do } \{s = s+i;\ i = i+1 \}\ \{s = n(\frac{n + 1}{2})\}
   $$
   where all variables are of type Integer. To do so, show that the following assertions for the transitions are correct:

   - $\{True\}\ i = 0\ \{i = 0\}$
   - $\{i = 0\}\ s = 0\ \{i \leq n + 1 \land s = i( \frac{i−1}{2} )\}$ 
   - $\{i \leq n + 1 \land s = i( \frac{i−1} {2} )\}\ (i ≤ n); s = s + i\ \{i \leq n \land s = i( \frac{i+1} {2} )\} $
   - $\{i \leq n \land s = i( \frac{i+1} {2} )\}\ i = i + 1\ \{i \leq n + 1 \land s = i( \frac{i−1} {2} )\} $
   - $\{i \leq n + 1 \land s = i( \frac{i−1} {2} )\}\ \lnot(i \leq n)\ \{s = n( \frac{n+1}{2} )\}$

   Use the method from the Notes on Floyd’s method to give the detailed translation of these statements to a formula, and prove that the formula is valid. The point of this exercise is to emphasize that the correctness of these sorts of statements can essentially be calculated mechanically, modulo the validity checking (Validity checking itself might be hard once quantifiers or more complicated mathematics are involved.)

   > Set 
   >
   > - $l_0$  is the start of the program
   > - $l_1$ is state after $i=0$
   > - $l_2$ is state after $s=0$
   > - $l_3$ is state before $s=s+1$
   > - $l_4$ is state after $l_3$ and before $i=i+1$
   > - $l_5$ is state after while loop
   >
   > We can change the hoare logic to transition
   >
   > - $l_0 \stackrel{True;\ i=0}{\longrightarrow} l_1$
   > - $l_1 \stackrel{i=0;\ s=0}{\longrightarrow} l_2$
   > - $l_2 \stackrel{i \leq n + 1 \land s = i( \frac{i−1} {2});\ i ≤ n; s = s + i}{\longrightarrow} l_3$
   > - $l_3 \stackrel{i \leq n \land s = i( \frac{i+1} {2});\ i = i + 1}{\longrightarrow} l_4$
   > - $l_4 \stackrel{i \leq n + 1 \land s = i( \frac{i−1} {2});\ i \leq n}{\longrightarrow} l_2$
   > - $l_4 \stackrel{i \leq n + 1 \land s = i( \frac{i−1} {2});\ \lnot(i \leq n)}{\longrightarrow} l_5$
   >
   > We can define the assertion $\mathcal{Q}$ for each location
   >
   > - $\mathcal{Q}(l_0) = True$
   > - $\mathcal{Q}(l_1) = i = 0$
   > - $\mathcal{Q}(l_2) = i \leq n + 1 \land s = i( \frac{i−1}{2})$
   > - $\mathcal{Q}(l_3) = i \leq n \land s = i( \frac{i+1}{2})$
   > - $\mathcal{Q}(l_4) = i \leq n + 1 \land s = i( \frac{i−1}{2})$
   > - $\mathcal{Q}(l_5) = s = n( \frac{n+1}{2})$
   >
   > ​	We need prove each transition is inductive
   >
   > - $\mathcal{Q}(l_0)\land g\Rightarrow\mathcal{Q}(l_1)\circ f$
   >   $$
   >   \mathcal{Q}(l_0):True, g: True, \mathcal{Q}(l_1): i=1, f:i=1\\
   >   True \land True \Rightarrow i=1\circ i=1\\
   >    True \Rightarrow  i=1
   >   $$
   >
   > - $\mathcal{Q}(l_1)\land g\Rightarrow\mathcal{Q}(l_2)\circ f$
   >   $$
   >   \mathcal{Q}(l_0):i=1, g: i=1, \mathcal{Q}(l_1): s=1, f:s=1\\
   >   i=1 \land i=1 \Rightarrow s=1\circ s=1\\
   >   $$
   >
   > - $\mathcal{Q}(l_2)\land g\Rightarrow\mathcal{Q}(l_3)\circ f$
   >
   >   If $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ hold, and $i \leq n$, then after executing $s = s + i$, the new value of $s$ will be $i( \frac{i-1} {2} ) + i$. Also, because $i \leq n$, both $i \leq n$ and $s = i( \frac{i+1} {2} )$ will hold after executing this statement.
   >
   > - $\mathcal{Q}(l_3)\land g\Rightarrow\mathcal{Q}(l_4)\circ f$
   >
   >   If $i \leq n$ and $s = i( \frac{i+1} {2} )$ hold, and $i = i + 1$ is executed, then the new $i$ will be $i+1$ while the value of $s$ remains the same. Since the original $i \leq n$, $i \leq n + 1$ will hold after executing this statement. Also, because the value of $s$ remains unchanged, $s = (i+1)( \frac{i+1 - 1} {2} ) = i( \frac{i}{2} )$ also holds under the new $i$. So, after executing this statement, both $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ will hold.
   >
   > - $\mathcal{Q}(l_4)\land g\Rightarrow\mathcal{Q}(l_2)\circ f$
   >
   >   If $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ hold and $i \leq n$ does not hold (i.e., $i > n$), then we know that $i = n + 1$. In this way, we know that $s = (n+1)(\frac{n}{2}) = n(\frac{n+1}{2})$. So, if $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ hold and $i \leq n$ does not hold, then $s = n( \frac{n+1}{2} )$ will hold.
   >
   > - $\mathcal{Q}(l_4)\land g\Rightarrow\mathcal{Q}(l_5)\circ f$
   >
   >   If $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ holds, and also $i \leq n$ does not hold (i.e., $i > n$), then we know that $i = n + 1$. In this way, we know that $s = (n+1)(\frac{n}{2}) = n(\frac{n+1}{2})$. So, if $i \leq n + 1$ and $s = i( \frac{i-1} {2} )$ holds, and also $i \leq n$ does not hold, then $s = n( \frac{n+1}{2} )$ will hold.
   
3. **Floyd’s method**: Consider the Counters example, with just one process.

   <img src="/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/3_2.png" style="zoom:40%;" />

   Apply Floyd’s method to prove that this terminates with $n = 10$.

   > $$
   > 
   > $$
   >
   > 

4. **Owicki-Gries**: Consider again the Counters example, but now with two processes (each with local variables $i$ and $x$, so that $n$ is the only shared variable) . Apply the Owicki-Gries method to prove that this terminates with $2 \leq n \leq 20$.