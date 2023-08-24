<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 9)</font></center>

1. a. No. Swapping these lines can potentially lead to a race condition, where both processes set the 'turn' variable before declaring their intention to enter the critical section (by setting b[0] or b[1] to true). If a context switch happens after setting 'turn' but before setting b[0] or b[1], the other process could enter the critical section resulting in a violation of mutual exclusion.

   b. No. If we add the statement `await b[1] = false` at the end of process p, process p would never be able to proceed if process q is not active or stuck in its non-critical section (because b[1] would remain true).

   c. Given that the modified algorithm doesn't satisfy deadlock freedom, it cannot satisfy eventual entry (or "liveness") either. If a process requests to enter its critical section, it should eventually be allowed to do so. However, as described in (b), a deadlock scenario prevents this from happening. Process p may indefinitely wait for process q to complete its critical section, which could result in starvation for process p.  

2. Deposit method: when someone makes a deposit, we simply add the deposit amount to the current balance. We then check to see if there are any processes waiting in the withdrawal queue. If there is, and the current balance is sufficient to satisfy the withdrawal request in the queue, we issue a signal for the process to continue with the withdrawal operation.

   Withdraw method: When someone tries to withdraw money, we first check if the current balance is sufficient. If the balance is insufficient, the process is placed in the withdraw queue and waits. Only when the balance is sufficient, the process can take it out of the queue and deduct the appropriate amount from the balance.

   Use the Signal-and-Continue rule. In the deposit method, after we signal, the process that sent the signal does not immediately yield the processor, but continues execution.

3. 

   ```c
   # a
   
   chan a_meet_b = [0] of {int};
   chan b_meet_a = [0] of {int};
   
   proctype server() {
       int a_count = 0; int b_count = 0; int temp;
       do
       :: a_meet_b ? temp -> a_count++; if a_count >= 1 && b_count >= 1 {a_count--; b_count--; b_meet_a ! 0;}
       :: b_meet_a ? temp -> b_count++; if b_count >= 2 && a_count >= 2 {a_count -= 2; b_count--; a_meet_b ! 0;}
       od
   }
   
   proctype A() {
       a_meet_b ! 0;
       b_meet_a ? 0;
   }
   
   proctype B() {
       b_meet_a ! 0;
       a_meet_b ? 0;
   }
   ```

   ```c
   # b
   
   proctype server() {
       int a_count = 0; int b_count = 0; int waiting_a = 0; int temp;
       do
       :: a_meet_b ? temp -> a_count++; if (a_count >= 2 && b_count >= 1) {a_count -= 2; b_count--; b_meet_a ! 0; a_meet_b ! 0;} else if (a_count >= 1 && b_count >= 1 && waiting_a == 0) {a_count--; waiting_a = 1;}
       :: b_meet_a ? temp -> b_count++; if (b_count >= 2 && waiting_a == 1) {b_count--; waiting_a = 0; a_meet_b ! 0;}
       od
   }
   ```

4. qwqw

   I: $\lnot(s_M\land u_1)\land \lnot (u_2\land (u_M \lor s_M))\land (s_1\Rightarrow s_M)$ 

   ​	$s_1\rightarrow u_1 \circ s_M \rightarrow u_M \Rightarrow \lnot s_M \Rightarrow I$

   ​	$s_1\rightarrow u_1 \circ u_4 \rightarrow t_M \Rightarrow \lnot s_M \Rightarrow I$
5. 

​			$s_2\rightarrow u_2\circ u_M\rightarrow u_3\Rightarrow \lnot(u_M\lor s_M)\Rightarrow I$

​			$s_2\rightarrow u_2\circ u_5\rightarrow t_M\Rightarrow \lnot(u_M\lor s_M)\Rightarrow I$

​		$(s_1\Leftrightarrow s_M)\land \lnot (u_2\land (u_M \lor s_M)) \land (u_4)$ 

​			$s_1\rightarrow u_1 \circ s_M \rightarrow u_M \Rightarrow \lnot s_M \Rightarrow I$

​			$ s_M \rightarrow u_M \circ s_1\rightarrow u_1 \Rightarrow \lnot s_M \Rightarrow I$

​			Q(u_M): x = 0

​				Q(u_3): x = 0

Q(u_5): false

T => X = 0[X/0]

X = 0 => X=0 \land y=1[y/1]

x=0 \land y = 1=> z = 0[z/x]

x = 0 \land y= 1 x ≥ y => F

F => T