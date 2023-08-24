<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 7)</font></center>

1. **Non-compositional Verification**: Here is a three process message passing system presented as a transition diagram of three processes $P_1$, $P_2$, and $P_3$.

   <img src="/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/6_1.png" alt="6_1" style="zoom:40%;" />

   Prove using the Levin and Gries or AFR methods that the following Hoare triple holds:
   $$
   \{\ \text{True}\ \}\ P_1\ ||\ P_2\ ||\ P_3\  \{\ y=v-1\ \}
   $$
   Give your assertion networks, your extra auxiliary variables, and (if using AFR) your communication invariant. List and discharge the proof obligations.

   > $$
   > R \neq 3\ \land\lnot(Q=2 \land R = 1) \land\lnot(P=2\land Q\ =1\land R=1)\land (P=2)\land (Q=1)\Rightarrow I[\frac{Q}{2}] [\frac{P}{3}]\\
   > T\Rightarrow x=v[x/v]\\
   > T\Rightarrow c=c\\
   > x=v\Rightarrow y=v-1[y/x-1]\\
   > x=y\Rightarrow x-1=y-1
   > $$

2. **Termination**: Consider the following program:

   <img src="/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/6_2.png" alt="6_2" style="zoom:50%;" />

   - Use the local method to prove $x ≥ 0$ -convergence for this program. You’ll need exit locations for $p$ and $q$ (not shown in the above pseudocode). First specify your assertion networks, your wellfounded set, and your ranking functions. Then list and discharge the proof obligations. 
   
     > 1. **Initialization**: \(P\) holds before `p` and `q` start:
     >    - Before `p` starts, \(x\) is an arbitrary integer. The predicate \(P(x) = (x ≥ 0)\) may or may not hold.
     >    - Before `q` starts, \(x\) should be non-negative, so \(P(x) = (x ≥ 0)\) holds.
     >
     > 2. **Consecution**: If \(P\) holds before an iteration of `p` or `q`, then \(P\) also holds after:
     >    - For `p`, we can see that if \(P(x)\) holds before \(p_2\), then \(P(x + 1)\) also holds after \(p_2\) since adding 1 to a non-negative number keeps it non-negative. This discharges the consecution obligation for `p`.
     >    - For `q`, if \(P(x)\) holds before \(q_1\), then \(P(2x)\) also holds after \(q_1\) since multiplying a non-negative number by 2 keeps it non-negative. This discharges the consecution obligation for `q`.
     >
     > 3. **Exit**: If `p` or `q` exits, then \(P\) still holds:
     >    - For `p`, it exits when \(x ≠ 0\) is false, i.e., when \(x = 0\). Since 0 is non-negative, \(P(x)\) holds at `p_exit`.
     >    - For `q`, it exits after \(q_1\), and we've shown in the consecution step that \(P(2x)\) holds after \(q_1\). Therefore, \(P(x)\) holds at `q_exit`.
     >
     > 4. **Decrease**: The ranking function \(R\) decreases on each iteration and remains in the wellfounded set \(W\):
     >    - For `p`, \(R_p(x) = x\) decreases on each iteration of \(p_2\) (since \(x\) increases by 1) and remains in \(W\).
     >    - For `q`, \(R_q(x) = x\) doesn't decrease on \(q_1\) (since \(x\) is multiplied by 2).
   - Is this program $\top$-convergent? Briefly motivate your answer. 
   
     > No. The loop $p$ ($p_1$ and $p_2$) will only terminate if $x = 0$. If $x$ starts as a positive number, the loop $p$ will run indefinitely, because $x$ is incremented in every iteration $p_2$, so it will never be zero. Hence, the program is not guaranteed to terminate for all initial states. 
     >
   - Is this program $\bot$-convergent? Briefly motivate your answer.
   
     > No. As discussed earlier, if \(x\) starts as a positive number, the loop $p$ will run indefinitely because $x$ is incremented in every iteration $p_2$, so it will never be zero. Consequently, the program is not guaranteed to reach a halt state from all initial states, violating the definition of $\bot$-convergence. 
   
   You may assume that the $x := x−1$ and $x := 2∗x$ are executed atomically