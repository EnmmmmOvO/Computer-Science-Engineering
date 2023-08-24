<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 1)</font></center>

1. **Dining Cryptographers:**  If we denote the variables of the protocol by (for $i = 0, 1, 2$) the boolean variables $c_i$ for cryptographer $i$ ’s coin toss, $p_i$ for whether or not cryptographer $i$ paid, then cryptographer $i$ ’s public announcement $a_i$ is $p_i \oplus c_i \oplus c_{i-1\ \ \text{mod}\  3}$

   We showed the *correctness* of the Dining Cryptographers protocol in lectures, by demonstrating that $c_0 \oplus c_1 \oplus c_2 = p_0 \oplus p_1 \oplus p_2$ . Noting that at most one of the $p_i$ is equal to 1, this expression expresses whether or not one of the cryptographers paid for the dinner.

   Note that cryptographer $i$ sees only the following variables:
   $$
   p_i,\ c_i,\ c_{(i−1\ \text{mod}\ 3)},\ a_0,\ a_1,\ a_2.
   $$
   Consider a scenario where cryptographer 0 paid — call this the “real world”. Consider cryptographer 2. Show the *security* of the protocol, by demonstrating that at the end of the protocol, cryptographer 2 cannot deduce from their observations whether cryptographer 0 paid or whether cryptographer 1 paid. That is, there exist two scenarios (in which at most one of the cryptographers paid) in which cryptographer 2’s variables have exactly the same values as in the real world, but in which $p_0 = 1$ in one scenario and $p_1 = 1$ in the other.

   > According to the tpoic, we can see that
   > $$
   > a_0 = p_0\oplus c_0 \oplus c_{0-1\ \text{mod}\ 3}= p_0\oplus c_0 \oplus c_2\\
   > a_1 = p_1\oplus c_1 \oplus c_{1-1\ \text{mod}\ 3}= p_1\oplus c_1 \oplus c_0\\
   > a_2 = p_2\oplus c_2 \oplus c_{2-1\ \text{mod}\ 3}= p_2\oplus c_2 \oplus c_1
   > $$
   > For real world 
   > $$
   > \begin{align*}
   > a_0&=1\oplus c_0 \oplus c_2\\
   > a_1&=c_0\oplus c_1\\
   > a_2&=c_1\oplus c_2\\
   > a_0\oplus a_1\oplus a_2&=1\oplus c_0\oplus c_2\oplus c_0\oplus c_1\oplus c_1\oplus c_2
   > \end{align*}
   > $$
   > First, consider the scenario of $p_0=1$:
   >
   > - Assume $c_0,c_1,c_2$ not change, the result is same as the real world
   >
   > - Assume $c_0$ or $c_1$ change, suppose $c_0$ change $c_0'=c_0\oplus 1$
   >   $$
   >   \begin{align*}
   >   &a_0'=1\oplus c_0'\oplus c_2=1\oplus (c_0\oplus 1)\oplus c_2=1\oplus a_0\\
   >   &a_1'=c_0'\oplus c_1=(c_0\oplus 1)\oplus c_1=1\oplus a_1\\
   >   &a_2'=a_2\\
   >   &a_0'+a_1'+a_2'=1\oplus a_0\oplus 1\oplus a_1\oplus a_2=a_0+a_1+a_2
   >   \end{align*}
   >   $$
   >   the result is same as the real world
   >
   > - Assume $c_0, c_1$ change, $c_0'=c_0\oplus 1, c_1'=c_1\oplus 1$
   >   $$
   >   \begin{align*}
   >   &a_0'=1\oplus c_0'\oplus c_2=1\oplus (c_0\oplus 1)\oplus c_2=1\oplus a_0\\
   >   &a_1'=c_0'\oplus c_1'=(c_0\oplus 1)\oplus (c_1\oplus 1)=a_1\\
   >   &a_2'=c_1'\oplus c_2=(c_1\oplus 1)\oplus c_2=1\oplus a_2\\
   >   &a_0'+a_1'+a_2'=1\oplus a_0\oplus a_1\oplus 1\oplus a_2=a_0+a_1+a_2
   >   \end{align*}
   >   $$
   >   the result is same as the real world
   >
   > Second, consider the scenario of $p_1=1$:
   > $$
   > \begin{align*}
   > a_0&=c_0 \oplus c_2\\
   > a_1&=1\oplus c_0\oplus c_1\\
   > a_2&=c_1\oplus c_2
   > \end{align*}
   > $$
   >
   > - Assume $c_0,c_1,c_2$ not change
   >   $$
   >   a_0\oplus a_1\oplus a_2=c_0\oplus c_2\oplus 1\oplus c_0\oplus c_1\oplus c_1\oplus c_2
   >   $$
   >   As the $c_0, c_1,c_2$ not change, $a_0\oplus a_1\oplus a_2$ will same as the real world.
   >
   > - Assume $c_0$ or $c_1$ change, suppose $c_0$ change $c_0'=c_0\oplus 1$
   >   $$
   >   \begin{align*}
   >   &a_0'=c_0'\oplus c_2=(c_0\oplus 1)\oplus c_2=1\oplus a_0\\
   >   &a_1'=1\oplus c_0'\oplus c_1=1\oplus (c_0\oplus 1)\oplus c_1=1\oplus a_1\\
   >   &a_2'=a_2\\
   >   &a_0'+a_1'+a_2'=1\oplus a_0\oplus 1\oplus a_1\oplus a_2=a_0+a_1+a_2
   >   \end{align*}
   >   $$
   >   the result is same as the real world
   >
   > - Assume $c_0, c_1$ change, $c_0'=c_0\oplus 1, c_1'=c_1\oplus 1$
   >   $$
   >   \begin{align*}
   >   &a_0'=c_0'\oplus c_2=(c_0\oplus 1)\oplus c_2=1\oplus a_0\\
   >   &a_1'=c_0'\oplus c_1'=1\oplus (c_0\oplus 1)\oplus (c_1\oplus 1)=a_1\\
   >   &a_2'=c_1'\oplus c_2=(c_1\oplus 1)\oplus c_2=1\oplus a_2\\
   >   &a_0'+a_1'+a_2'=1\oplus a_0\oplus a_1\oplus 1\oplus a_2=a_0+a_1+a_2
   >   \end{align*}
   >   $$
   >   the result is same as the real world

2. **Safety and Liveness:** Let $s$ be a state, and let $s^\omega$ denote the behaviour $ssssssssssss . . .$ (i.e. infinitely many repetitions of $s$.)

   Give an example of a set $A$ such that $s^\omega \in \overline{A}$ , but $s^\omega \notin A$ .

   > Assume the  $A=\{\exists n \in \mathbb{N},\sigma = s^ni^\omega\}$, now as the $\sigma$ in A is countable, the $s^\omega \notin A$, the limit closure of A is $\overline{A}=\{s^\omega, i^\omega\}$, therefore, $s^\omega\in \overline{A}$.

3. **Alpern and Schneider’s theorem:** Alpern and Schneider’s theorem states that any property $P$ is the intersection of a safety property $P_S$ and a liveness property $P_L$ . In the following, state concretely what these properties are. (Don’t just restate the theorem, give expressions for these sets that are as simple as possible!)

   1. What are $P_S$, $P_L$ when $P$ is a safety property?

      > $P_S=P\land \Sigma^\omega$
   2. What are $P_S$, $P_L$ when $P$ is a liveness property?

      > $P_L=\Sigma^\omega$
   3. Let $\Sigma = \{a, b\}$ . That is, we assume there are only two states, $a$ and $b$ . Consider the property $P = \{\sigma|\sigma$ contains exactly one $b\}$ . What are $P_S$ and $P_L$ ?
   4. Is the empty property $\emptyset$ a liveness property? Is it a safety property? Explain.

      > $\overline{\emptyset} = \emptyset$, the set of behaviour is limit closed, it satisfies the safety property, but the $\emptyset$ is not equal $\Sigma^\omega$, therefore, the set is not dense, it does not satify liveness property.

4. **Temporal Logic**

   Define suitable predicate symbols and give LTL formalisations for the following properties (assume that there is one state per day):

   1. Once the dragon is slain, the princess will live happily ever after.

      > $\Box\ (\lnot\ \text{dragon live} \Rightarrow \bigcirc \Box\ \text{princess happy})$

   2. The dragon will never be slain, and the princess will live happily until she becomes sad.

      > $\Box\ \text{dragon live} \land (\text{princess happy }\mathcal{U}\ \lnot\text{ princess happy})$

   3. The dragon will be slain at least twice.

      > $\lozenge(\lnot\ \text{dragon live} \land \lozenge(\text{dragon live} \land \lozenge\lnot\ \text{dragon live} ))$ 

   4. The dragon will be slain at most once.

      > $\lozenge(\lnot\ \text{dragon live} \land \lnot\lozenge(\text{dragon live} \land \lozenge\lnot\ \text{dragon live} ))$

   5. On any day that the dragon is slain, the princess will be sad, but she will eventually become happy again.

      > $\Box((\lnot\ \text{dragon live} \Rightarrow \lnot\ \text{princess happy})\ \mathcal{U}\ \text{princess happy})$

5.  Prove the following logical statements:
   $$
   \begin{align*}\Box \bigcirc \varphi &\Leftrightarrow \bigcirc \Box \varphi\\
   \phi\ U\ \psi &\Leftrightarrow \psi \lor (\phi \land \bigcirc (\phi\ U\ \psi))\\
   \lozenge \lozenge \varphi &\Leftrightarrow \lozenge\varphi\end{align*}
   $$
   It may help to use these semantic definitions for $\Box$ and $\lozenge$ (derivable from the definition in terms of  $\mathcal{U}$ ):
   $$
   \begin{align*}\sigma \vDash \lozenge \varphi\quad &\text{iff}\quad \exist i \geq 0. (\sigma|_i \vDash \varphi) \\
   \sigma \vDash \Box \varphi\quad &\text{iff}\quad \forall i \geq 0. (\sigma|_i \vDash \varphi)\end{align*}
   $$
   You may use previously proven identities (both in this question and in lectures) to prove new ones.

   Note that two temporal logic formulas $\phi$ and $\varphi$ are logically equivalent, written $\phi \Leftrightarrow \varphi$ , iff for all behaviours $\sigma$ it holds that: 
   $$
   \begin{align*}
   \sigma \vDash \varphi\ \text{if and only if } \sigma \vDash \varphi
   \end{align*}
   $$
   
   > Let 
   > $$
   > \begin{align*}\sigma \vDash \lozenge \varphi\quad &\text{iff}\quad \exist i \geq 0. (\sigma|_i \vDash \varphi)\ \ (1)\\
   > \sigma \vDash \Box \varphi\quad &\text{iff}\quad \forall i \geq 0. (\sigma|_i \vDash \varphi)\ \ (2)\end{align*}
   > $$
   
   
   
   > $$
   > \sigma \vDash \Box \bigcirc \varphi\\
   > \text{iff } \forall i\geq0,\ \sigma|_{i}\vDash \bigcirc\varphi\ \text{   (According (2))}\\ 
   > \text{iff } \forall i\geq0,\ (\sigma|_{i})|_1\vDash \varphi \text{   (According } \bigcirc \text{)}\\
   > \text{iff } \forall i\geq0,\ (\sigma|_{1})|_i\vDash \varphi \text{   (According }\sigma|_i|_j=\sigma|_j|_i\text{)}\\
   > \sigma|_{1}\vDash \Box\varphi \text{   (According (2))}\\
   > \sigma \vDash \Box \bigcirc \sigma \text{   (According } \bigcirc \text{)}
   > $$
   
   
   
   > $$
   > \sigma \vDash \phi\ U\ \psi\\
   > \text{iff } \exists i\geq0\ \forall j<i, \sigma|_i\vDash\phi, \sigma|_j\vDash\psi
   > $$
   >
   > 
   
   
   
   > $$
   > \sigma \vDash \lozenge\lozenge \varphi\\
   > \text{iff } \exists i\geq0,\ \sigma|_{i}\vDash \lozenge\varphi\ \text{   (According (1))}\\ 
   > \text{iff } \exists i\geq0\ \exists j\geq0,\ (\sigma|_{i})|_j\vDash \varphi \text{   (According (1))}\\
   > \text{iff } \exists i\geq0\ \exists j\geq0,\ \sigma|_{i+j}\vDash \varphi \text{   (According }\sigma|_i|_j=\sigma|_{i+j}\text{)}\\
   > \text{iff } \exists k\geq0\ \sigma|_{k}\vDash \varphi \text{   (k=i+j)}\\
   > \sigma \vDash \lozenge\sigma \text{   (According (1))}
   > $$
   >
   > 