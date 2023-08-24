<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 8)</font></center>

1. **Process algebra**

   1. We saw a large number of algebraic laws of CCS in the lecture on CCS. Here are some more proposed laws. Briefly discuss the merits of each proposed law, and whether you think it should be accepted. If you think it should be accepted, give an informal intution for why; if you think not, give a concrete example where it has absurd consequences.

      - $P\ |\ P=P$

        > I think so. $|$ means parallel. Suppose $Clock = P\ |\ P$,  $Clock = P.P + P.P + P$, This is true when the starting point and the key point are the same, that is, $P$ is self-cycling.

      - $P \setminus b \setminus b=P \setminus b$

        > I think so, because $ P\ \backslash\  b$ means the action $b$ and  $\overline{b} $may not be executes in $P$,  $ P\ \backslash\  b\ \backslash\ b$ means the action $b$ and  $\overline{b} $may not be executes in $P\ \backslash\  b$, both of them have same meanings.

      - $(a.P)|(a.Q) = a.(P|Q)$

        > I think it is not. Because, $a.(P\ |\ Q)$ means that process $a$ must finish before process $P$ or $Q$, but $(a.P)\ |\ (a.Q)$ can existed that $a.P.a.Q$, which process $a$ do after $P$ or $Q$.

   2. Consider the CCS processes $P = a.\overline{b}.P$ and $Q = \overline{a}.b.Q$. Draw the labelled transition system for the process $(P|Q) \setminus a$, and justify each transition by means of a proof using the operational semantics of CCS.

      > 

2. **Ricart-Agrawala Algorithm**

   Pseudocode of the Ricart-Agrawala Algorithm is:

   <img src="/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/7_1.png" alt="7_1" style="zoom:50%;" />

   1. Suppose that we exchanged the lines $p8$ and $p9–p11$ in Main, i.e. $\texttt{requestCS} \leftarrow \texttt{false}$ now executes after the for loop (instead of executing before the for loop). Suppose furthermore that it’s possible for **Receive** to preempt **Main** at these locations. Provide an example that illustrates why the modified algorithm is no longer correct.

      > Suppose the exchanging $p8$ and $p9-p11$, when a process $p$ is finish and get out from critical section, it send message to all node N in deferred, during this period, the Receive part of $P$ check the requestCS of itself is true, and it will record the source into defer. Suppose the receiver accept the request and put them in defer, the loop may go on forever, and causing that process $P$ may not apply to enter the Critical section again.

   2. In **Receive**, can the statement $\texttt{p2: highestNum} \leftarrow \texttt{max(highestNum,requestNum)}$ be replaced by $\texttt{p2: highestNum} \leftarrow \texttt{requestNum}$? Why? Justify your answer and provide an example. 

      *In both parts of this question, you can sketch diagrams in addition to textual explanations. However, if your textual explanations are clear, such diagrams might be unnecessary.*

      > Suppose there is a request message sent to $P$ which be delay by some ways, during this time, more request which have high marks had been accepted by $P$. If the grogram only copy request number as the highestNum, it may choose a less number, and it may appear two or more request message with same requestNum which send by different process, receive part $p3$ find the requestNum is not smaller than my number, and record them, it may lead that some process cannot get reply from all node and cannot go into critical section.

3. **Token-Passing**

   Pseudocode of the Ricart-Agrawala Token-passing Algorithm is:

   <img src="/Users/enmmmmovo/Documents/Study/COMP3151/hw/material/7_2.png" alt="7_2" style="zoom:60%;" />

   1. In node $i$, can the value of $\texttt{requested}[j]$ be less than the value of $\texttt{granted}[j]$ for $j\neq i$? Why? Justify your answer.

      > Yes. Suppose a process $P$ send a message for all of the node and get the token, one of the other process $Q$ have not get the request message or message had been lost, when this process $Q$ get the token, it will appear that the request times of the $P$ is less than the granted of $P$.

   2.  In node i, can the value of $\texttt{requested}[j]$ be greater than the value of $\texttt{granted}[j]$ for $j\neq i$? Why? Justify your answer.

      > Yes. When there are more than one process $p$, $q$... which send request message, the process which had token need to choose one of it, suppose it is $p$ and send the token. During this time, the process $q$ send the second or more request and get by the process $p$ which get the token, the request times of $q$ will larger than the granted time of $p$.