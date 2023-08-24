<center><font size=6pt>COMP3151/9154 23T2 Homework (Week 4)</font></center>

1. In the Promela code under Week 3 on Moodle, you will find Szymanski’s algorithm for three processes, broken down to satisfy LCR, with a particular choice of test order for the various await statements. This choice happens to satisfy mutual exclusion and eventual entry (as you may check in Spin), but as mentioned in the lectures, not all choices do. The task here is to twiddle with the test orders and figure out which orderings break the algorithm and which don’t. You don’t need to test all permutations, but do answer these questions: Can you find any reorderings that break mutual exclusion and/or eventual entry? (You should be able to find at least one). Are there any awaits that don’t seem sensitive to reordering at all? What if you reorder the tests for all the awaits in the exact same way? And finally, based on any error trails you obtain, can you form an educated guess about *why* the test order matters?

   Explain your findings, informally and in your own words.

   > $$
   > \begin{align*}\Large \text{Szymanski's algorithm}\end{align*}
   > $$
   >
   > ---
   >
   > $$
   > \begin{align*}
   > & \ \ \ \ \ \ \ \text{forever do}\\
   > &p1:\ \ \ \ \textit{non-critical section}\\
   > &p2:\ \ \ \ \text{flag}[i]\leftarrow 1\\
   > &p3:\ \ \ \ \text{await }\forall j. \text{flag}[j] <3\\
   > &p4:\ \ \ \ \text{flag}[i]\leftarrow3\\
   > &p5:\ \ \ \ \text{if } \exists j.\ \text{flag}[j] =1\ \text{then}\\
   > &p6:\ \ \ \ \ \ \ \ \text{flag}[i]\leftarrow 2\\
   > &p7:\ \ \ \ \ \ \ \ \text{await }\exists j.\ \text{flag}[j] =4\\
   > &p8:\ \ \ \ \text{flag}[i]\leftarrow 4\\
   > &p9:\ \ \ \ \text{await }\forall j<i. \text{flag}[j] <2\\
   > &p10:\ \ \textit{critical section}\\
   > &p11:\ \ \text{await }\forall j>i. \text{flag}[j] <2\ \text{or flag}[j] > 3\\
   > &p12:\ \ \text{flag}[i]\leftarrow0\\
   > \end{align*}
   > $$
   >
   > ---
   >
   > 
   >
   > #### Changing the order can lead to errors
   >
   > ```c
   > /* p3: Await FORALL j. flag[j] < 3 */
   > 
   > flag[2] < 3;
   > flag[1] < 3;
   > flag[0] < 3;
   > ```
   >
   > |           proc0            |           proc1            |               proc2               | flag[0] | flag[1] | flag[2] |  cs  |
   > | :------------------------: | :------------------------: | :-------------------------------: | :-----: | :-----: | :-----: | :--: |
   > |      p2: flag[i] ← 1       |                            |          p2: flag[i] ← 1          |    1    |    0    |    0    |  0   |
   > |                            |                            | p3: flag[2]<3 flag[1]<3 flag[0]<3 |    1    |    0    |    1    |  0   |
   > |                            |                            |          p4: flag[i] ← 3          |    1    |    0    |    3    |  0   |
   > |                            |                            |      p5: Exists flag[i] = 1       |    1    |    0    |    3    |  0   |
   > |      p4: flag[i] ← 3       |                            |          p6: flag[i] ← 2          |    3    |    0    |    2    |  0   |
   > | p5: Not exists flag[i] = 1 |                            |                                   |    3    |    0    |    2    |  0   |
   > |      p8: flag[i] ← 4       |      p2: flag[i] ← 1       |                                   |    4    |    1    |    2    |  0   |
   > |          p9: Pass          |  p3: flag[2]<3 flag[1]<3   |      p7: Exists flag[i] = 4       |    4    |    1    |    2    |  0   |
   > |       p10: Enter CS        |             …              |          p8: flag[i] ← 4          |    4    |    1    |    4    |  1   |
   > |  P11: flag[1]<2 flag[2]>3  |             …              |                                   |    4    |    1    |    4    |  1   |
   > | p10: flag[i] ← 0, Exit CS  |             …              |                                   |    0    |    1    |    4    |  0   |
   > |                            |       p3: flag[0]<3        |                                   |    0    |    1    |    4    |  0   |
   > |                            |                            |      p9: flag[0]<2 flag[1]<2      |    0    |    1    |    4    |  0   |
   > |                            |      p4: flag[i] ← 3       |           p10: Enter CS           |    0    |    3    |    4    |  1   |
   > |                            | p5: Not exists flag[i] = 1 |                                   |    0    |    3    |    4    |  1   |
   > |                            |      p8: flag[i] ← 4       |                                   |    0    |    4    |    4    |  1   |
   > |                            |       p9: flag[0]<2        |                                   |    0    |    4    |    4    |  1   |
   > |                            |       p10: Enter CS        |                                   |    0    |    4    |    4    |  2   |
   >
   > The order of the await conditions in Szymanski's algorithm is crucial because reading the flag array is not atomic. Consequently, the order of reading can affect the behavior of the algorithm.
   >
   > As the index increases, each process faces more constraints. To put it another way, each process can control the subsequent ones to maintain order. The state of a preceding process can control the following processes. When a preceding process is in the waiting state (states 3 or 4), the following processes are prevented from entering. In particular, when flag=4, no more processes will be allowed to enter the waiting section, and all subsequent ones in the waiting section are guaranteed to enter the critical section regardless of their status (whether it's 2, 3, or 4).
   >
   > In the example where the state is [4,1,2], the action of process 0 will prevent process 1, which comes after process 0, from entering the waiting state. Process 1 must wait until the critical section is completed, while process 0 also ensures that process 2, which has already entered the waiting state, can complete its execution. The process in the preceding order not only ensures that processes not in the waiting state cannot enter until they are ready to enter the critical section, but also ensures that all subsequent processes in the waiting state are flagged to 4 to block processes not in the waiting state from entering the waiting state.
   >
   > If the order is changed, it would allow process 1 to enter the waiting state prematurely. This could lead to multiple processes simultaneously entering the critical section, thereby violating mutual exclusion.
   >
   > #### Change the order does not affect the results
   >
   > ```		c
   > /* p5: if EXISTS j. flag[2] = 1 */     
   > 
   > b = 0;
   > b = b || (flag[2] == 1);
   > b = b || (flag[1] == 1);
   > b = b || (flag[0] == 1);
   > ```
   >
   > ```c
   > /* p7: Await EXISTS j. flag[j] = 4 */
   > 
   > do
   > :: b = 0;
   >    b = b || (flag[2] == 4);
   >    b = b || (flag[1] == 4);
   >    b = b || (flag[0] == 4);
   >    if
   >    :: b -> break;
   >    :: else -> skip;
   >    fi;
   > od;
   > ```
   >
   > The two conditions above are exists judgments. Since the `do` and `if` operations in SPIN are chosen randomly, changing the order will not affect the result.
   >
   > 
   >
   > ```c
   > /* p9: Await FORALL j<i. flag[j] < 2*/
   > 
   > /* P4 */
   > flag[3] < 2;
   > flag[2] < 2;
   > flag[1] < 2;
   > flag[0] < 2;
   > 
   > /* P3 */
   > flag[2] < 2;
   > flag[1] < 2;
   > flag[0] < 2;
   > 
   > /* P2 */
   > flag[1] < 2;
   > flag[0] < 2;
   > 
   > /* P1 */
   > flag[0] < 2;
   > ```
   >
   > ```c
   > /* p11: await FORALL j>i. flag[j] < 2 or flag[j] > 3*/
   > 
   > 
   > /* P0 */
   > flag[4] < 2 || flag[4] > 3;
   > flag[3] < 2 || flag[3] > 3;
   > flag[2] < 2 || flag[2] > 3;
   > flag[1] < 2 || flag[1] > 3;
   > 
   > /* P1 */
   > flag[4] < 2 || flag[4] > 3;
   > flag[3] < 2 || flag[3] > 3;
   > flag[2] < 2 || flag[2] > 3;
   > 
   > /* P2 */
   > flag[4] < 2 || flag[4] > 3;
   > flag[3] < 2 || flag[3] > 3;
   > 
   > /* P3 */
   > flag[4] < 2 || flag[4] > 3;
   > ```
   >
   > To avoid the potential issue of having too few processes, I increased the count to five. This adjustment appears not to produce any errors. 
   >
   > - When checking in preorder, changing the order simply means that the program checks the status of the nearest preceding process in the waiting section first. It cannot enter if the preceding one is blocked, but it does satisfy the condition that it can only enter after all processes in the waiting section that come before it in the sequence have exited the critical section.
   > - For subsequent checks, since the first program to enter the critical section must wait until all subsequent programs have changed their status to 4 before it can exit, no errors are generated.

   

2. **Cigarette Smokers Problem:** Three smokers are rolling their own cigarettes and smoking them. In order to do so, they need three resources: paper, tobacco, and matches. Each smoker has their own limitless supply of one of the three ingredients. For the other two ingredients, they must acquire them from an emphAgent. They can ask for an *Agent* to distribute 1 resources to them by signalling on the *agent* semaphore. One of the *Agent* threads will then awaken, and produce two of the three different resources by signalling on two of the three semaphores *tobacco*, *paper* and *match*. Note that the smoker has no control over which *Agent* thread awakens and which resources are produced. 

   The existing code where smokers get resources directly from the agents is highly vulnerable to a deadlock scenario. In this exercise, we will implement a solution to this problem that ensures progress by introducing a ”middle-man” between the agents and smokers. 

   - Step One :: Introduce a dedicated semaphore for each smoker, and the smoker will just wait on that semaphore, smoke a cigarette, and signal an agent forever. 

   - Step Two :: Add a thread called a pusher for each of the three resources. The *pusher* will perpetually: 

     1.  Wait for its resource to become available. 

     2. Update some shared state (shared with the other pushers) regarding what resources are available. 

     3. If two of the three resources are available, update the shared state to remove those resources, and signal the smoker that requires those two resources, to indicate that they may smoke the cigarette. 

        Caution :: You must make the loop body of the pusher a critical section - mutual exclusion is required when accessing the shared state. You can accomplish this by adding another semaphore for the pushers to use.

   > ```java
   > public class CigaretteSmokers {
   >     static Semaphore3151 agent = new JavaSemaphore(1);
   >     static Semaphore3151 tobacco = new JavaSemaphore(0);
   >     static Semaphore3151 paper = new JavaSemaphore(0);
   >     static Semaphore3151 match = new JavaSemaphore(0);
   > 	
   >   	/* TODO: Add more semaphores and shared variables here as needed */
   >     static Semaphore3151 mutex = new JavaSemaphore(1);
   >     static Semaphore3151 smokerTobacco = new JavaSemaphore(0);
   >     static Semaphore3151 smokerPaper = new JavaSemaphore(0);
   >     static Semaphore3151 smokerMatch = new JavaSemaphore(0);
   >     static boolean isTobacco = false;
   >     static boolean isPaper = false;
   >     static boolean isMatch = false;
   > 
   >     public static void main(String[] args) {
   >         AgentA a = new AgentA();
   >         AgentB b = new AgentB();
   >         AgentC c = new AgentC();
   >         SmokerA sa = new SmokerA();
   >         SmokerB sb = new SmokerB();
   >         SmokerC sc = new SmokerC();
   >         
   >       	/* TODO: Add and start more threads here as needed */
   >       	PusherTobacco pt = new PusherTobacco();
   >         PusherPaper pp = new PusherPaper();
   >         PusherMatch pm = new PusherMatch();
   >       
   >         a.start();
   >         b.start();
   >         c.start();
   >         sa.start();
   >         sb.start();
   >         sc.start(); 
   >       	pt.start();
   >         pp.start();
   >         pm.start();
   >     }
   >   
   >   	/* TODO: Add more classes here for threads as needed */
   >   	public static class PusherTobacco extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 tobacco.P();
   >                 mutex.P();
   >                 if (isPaper) {
   >                     isPaper = false;
   >                     smokerMatch.V();
   >                 } else if (isMatch) {
   >                     isMatch = false;
   >                     smokerPaper.V();
   >                 } else {
   >                     isTobacco = true;
   >                 }
   >                 mutex.V();
   >             }
   >         }
   >     }
   >     
   >     public static class PusherPaper extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 paper.P();
   >                 mutex.P();
   >                 if (isTobacco) {
   >                     isTobacco = false;
   >                     smokerMatch.V();
   >                 } else if (isMatch) {
   >                     isMatch = false;
   >                     smokerTobacco.V();
   >                 } else {
   >                     isPaper = true;
   >                 }
   >                 mutex.V();
   >             }
   >         }
   >     }
   >    
   >      public static class PusherMatch extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 match.P();
   >                 mutex.P();
   >                 if (isTobacco) {
   >                     isTobacco = false;
   >                     smokerPaper.V();
   >                 } else if (isPaper) {
   >                     isPaper = false;
   >                     smokerTobacco.V();
   >                 } else {
   >                     isMatch = true;
   >                 }
   >                 mutex.V();
   >             }
   >         }
   >     }
   >    
   >  // Smoker with Tobacco
   >     public static class SmokerA extends Thread {
   >         private void smoke() {
   >             System.out.println("SMOKEA: Got a paper and matches. Puff Puff.");
   >         }
   >    
   >      @Override
   >         public void run() {
   >             while (true) {
   >                 smokerTobacco.P();
   >                 smoke();
   >                 agent.V();
   >             }
   >         }
   >     }
   >    
   >  // Smoker with Paper
   >     public static class SmokerB extends Thread {
   >         private void smoke() {
   >             System.out.println("SMOKEB: Got tobacco and matches. Puff Puff.");
   >         }
   >    
   >      @Override
   >         public void run() {
   >             while (true) {
   >                 smokerPaper.P();
   >                 smoke();
   >                 agent.V();
   >             }
   >         }
   >     }
   >    
   >  // Smoker with Matches
   >     public static class SmokerC extends Thread {
   >         private void smoke() {
   >             System.out.println("SMOKEC: Got tobacco and paper. Puff Puff.");
   >         }
   >    
   >      @Override
   >         public void run() {
   >             while (true) {
   >                 smokerMatch.P();
   >                 smoke();
   >                 agent.V();
   >             }
   >         }
   >     }
   >    
   >  /* Do not change anything below this line */
   >     public static class AgentA extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 agent.P();
   >                 System.out.println("AGENTA: Supplying tobacco and paper");
   >                 tobacco.V();
   >                 paper.V();
   >             }
   >         }
   >     }
   >    
   >  public static class AgentB extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 agent.P();
   >                 System.out.println("AGENTB: Supplying paper and match");
   >                 paper.V();
   >                 match.V();
   >             }
   >         }
   >     }
   >    
   >  public static class AgentC extends Thread {
   >         @Override
   >         public void run() {
   >             while (true) {
   >                 agent.P();
   >                 System.out.println("AGENTC: Supplying tobacco and match");
   >                 tobacco.V();
   >                 match.V();
   >             }
   >         }
   >     }
   >    }
   > 
   > ```
   
   
   
3. **Semaphores with Monitors** 

   In the *ProducerConsumer* module you will find an implementation of the Producer-Consumer problem we analysed in class. This (and the Cigarette Smokers example from earlier) use a semaphore class called *JavaSemaphore* that wraps around Java’s built-in semaphores. We have two other classes, *BusyWaitSemaphore* and *WeakSemaphore*, without implementations added. 

   - Step One :: Using *only* Java’s built-in concurrency primitives, specifically *synchronized* blocks/methods and *Thread.yield()*, implement a busy-wait semaphore in BusyWaitSemaphore. You can test it using *ProducerConsumer* or *CigaretteSmokers*. 
   - Step Two :: Using *only* Java’s built-in concurrency primitives and monitor-like constructs, specifically *synchronized* blocks, *Object.wait()* and *Object.notify()*, implement a weak semaphore in *WeakSemaphore*. You can test it using the same examples. 
   - Using *only* Java’s built-in concurrency primitives and monitor-like constructs, as well as an *ArrayDeque* of *Object*, implement a strong semaphore in *StrongSemaphore*. You may use *Object.notifyAll()* so long as the first process to /leave/ its await is the first process in the queue.

   > - *Busy-Wait Semaphore*
   >
   >   ```java
   >   public class BusyWaitSemaphore implements Semaphore3151 {
   >     
   >       //TODO: add private state here as needed
   >       private int counter;
   >     
   >       public BusyWaitSemaphore(int v) {
   >           //TODO: Implement
   >           this.counter = v;
   >       }
   >     
   >       @Override
   >       public void P() {
   >           //TODO: Use Java's weak waiting here here, but also add an identifier to the queue
   >           //TODO: All processes on waking should check if they are first in the queue.
   >           while (true) {
   >               synchronized (this) {
   >                   if (counter > 0) {
   >                       counter--;
   >                       return;
   >                   }
   >               }
   >               Thread.yield();
   >           }
   >       }
   >     
   >       @Override
   >       public synchronized void V() {
   >           //TODO: synchronized method or blocks can be used here to do the increment in one step.
   >           counter++;
   >       }
   >   }
   >     
   >   ```
   >
   > 
   >
   > - *Weak Semaphore*
   >
   >   ```java
   >   public class Semaphore implements Semaphore3151 {
   >     
   >       //TODO: Add private state here as needed
   >       private int counter;
   >     
   >       public WeakSemaphore(int v) {
   >           //TODO: implement
   >           this.counter = v;
   >       }
   >       @Override
   >       public synchronized void P() {
   >           //TODO: Used synchronized methods and the Java wait() method to add the process to the waiting set.
   >           while (this.counter == 0) {
   >               try {
   >                   wait();
   >               } catch (InterruptedException e) {
   >                   Thread.currentThread().interrupt();
   >               }
   >           }
   >           this.counter--;
   >       }
   >     
   >       @Override
   >       public synchronized void V() {
   >           //TODO: Use the Java notify() method to awaken a waiting process.
   >           this.counter++;
   >           notify();
   >       }
   >     
   >   }
   >     
   >   ```
   >
   >   
   >
   > - *Strong Semaphore*
   >
   >   ```java
   >   import java.util.ArrayDeque;
   >   import java.util.Queue;
   >     
   >   public class StrongSemaphore implements Semaphore3151 {
   >     
   >       //TODO: Private state (presumably a Queue goes here)
   >       private int counter;
   >       private final Queue<Object> waitingThreads;
   >     
   >       public StrongSemaphore(int v) {
   >           //TODO: Implement
   >           this.counter = v;
   >           this.waitingThreads = new ArrayDeque<>();
   >       }
   >     
   >       @Override
   >       public synchronized void P() {
   >           //TODO: Use Java's weak waiting here here, but also add an identifier to the queue
   >           //TODO: All processes on waking should check if they are first in the queue.
   >           waitingThreads.add(Thread.currentThread());
   >           while (counter == 0 || waitingThreads.peek() != Thread.currentThread()) {
   >               try {
   >                   this.wait();
   >               } catch (InterruptedException e) {
   >                   Thread.currentThread().interrupt();
   >               }
   >           }
   >           waitingThreads.poll();
   >           counter--;
   >       }
   >     
   >       @Override
   >       public synchronized void V() {
   >           //TODO: Use Java's notifyAll() method to awaken all processes, but be sure to
   >           //TODO: make sure that all but the first process in the queue go back to sleep.
   >           counter++;
   >           this.notifyAll();
   >       }
   >   }
   >     
   >   ```



