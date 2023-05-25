import java.util.concurrent.Semaphore;

class Philosopher extends Thread {
    String name;
    Semaphore left_fork;
    Semaphore right_fork;

    Philosopher(String name, Semaphore left_fork, Semaphore right_fork) {
        this.name = name;
        this.left_fork = left_fork;
        this.right_fork = right_fork;        
    }

    public void run () {
        while(true) {
            System.out.println(name + " thinks...");
            try {
                Thread.sleep(150);
            }
            catch(InterruptedException e) {
            }

            left_fork.acquireUninterruptibly();
            System.out.println(name + " grabbed a fork...");
            try {
                Thread.sleep(150);
            }
            catch(InterruptedException e) {
            }
            right_fork.acquireUninterruptibly();
            System.out.println(name + " grabbed another fork...");            
            System.out.println(name + " eating...");
            try {
                Thread.sleep(150);
            }
            catch(InterruptedException e) {
            }
            System.out.println(name + " releases forks...");
            left_fork.release();
            right_fork.release();
        }
    }
}

public class Dinphil {
    public static void main(String[] args) {
        // we want binary semaphores that have 1 free ticket initially
        // we don't care about liveness here, only deadlock
        Semaphore fork1 = new Semaphore(1,false);
        Semaphore fork2 = new Semaphore(1,false);
        Semaphore fork3 = new Semaphore(1,false);                
        Thread t1 = new Philosopher("Hegel",fork1,fork2);
        Thread t2 = new Philosopher("Plato",fork2,fork3);
        Thread t3 = new Philosopher("Averroes",fork3,fork1);

        t1.start();
        t2.start();
        t3.start();                
    }
}

/* We're deadlocked :(
   Suggestion:
   - make "grab both forks" a critical section
     with another semaphore, shared between
     everybody
   - ordering the forks
     In the system as a whole, we'll have
         n   locks  (or semaphores)
     each process requires some subset of the
     locks

     Globally order all the locks
     Total order:
        fork1 < fork2 < fork3
     Enforce discipline:
        everybody needs to claim the "smallest"
        lock first

     If everybody claims locks in an order
     consistent w/ the total order,
     deadlock is impossible.

     If P is stuck, that means somebody is
     hogging a higher lock.
     But the process hogging the *highest* lock
     can't be stuck.
 */