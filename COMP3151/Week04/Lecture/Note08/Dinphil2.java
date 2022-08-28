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

public class Dinphil2 {
    public static void main(String[] args) {
        // we want binary semaphores that have 1 free ticket initially
        // we don't care about liveness here, only deadlock
        Semaphore fork1 = new Semaphore(1,false);
        Semaphore fork2 = new Semaphore(1,false);
        Semaphore fork3 = new Semaphore(1,false);
        // fork1 < fork2 < fork3
        Thread t1 = new Philosopher("Hegel",fork1,fork2);
        Thread t2 = new Philosopher("Plato",fork2,fork3);
        Thread t3 = new Philosopher("Averroes",fork1,fork3);

        t1.start();
        t2.start();
        t3.start();                
    }
}
