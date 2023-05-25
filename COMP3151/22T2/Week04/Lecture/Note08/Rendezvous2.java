import java.util.concurrent.Semaphore;

class RendezvousThread extends Thread {
    String name;
    Semaphore s1;
    Semaphore s2;

    public RendezvousThread(String name, Semaphore s1, Semaphore s2) {
        this.name = name;
        this.s1 = s1;
        this.s2 = s2;
    }

    public void run() {
        System.out.println(name + " first statement");
        // here, we want to: unblock the other proc
        // wait until the other proc unblocks us
        s1.release();
        s2.acquireUninterruptibly();
        System.out.println(name + " second statement");        
    }
}

public class Rendezvous2 {
    public static void main(String[] args) {
        Semaphore s1 = new Semaphore(0);
        Semaphore s2 = new Semaphore(0);
        Thread t1 = new RendezvousThread("Bertram",s1,s2);
        Thread t2 = new RendezvousThread("Agatha",s2,s1);

        t1.start(); // start means
                    // execute run() in a new thread
        t2.start();
    }
}