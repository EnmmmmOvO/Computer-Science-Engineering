import java.util.concurrent.Semaphore;

class RendezvousThread extends Thread {
    String name;
    Semaphore s1;

    public RendezvousThread(String name, Semaphore s1) {
        this.name = name;
        this.s1 = s1;
    }

    public void run() {
        System.out.println(name + " first statement");
        // here, we want to: unblock the other proc
        // wait until the other proc unblocks us
        s1.release();
        s1.acquireUninterruptibly();
        System.out.println(name + " second statement");
        s1.release();
    }
}

public class Rendezvous3 {
    public static void main(String[] args) {
        Semaphore s1 = new Semaphore(-1);
        Thread t1 = new RendezvousThread("Bertram",s1);
        Thread t2 = new RendezvousThread("Agatha",s1);

        t1.start(); // start means
                    // execute run() in a new thread
        t2.start();
    }
}
