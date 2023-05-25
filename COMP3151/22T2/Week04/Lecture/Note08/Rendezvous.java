import java.util.concurrent.Semaphore;

class RendezvousThread extends Thread {
    String name;

    public RendezvousThread(String name) {
        this.name = name;
    }

    public void run() {
        System.out.println(name + " first statement");
        System.out.println(name + " second statement");        
    }
}

public class Rendezvous {
    public static void main(String[] args) {
        Thread t1 = new RendezvousThread("Bertram");
        Thread t2 = new RendezvousThread("Agatha");

        t1.start();
        t2.start();
    }
}