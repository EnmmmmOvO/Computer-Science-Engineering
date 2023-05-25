class CounterValue {
    private volatile int count;

    public CounterValue() {
        count = 0;
    }

    /* A *synchronized* method
        can only have one process at a time in it.
       I.e., it's implicitly protected by a lock.
       For each object, the synchronized methods
       use the same lock.
     */
    public synchronized void increment() {
        count++;
    }

    // In this case, synching on read is pointless
    public synchronized int read() {
        return count;
    }
}

class CounterThread extends Thread {

    private CounterValue c;

    public CounterThread(CounterValue c) {
        this.c = c;
    }

    public void run() {
        for(int i = 0; i < 5000; i++) {
            c.increment();
        }
    }
}

public class Counter2 {

    public static void main(String [] main) throws InterruptedException {
        CounterValue c = new CounterValue();
        Thread t1 = new CounterThread(c);
        Thread t2 = new CounterThread(c);

        t1.start();
        t2.start();

        t1.join(); // wait until t1 is finished
        t2.join();
        System.out.println("Final counter value is " + c.read());
    }

}