class CounterValue {
    /* 1. Volatile in C, and volatile in Java, are completely different

       In C: volatile is a way to tell the compiler that
             reads and writes to this variable
             shouldn't be optimised away.

       In Java: makes sure reads and writes to this variable are
                sequentially consistent.

       Reads/writes are *sequentially consistent* if the way they
       behave are consistent with atomic reads and writes.
       In other words: the concurrency model we've used
         has assumed that as soon as I write,
         the results become immediately observable to everybody.

       |----------------|-------------|
       | int x,y = 0;                 |
       |----------------|-------------|
       | x := 1         | y := 1      |
       | int z := y     | int a := x  |
       --------------------------------

      Q: What are the possible final values of (a,z) now?
       Can we get (1,1)?
       - Yes, if they both execute in lockstep.
       How about (0,1) or (1,0)?
       - Yes, if one process finishes before the other starts
       How about (0,0)?
       - With atomic writes, no.
       - Under *weak memory models*, yes.
         W/ low-level concurrent programming on modern multicore
          archs, you sometimes can observe results
          that don't arise from any interleaving of our reads
          and writes.
     */    
    private volatile int count;

    public CounterValue() {
        count = 0;
    }

    public void increment() {
        count++;
    }

    public int read() {
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
            // here, responsibility for synching access to the resource
            // belongs to the threads
            // or in other words: responsibility is diffused throughout
            // possibly the whole program

            // wait on semaphore here
            c.increment();
            // signals on a semaphore here
        }
    }
}

public class Counter {

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