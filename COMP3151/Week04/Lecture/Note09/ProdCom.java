/* A monitor for managing the buffer */
/* A fake buffer: we're only going to track
   whether it's full or not, and not put 
   anything in it.
 */
class Buffer {
    private int max_size;
    private volatile int current_size;

    public Buffer(int max_size) {
        this.max_size = max_size;
        this.current_size = 0;
    }

    public synchronized void enqueue() {
        /* The queue might be full.
           If so, we wait.
         */
        while(max_size == current_size) {
            // wait is "wait on a condition variable"
            // every Object in java implicitly has
            // exactly one condition variable.
            try {
                wait();
            }
            catch(InterruptedException e) {}
            // when we're here, we don't know if
            // the condition we were waiting
            // is *still* true
        }
        /* here, we really do know that max_size != current_size */
        current_size++;
        notifyAll();        
    }

    public synchronized void dequeue() {
        while(current_size == 0) {
            try {
                wait();
            }
            catch(InterruptedException e) {}
        }
        current_size--;
        notifyAll();        
    }
}

class Consumer extends Thread {
    Buffer b;

    public Consumer(Buffer b) {
        this.b = b;
    }

    public void run() {
        while(true) {
            b.enqueue();
            System.out.println("Thread #" + getId() + " enqueued a thing!");
        }
    }
}

class Producer extends Thread {
    Buffer b;

    public Producer(Buffer b) {
        this.b = b;
    }

    public void run() {
        while(true) {
            b.dequeue();
            System.out.println("Thread #" + getId() + " dequeued a thing!");
        }
    }
}

public class ProdCom {
    public static void main(String[] args) {
        Buffer b = new Buffer(1);
        Thread t1 = new Producer(b);
        Thread t2 = new Producer(b);
        Thread t3 = new Consumer(b);
        Thread t4 = new Consumer(b);
        t1.start();
        t2.start();
        t3.start();
        t4.start();
    }
}