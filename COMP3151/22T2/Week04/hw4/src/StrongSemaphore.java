public class StrongSemaphore implements Semaphore3151 {

    //TODO: Private state (presumably a Queue goes here)
    public StrongSemaphore(int v) {
        //TODO: Implement
    }
    @Override
    public synchronized void P() {
        //TODO: Use Java's weak waiting here here, but also add an identifier to the queue
        //TODO: All processes on waking should check if they are first in the queue.
    }

    @Override
    public synchronized void V() {
        //TODO: Use Java's notifyAll() method to awaken all processes, but be sure to
        //TODO: make sure that all but the first process in the queue go back to sleep.
    }
}
