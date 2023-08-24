public class BusyWaitSemaphore implements Semaphore3151 {

    //TODO: add private state here as needed
    private int counter;

    public BusyWaitSemaphore(int v) {
        //TODO: Implement
        this.counter = v;
    }

    @Override
    public void P() {
        //TODO: Use Java's weak waiting here here, but also add an identifier to the queue
        //TODO: All processes on waking should check if they are first in the queue.
        while (true) {
            synchronized (this) {
                if (counter > 0) {
                    counter--;
                    return;
                }
            }
            Thread.yield();
        }
    }

    @Override
    public synchronized void V() {
        //TODO: synchronized method or blocks can be used here to do the increment in one step.
        counter++;
    }
}
