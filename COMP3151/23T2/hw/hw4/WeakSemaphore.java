public class WeakSemaphore implements Semaphore3151 {

    //TODO: Add private state here as needed
    private int counter;

    public WeakSemaphore(int v) {
        //TODO: implement
        this.counter = v;
    }
    @Override
    public synchronized void P() {
        //TODO: Used synchronized methods and the Java wait() method to add the process to the waiting set.
        while (this.counter == 0) {
            try {
                wait();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        this.counter--;
    }

    @Override
    public synchronized void V() {
        //TODO: Use the Java notify() method to awaken a waiting process.
        this.counter++;
        notify();
    }

}
