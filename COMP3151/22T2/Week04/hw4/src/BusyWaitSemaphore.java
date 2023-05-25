public class BusyWaitSemaphore implements Semaphore3151 {

    //TODO: add private state here as needed
    public BusyWaitSemaphore(int v) {
        //TODO: Implement
    }
    @Override
    public void P() {

        //TODO: synchronized blocks can be used to do the comparison and decrement in one step.
        //TODO: Thread.yield() should be called in the busy wait

    }

    @Override
    public void V() {
        //TODO: synchronized method or blocks can be used here to do the increment in one step.
    }
}
