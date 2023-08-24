import java.util.concurrent.Semaphore;

public class JavaSemaphore implements Semaphore3151 {

    private Semaphore sem;
    public JavaSemaphore(int v) {
        // we will choose a fair java semaphore
        sem = new Semaphore(v,true);
    }

    @Override
    public void P() {
        sem.acquireUninterruptibly();
    }

    @Override
    public void V() {
        sem.release();
    }
}
