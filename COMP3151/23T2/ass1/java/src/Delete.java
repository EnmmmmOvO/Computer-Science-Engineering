public class Delete implements Runnable {

    private final ConcurrencyDataStructure c;
    private final int n;

    public Delete(ConcurrencyDataStructure c, int n) {
        this.c = c;
        this.n = n;
    }

    @Override
    public void run() {
        System.out.println("Prepare Delete " + n);
        c.delete(n);
        System.out.println("Delete" + n + " finish");
    }
}
