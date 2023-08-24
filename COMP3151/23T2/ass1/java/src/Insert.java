public class Insert implements Runnable {

    private final ConcurrencyDataStructure c;
    private final int n;

    public Insert(ConcurrencyDataStructure c, int n) {
        this.c = c;
        this.n = n;
    }

    @Override
    public void run() {
        System.out.println("Prepare Insert " + n);
        c.insert(n);
        System.out.println("Insert " + n + " finish");
    }
}
