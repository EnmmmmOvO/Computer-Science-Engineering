public class Member implements Runnable {

    private final ConcurrencyDataStructure c;
    private final int n;

    public Member(ConcurrencyDataStructure c, int n) {
        this.c = c;
        this.n = n;
    }

    @Override
    public void run() {
        System.out.println("Prepare find member " + n);
        boolean test = c.member(n);
        if (test) System.out.println("Find member " + n + " finish : find");
        else System.out.println("Find member " + n + " finish : not find");
    }
}
