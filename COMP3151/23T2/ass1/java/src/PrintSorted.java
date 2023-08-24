public class PrintSorted implements Runnable {

    private final ConcurrencyDataStructure c;

    public PrintSorted(ConcurrencyDataStructure c) {
        this.c = c;
    }

    @Override
    public void run() {
        System.out.println("Prepare print");
        c.print_sort();
        System.out.println("Print finish");
    }
}
