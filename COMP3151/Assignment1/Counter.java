import java.util.ArrayList;
import java.util.Arrays;

public class Counter {

    private static int R;
    private static int B;
    private static int k;

    private static volatile byte[] c;

    public static void main(String[] args) {

        try {
            if (args.length != 3) throw new Exception ("Please enter three arguments (R, B, k)! ");

            R = Integer.parseInt(args[0]);
            if (R < 1) throw new Exception("The argument R must be greater than 0!");

            B = Integer.parseInt(args[1]);
            if (B < 2) throw new Exception("The argument B must be greater than 1!");

            k = Integer.parseInt(args[2]);
            if (k < 0) throw new Exception("The argument k must be greater than or equal to 0!");
        } catch (Exception e) {
            System.err.println(e);
            System.exit(1);
        }

        c = new byte[B];

        Writer writer = new Writer();

        ArrayList<Reader> readers = new ArrayList<>();
        for (int loop = 0; loop < R; loop++) readers.add(new Reader(loop));

        writer.start();
        readers.forEach(Thread::start);
    }

    private static class Reader extends Thread {
        private final int number;
        public Reader(int number) {
            this.number = number;
        }

        @Override
        public void run() {
            for (int loopTime = 0; k == 0 || loopTime < k; loopTime++) {
                byte[] temp = new byte[B];
                System.out.println("Reader " + number + " prepare to read");
                System.arraycopy(c, 0, temp, 0, B);
                System.out.println("Reader " + number + " had read " + Arrays.toString(temp));
            }
        }
    }

    private static class Writer extends Thread {
        @Override
        public void run() {
            for (int loopTime = 0; k == 0 || loopTime < k; loopTime++) {
                byte[] temp = new byte[B];
                System.arraycopy(c, 0, temp, 0, B);

                for (int position = B - 1; position >= 0; position--) {
                    if (temp[position] != Byte.MAX_VALUE) {
                        temp[position]++;
                        break;
                    } else temp[position] = 0;
                }
                System.out.println("Writer prepare to write");
                System.arraycopy(temp, 0, c, 0, B);
                System.out.println("Writer had written " + Arrays.toString(c));
            }
        }
    }
}
