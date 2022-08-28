package temp;// Counter.java
// Authors: Michael Cunanan (z5204816), Kenvin Yu (z5207857)

import java.util.Arrays;

public class Counter {
    private static int R;
    private static int B;
    private static int k;

    // Shared
    private static volatile byte[] c; // Buffer 1 
    private static volatile byte[] d; // Buffer 2
    private static volatile int p1;   // Parity 1
    private static volatile int p2;   // Parity 2

    private static final int BYTE_MAX = 127;

    Counter() {
                
    } 

    public static void main(String[] args) {
        int i;
        
        if (args.length == 3) {
            try {  
                R = Integer.parseInt(args[0]);
                B = Integer.parseInt(args[1]);
                k = Integer.parseInt(args[2]);

                if (R <= 0) throw new NumberFormatException("R is non-positive");
                if (B <= 0) throw new NumberFormatException("B is non-positive");
                if (k < 0) throw new NumberFormatException("k is negative");
                
            } catch (NumberFormatException e) {
                System.err.println("Arguments must be non-negative integers.");
                System.exit(1);
            }
        } else {
            System.err.println("Please give 3 arguments.");
            System.exit(1);
        }

        // Initialise shared buffers and parity "bits"
        c = new byte[B];
        d = new byte[B];
        p1 = 0;
        p2 = 0;

        // Create Writer and Readers
        Writer w = new Counter().new Writer();
        Reader[] readers = new Reader[R];
        for (i = 0; i < R; i++) {
            readers[i] = new Counter().new Reader(i);
        }

        // Start Writer and Readers
        w.start();
        for (i = 0; i < R; i++) {
            readers[i].start();
        }
    }
    
    public class Writer extends Thread {
        @Override
        public void run() {
            byte[] e = new byte[B];
            int i = 0;
            int q = 0;

            for (int round = 0; k == 0 || round < k; round++) {
                q = p1;
                for (i = 0; i < B; i++) {
                    e[i] = c[i];
                }
                i = B - 1;
                while (true) {      // Faithful Promela implementation
                    if (i >= 0) {
                        if (e[i] == BYTE_MAX) {
                            if (i == 0) {
                                q = 1 - q;
                            } 
                            e[i] = 0;
                        } else {
                            e[i]++;
                            break;
                        }
                        i--;
                    } else {
                        break;
                    }
                }
                System.out.println("Writing: " + Arrays.toString(e));
                p2 = q;
                // Write into d left to right
                for (i = 0; i < B; i++) {
                    d[i] = e[i];
                }
                // Write into c right to left
                for (i = 0; i < B; i++) {
                    c[B-1-i] = e[B-1-i];
                }
                p1 = q;
                // We have now completed a `write'
                System.out.println("Wrote: " + Arrays.toString(e));
            }
        }
    }

    public class Reader extends Thread {
        private int pid;

        public Reader(int i) {
            pid = i;
        }

        
        @Override 
        public void run() {
            byte[] s = new byte[B];
            byte[] t = new byte[B];
            byte[] v = new byte[B];
            int q1;
            int q2;
            int i;

            for (int round = 0; k == 0 || round < k; round++) {
                for (i = 0; i < B; i++) {
                    v[i] = 0;
                }

                System.out.println("Reading (" + pid + ")");
                // Start reading shared memory
                q1 = p1;
                // Read into s from left to right
                for (i = 0; i < B; i++) {
                    s[i] = c[i];
                }
                // Read into t from right to left
                for (i = 0; i < B; i++) {
                    t[B-1-i] = d[B-1-i];
                }
                q2 = p2;
                // End reading shared memory

                if (q1 != q2) {
                    // Do nothing
                } else {
                    i = 0;
                    while (true) {
                        if (i < B && s[i]==t[i]) {
                            v[i] = t[i];
                            i++;
                        } else {
                            break;
                        }
                    }
                    if (i != B) {
                        v[i] = t[i];
                    }
                }

                // At this point, v is the read-in value
                System.out.println("Read (" + pid + "): " + Arrays.toString(v));
            }
        }
    }
}

