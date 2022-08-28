public class ProducerConsumer {
    public static int BUFFER_SIZE;
    public static int CAP;
    public static Semaphore3151 full;
    public static Semaphore3151 empty;
    public static int[] data;

    public static void main(String[] args) {
        try {
            BUFFER_SIZE = Integer.parseInt(args[0]);
            CAP = Integer.parseInt(args[1]);
        } catch (Exception e) {
            System.out.println("Usage: java ProducerConsumer [BUFFER_SIZE] [CAP]");
            System.exit(255);
        }
        System.out.println("Buffer size: " + BUFFER_SIZE);
        System.out.println("Total messages: " + CAP);
        full  = new StrongSemaphore(0);
        empty = new StrongSemaphore(BUFFER_SIZE);
        data = new int[BUFFER_SIZE];

        Producer prod = new Producer();
        Consumer cons = new Consumer();
        cons.start();
        prod.start();

    }

    public static class Producer extends Thread {
        private int j = 0;

        private int g(int x) {
            return 2 * x + 1;
        }

        @Override
        public void run() {
            while (j < CAP) {
                empty.P();
                int produced = g(j);
                data[j%BUFFER_SIZE] = produced;
                System.out.println("PROD: Produced " + produced);
                j++;
                full.V();
            }
            System.out.println("PROD: Terminated");
        }
    }
    public static class Consumer extends Thread {
        private int k = 0;
        private int t = 0;
        @Override
        public void run() {
            while (k < CAP) {
                full.P();
                int consumed = data[k%BUFFER_SIZE];
                System.out.println("CONS: Consumed " + consumed);
                t += consumed;
                k++;
                empty.V();
            }
            System.out.println("CONS: Terminated. Total is " + t);
        }
    }


}
