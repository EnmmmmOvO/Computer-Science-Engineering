import java.util.*;
import java.util.concurrent.*;


public class SzymanskiAlgorithm {
    public static void main(String[] args) throws Exception {
        Thread t1 = new monitor(10);
        t1.start();
    }
}


class monitor extends Thread {
    final int size;    // Record the number of process
    volatile int[] flag;    // Record the states for each process
    Semaphore changeFlagOrStatus;    // At the same time, only one process can get the semaphore which also means that
                                     // only one process can loop forward or change the flag;

    public monitor(int size) {
        this.size = size;
        flag = new int[size];
        changeFlagOrStatus = new Semaphore(1);
    }

    @Override
    public void run() {
        ArrayList<thread> list = new ArrayList<>();
        for (int loop = 0; loop < size; loop++) list.add(new thread(loop, this));
        list.forEach(Thread::start);
    }
}


class thread extends Thread {
    private final int index;
    final monitor recordMonitor;


    public thread(int index, monitor recordMonitor) {
        this.index = index;
        this.recordMonitor = recordMonitor;
    }

    private void changeFlag(int i) {
        recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
        recordMonitor.flag[index] = i;
        //System.out.println("***** I am thread " + index + ", I change the flag[" + index + "] to " + i + " *****");
        try { notifyAll(); } catch (Exception e) {}
        recordMonitor.changeFlagOrStatus.release();
    }

    private void sleep(int time) {
        try {
            Thread.sleep((int) (Math.random() * time));
        } catch (Exception e) {
            System.err.println("I am thead " + index + ": " + e);
        }
    }


    @Override
    public void run() {
        while (true) {
            sleep(1000);

            changeFlag(1);

            while (true) {
                recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
                if (Arrays.stream(recordMonitor.flag).allMatch(value -> value < 3)) break;
                recordMonitor.changeFlagOrStatus.release();
                try { wait(); } catch (Exception e) {}
            }
            recordMonitor.changeFlagOrStatus.release();

            changeFlag(3);

            recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
            if (Arrays.stream(recordMonitor.flag).anyMatch(value -> value == 1)) {
                recordMonitor.changeFlagOrStatus.release();

                changeFlag(2);
                try { wait(); } catch (Exception e) {}
                while (true) {
                    recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
                    if (Arrays.stream(recordMonitor.flag).anyMatch(value -> value == 4)) break;
                    recordMonitor.changeFlagOrStatus.release();
                    try { wait(); } catch (Exception e) {}
                }
            }
            recordMonitor.changeFlagOrStatus.release();
            sleep(1000);
            changeFlag(4);

            while (true) {
                recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
                boolean check = true;
                for (int loop = 0; loop < index; loop++) {
                    if (recordMonitor.flag[loop] >= 2) {
                        check = false;
                        break;
                    }
                }
                if (check) break;
                recordMonitor.changeFlagOrStatus.release();
                try { wait(); } catch (Exception e) {}
            }
            recordMonitor.changeFlagOrStatus.release();


            System.out.println("----------------------------------------------------------");
            System.out.println("I am thead " + index + ", I prepare entering critical section");
            System.out.println("I am thead " + index + ", I am in critical section");
            System.out.print("Now these thread will have right into critical section\n[ ");
            recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
            for (int loop = 0; loop < recordMonitor.size; loop++) {
                if (loop == index) continue;
                if (recordMonitor.flag[loop] >= 2) System.out.print(loop + "(" +
                        recordMonitor.flag[loop] + ") ");
            }
            recordMonitor.changeFlagOrStatus.release();
            System.out.println("]");
            System.out.println("I am thead " + index + ", I exit critical section");
            System.out.println("----------------------------------------------------------");

            while (true) {
                recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
                boolean check = true;
                for (int loop = index + 1; loop < recordMonitor.size; loop++) {
                    if (recordMonitor.flag[loop] == 2 || recordMonitor.flag[loop] == 3) {
                        check = false;
                        break;
                    }
                }
                if (check) break;
                recordMonitor.changeFlagOrStatus.release();
                try { wait(); } catch (Exception e) {}
            }
            recordMonitor.changeFlagOrStatus.release();

            System.out.println("----------------------------------------------------------");
            System.out.print("I am thead " + index + ", I had go into non-critical section\n[");
            recordMonitor.changeFlagOrStatus.acquireUninterruptibly();
            for (int loop = 0; loop < recordMonitor.size; loop++) {
                if (loop == index) continue;
                if (recordMonitor.flag[loop] >= 2) System.out.print(loop + "(" +
                        recordMonitor.flag[loop] + ") ");
            }
            recordMonitor.changeFlagOrStatus.release();
            System.out.println("]");
            System.out.println("----------------------------------------------------------");

            changeFlag(0);
        }
    }

}