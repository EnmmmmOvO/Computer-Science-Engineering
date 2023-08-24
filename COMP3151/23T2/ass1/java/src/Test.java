public class Test {
    public static void TestInsert() {
        int N = 5;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);
        Thread[] threads = new Thread[N];
        for (int i = 0; i < N; i++) threads[i] = new Thread(new Insert(c, i));
        for (int i = 0; i < N; i++) threads[i].start();

        for (int i = 0; i < N; i++) {
            try {
                threads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        c.print_sort();
    }

    public static void TestDeleteEmpty() {
        int N = 6;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);
        Thread[] threads = new Thread[N];
        for (int i = 0; i < N; i++) threads[i] = new Thread(new Delete(c, i));
        for (int i = 0; i < N; i++) threads[i].start();

        for (int i = 0; i < N; i++) {
            try {
                threads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        c.print_sort();
    }

    public static void TestMemberEmpty() {
        int N = 7;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);
        Thread[] threads = new Thread[N];
        for (int i = 0; i < N; i++) threads[i] = new Thread(new Member(c, i));
        for (int i = 0; i < N; i++) threads[i].start();

        for (int i = 0; i < N; i++) {
            try {
                threads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        c.print_sort();
    }

    public static void TestInsertDelete() {
        int N = 8;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);
        Thread[] insertThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            insertThreads[i] = new Thread(new Insert(c, i));
        }
        for (int i = 0; i < N; i++) {
            insertThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                insertThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread[] deleteThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            deleteThreads[i] = new Thread(new Delete(c, i));
        }
        for (int i = 0; i < N; i++) {
            deleteThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                deleteThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        c.print_sort();
    }

    public static void TestInsertDeleteMember() {
        int N = 9;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);

        Thread[] insertThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            insertThreads[i] = new Thread(new Insert(c, i));
        }
        for (int i = 0; i < N; i++) {
            insertThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                insertThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread[] memberThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            memberThreads[i] = new Thread(new Member(c, i));
        }
        for (int i = 0; i < N; i++) {
            memberThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                memberThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread[] deleteThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            deleteThreads[i] = new Thread(new Delete(c, i));
        }
        for (int i = 0; i < N; i++) {
            deleteThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                deleteThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        c.print_sort();
    }

    public static void TestInsertDeleteMemberPrintSorted() {
        int N = 10;

        ConcurrencyDataStructure c = new ConcurrencyDataStructure(N);

        Thread[] insertThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            insertThreads[i] = new Thread(new Insert(c, i));
        }
        for (int i = 0; i < N; i++) {
            insertThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                insertThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread[] memberThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            memberThreads[i] = new Thread(new Member(c, i));
        }
        for (int i = 0; i < N; i++) {
            memberThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                memberThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread[] deleteThreads = new Thread[N];
        for (int i = 0; i < N; i++) {
            deleteThreads[i] = new Thread(new Delete(c, i));
        }
        for (int i = 0; i < N; i++) {
            deleteThreads[i].start();
        }

        for (int i = 0; i < N; i++) {
            try {
                deleteThreads[i].join();
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        Thread printSortedThread = new Thread(new PrintSorted(c));
        printSortedThread.start();

        try {
            printSortedThread.join();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }


    public static void main(String[] args) {
//        TestInsert();
//        TestDeleteEmpty();
//        TestMemberEmpty();
//        TestInsertDelete();
//        TestInsertDeleteMember();
        TestInsertDeleteMemberPrintSorted();
    }
}
