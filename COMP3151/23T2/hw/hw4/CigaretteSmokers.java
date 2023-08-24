public class CigaretteSmokers {
    static Semaphore3151 agent = new JavaSemaphore(1);
    static Semaphore3151 tobacco = new JavaSemaphore(0);
    static Semaphore3151 paper = new JavaSemaphore(0);
    static Semaphore3151 match = new JavaSemaphore(0);

    /* TODO: Add more semaphores and shared variables here as needed */
    static Semaphore3151 mutex = new JavaSemaphore(1);
    static Semaphore3151 smokerTobacco = new JavaSemaphore(0);
    static Semaphore3151 smokerPaper = new JavaSemaphore(0);
    static Semaphore3151 smokerMatch = new JavaSemaphore(0);
    static boolean isTobacco = false;
    static boolean isPaper = false;
    static boolean isMatch = false;

    public static void main(String[] args) {
        AgentA a = new AgentA();
        AgentB b = new AgentB();
        AgentC c = new AgentC();
        SmokerA sa = new SmokerA();
        SmokerB sb = new SmokerB();
        SmokerC sc = new SmokerC();

        /* TODO: Add and start more threads here as needed */
        PusherTobacco pt = new PusherTobacco();
        PusherPaper pp = new PusherPaper();
        PusherMatch pm = new PusherMatch();

        a.start();
        b.start();
        c.start();
        sa.start();
        sb.start();
        sc.start();
        pt.start();
        pp.start();
        pm.start();
    }

    /* TODO: Add more classes here for threads as needed */
    public static class PusherTobacco extends Thread {
        @Override
        public void run() {
            while (true) {
                tobacco.P();
                mutex.P();
                if (isPaper) {
                    isPaper = false;
                    smokerMatch.V();
                } else if (isMatch) {
                    isMatch = false;
                    smokerPaper.V();
                } else {
                    isTobacco = true;
                }
                mutex.V();
            }
        }
    }

    public static class PusherPaper extends Thread {
        @Override
        public void run() {
            while (true) {
                paper.P();
                mutex.P();
                if (isTobacco) {
                    isTobacco = false;
                    smokerMatch.V();
                } else if (isMatch) {
                    isMatch = false;
                    smokerTobacco.V();
                } else {
                    isPaper = true;
                }
                mutex.V();
            }
        }
    }

    public static class PusherMatch extends Thread {
        @Override
        public void run() {
            while (true) {
                match.P();
                mutex.P();
                if (isTobacco) {
                    isTobacco = false;
                    smokerPaper.V();
                } else if (isPaper) {
                    isPaper = false;
                    smokerTobacco.V();
                } else {
                    isMatch = true;
                }
                mutex.V();
            }
        }
    }

    // Smoker with Tobacco
    public static class SmokerA extends Thread {
        private void smoke() {
            System.out.println("SMOKEA: Got a paper and matches. Puff Puff.");
        }

        @Override
        public void run() {
            while (true) {
                smokerTobacco.P();
                smoke();
                agent.V();
            }
        }
    }

    // Smoker with Paper
    public static class SmokerB extends Thread {
        private void smoke() {
            System.out.println("SMOKEB: Got tobacco and matches. Puff Puff.");
        }

        @Override
        public void run() {
            while (true) {
                smokerPaper.P();
                smoke();
                agent.V();
            }
        }
    }

    // Smoker with Matches
    public static class SmokerC extends Thread {
        private void smoke() {
            System.out.println("SMOKEC: Got tobacco and paper. Puff Puff.");
        }

        @Override
        public void run() {
            while (true) {
                smokerMatch.P();
                smoke();
                agent.V();
            }
        }
    }

    /* Do not change anything below this line */
    public static class AgentA extends Thread {
        @Override
        public void run() {
            while (true) {
                agent.P();
                System.out.println("AGENTA: Supplying tobacco and paper");
                tobacco.V();
                paper.V();
            }
        }
    }

    public static class AgentB extends Thread {
        @Override
        public void run() {
            while (true) {
                agent.P();
                System.out.println("AGENTB: Supplying paper and match");
                paper.V();
                match.V();
            }
        }
    }

    public static class AgentC extends Thread {
        @Override
        public void run() {
            while (true) {
                agent.P();
                System.out.println("AGENTC: Supplying tobacco and match");
                tobacco.V();
                match.V();
            }
        }
    }
}