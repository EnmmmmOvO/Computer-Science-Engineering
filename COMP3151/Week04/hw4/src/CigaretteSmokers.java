public class CigaretteSmokers {
    static Semaphore3151 agent    = new JavaSemaphore(1);
    static Semaphore3151 tobacco  = new JavaSemaphore(0);
    static Semaphore3151 paper    = new JavaSemaphore(0);
    static Semaphore3151 match    = new JavaSemaphore(0);

    /* TODO: Add more semaphores and shared variables here as needed */

    public static void main(String[] args) {
        AgentA a = new AgentA();
        AgentB b = new AgentB();
        AgentC c = new AgentC();
        SmokerA sa = new SmokerA();
        SmokerB sb = new SmokerB();
        SmokerC sc = new SmokerC();

        /* TODO: Add and start more threads here as needed */
        a.start();
        b.start();
        c.start();
        sa.start();
        sb.start();
        sc.start();
    }

    /* TODO: Add more classes here for threads as needed */

    // Smoker with Tobacco
    public static class SmokerA extends Thread {

        private void smoke() {
            System.out.println("SMOKEA: Got a paper and matches. Puff Puff.");
        }
        @Override
        public void run() {
            while (true) {
                /* FIXME: This code deadlocks! */
                paper.P();
                match.P();
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
                /* FIXME: This code deadlocks! */
                tobacco.P();
                match.P();
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
                /* FIXME: This code deadlocks! */
                tobacco.P();
                paper.P();
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
