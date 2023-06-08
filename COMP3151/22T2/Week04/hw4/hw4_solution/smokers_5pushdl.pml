
#define P(v) atomic { v > 0; v = v - 1 }
#define V(v) v = v + 1

// pre-provided
byte agent = 1;

byte paper = 0;
byte tobacco = 0;
byte match = 0;

// student's additions
byte smokerA = 0;
byte smokerB = 0;
byte smokerC = 0;

byte pusher = 1;

int balance_paper   = 0;
int balance_match   = 0;
int balance_tobacco = 0;

init {
  run AgentA();
  run AgentB();
  run AgentC();

  run SmokerA();
  run SmokerB();
  run SmokerC();

  run PusherAC();
  run PusherBA();
  run PusherCB();
}

proctype SmokerA() {
  do
  ::
    P(smokerA);
    d_step {
      balance_paper = balance_paper - 1;
      balance_match = balance_match - 1;
      printf("SMOKEA: Got a paper and matches. Puff Puff.");
    }
    V(agent);
    // P(smokerA);
  od
}

proctype SmokerB() {
  do
  ::
    P(smokerB);
    d_step {
      balance_tobacco = balance_tobacco - 1;
      balance_match = balance_match - 1;
      printf("SMOKEB: Got a tobacco and matches. Puff Puff.");
    }
    V(agent);
    // V(smokerB);
  od
}

proctype SmokerC() {
  do
  ::
    P(smokerC);
    d_step {
      balance_tobacco = balance_tobacco - 1;
      balance_paper = balance_paper - 1;
      printf("SMOKEC: Got a tobacco and paper. Puff Puff.");
    }
    V(agent);
    // P(smokerC);
  od
}

// pushers

proctype PusherAC() {
  do ::
    P(pusher);
    P(tobacco);
    P(paper);
    V(smokerC);
    V(pusher);
  od
}

proctype PusherBA() {
  do ::
    P(pusher);
    P(paper);
    P(match);
    V(smokerA);
    V(pusher);
  od
}

proctype PusherCB() {
  do ::
    P(pusher);
    P(tobacco);
    P(match);
    V(smokerB);
    V(pusher);
  od
}

// Provided: Agents

proctype AgentA() {
  do ::
    P(agent);
    printf("AGENTA: Supplying tobacco and paper");
    d_step {
      balance_tobacco = balance_tobacco + 1;
      V(tobacco);
    }
    d_step {
      balance_paper = balance_paper + 1;
      V(paper);
    }
  od
}

proctype AgentB() {
  do ::
    P(agent);
    printf("AGENTB: Supplying paper and match");
    d_step {
      balance_paper = balance_paper + 1;
      V(paper);
    }
    d_step {
      balance_match = balance_match + 1;
      V(match);
    }
  od
}

proctype AgentC() {
  do ::
    P(agent);
    printf("AGENTC: Supplying tobacco and match");
    d_step {
      balance_tobacco = balance_tobacco + 1;
      V(tobacco);
    }
    d_step {
      balance_match = balance_match + 1;
      V(match);
    }
  od
}

ltl balanced {
  [](
    balance_paper >= 0
    && balance_match >= 0
    && balance_tobacco >= 0
  )
}