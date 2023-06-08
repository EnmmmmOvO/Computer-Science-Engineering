
#define P(v) atomic { v > 0; v = v - 1 }
#define V(v) v = v + 1

// pre-provided
byte agent = 1;

byte paper = 0;
byte tobacco = 0;
byte match = 0;

// student's additions
byte SmA = 0;
byte SmB = 0;
byte SmC = 0;

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

  run TobaccoPusher();
  run PaperPusher();
  run MatchPusher();
}

proctype SmokerA() {
  do
  ::
    P(paper);
    P(match);
    d_step {
      balance_paper = balance_paper - 1;
      balance_match = balance_match - 1;
      printf("SMOKEA: Got a paper and matches. Puff Puff.");
    }
    V(agent);
  od
}

proctype SmokerB() {
  do
  ::
    P(tobacco);
    P(match);
    d_step {
      balance_tobacco = balance_tobacco - 1;
      balance_match = balance_match - 1;
      printf("SMOKEB: Got a tobacco and matches. Puff Puff.");
    }
    V(agent);
  od
}

proctype SmokerC() {
  do
  ::
    P(tobacco);
    P(paper);
    d_step {
      balance_tobacco = balance_tobacco - 1;
      balance_paper = balance_paper - 1;
      printf("SMOKEC: Got a tobacco and paper. Puff Puff.");
    }
    V(agent);
  od
}

// pushers

proctype TobaccoPusher() {
  do ::
    V(tobacco);
    P(paper);
    P(match);
    V(SmA);
    P(SmB);
    P(SmC);
    V(paper);
    V(match);
  od
}

proctype PaperPusher() {
  do ::
    V(paper);
    P(tobacco);   
    P(match);
    V(SmB);
    P(SmA);
    P(SmC);
    V(tobacco);   
    V(match);

  od
}

proctype MatchPusher() {
  do ::
    V(match);
    P(tobacco);
    P(paper);
    V(SmC);
    P(SmA);
    P(SmB);
    V(tobacco);
    V(paper);
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