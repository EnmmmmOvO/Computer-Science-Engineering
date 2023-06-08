
#define P(v) d_step { v > 0; v-- }
#define V(v) v++

// pre-provided
byte agent = 1;

byte paper = 0;
byte tobacco = 0;
byte match = 0;

// student's additions
byte readyA = 0;
byte readyB = 0;
byte readyC = 0;

byte pusher = 1;

bit tobaccoReady = false;
bit paperReady = false;
bit matchReady = false;

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
    P(readyA);
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
    P(readyB);
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
    P(readyC);
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
    P(tobacco);
    P(pusher);
    if
    :: matchReady ->
       matchReady = false;
       V(readyB);
    :: !matchReady && paperReady ->
       paperReady = false;
       V(readyC);
    :: else ->
      tobaccoReady = true;
    fi
    V(pusher);
  od
}

proctype PaperPusher() {
  do ::
    P(paper);
    P(pusher);
    if
    :: tobaccoReady ->
       tobaccoReady = false;
       V(readyC);
    :: !tobaccoReady && matchReady ->
       matchReady = false;
       V(readyA);
    :: else ->
      paperReady = true;
    fi
    V(pusher);
  od
}

proctype MatchPusher() {
  do ::
    P(match);
    P(pusher);
    if
    :: tobaccoReady ->
       tobaccoReady = false;
       V(readyB);
    :: !tobaccoReady && paperReady ->
       paperReady = false;
       V(readyA);
    :: else ->
      matchReady = true;
    fi
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

ltl zero_one {
  [](  agent <= 1
    && paper <= 1
    && tobacco <= 1
    && match <= 1
    && readyA <= 1
    && readyB <= 1
    && readyC <= 1
    && pusher <= 1
  )
}

