
#define P(v) atomic { v > 0; v = v - 1 }
#define V(v) v = v + 1

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


int balance_paper = 0;
int balance_match = 0;
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
    P(readyA)
    printf("SMOKEA: Got a paper and matches. Puff Puff.");
    V(agent)
  od
}

proctype SmokerB() {
  do
  ::
    P(readyB)
    printf("SMOKEB: Got a tobacco and matches. Puff Puff.");
    V(agent)
  od
}

proctype SmokerC() {
  do
  ::
    P(readyC)
    printf("SMOKEC: Got a tobacco and paper. Puff Puff.");
    V(agent)
  od
}

proctype TobaccoPusher() {
  do ::
    P(tobacco);
    tobaccoReady = true;
    P(pusher);
    if
    :: tobaccoReady && matchReady ->
       matchReady = false;
       tobaccoReady = false;
       V(readyB);
    :: else -> skip
    fi
    if
    :: tobaccoReady && paperReady ->
       paperReady = false;
       tobaccoReady = false;
       V(readyC);
    :: else -> skip
    fi
    V(pusher);
  od
}

proctype PaperPusher() {
  do ::
    P(paper);
    paperReady = false;
    P(pusher);
    if
    :: paperReady && tobaccoReady ->
       tobaccoReady = false;
       paperReady = false;
       V(readyC);
    :: else -> skip
    fi
    if
    :: paperReady && matchReady ->
       matchReady = false;
       paperReady = false;
       V(readyA);
    :: else -> skip
    fi
    V(pusher);
  od
}

proctype MatchPusher() {
  do ::
    P(match);
    matchReady = true;
    P(pusher);
    if
    :: matchReady && tobaccoReady ->
       tobaccoReady = false;
       matchReady = false;
       V(readyB);
    :: else -> skip
    fi
    if
    :: matchReady && paperReady ->
       paperReady = false;
       matchReady = false;
       V(readyA);
    :: else -> skip
    fi
    V(pusher);
  od
}

// Provided: Agents

proctype AgentA() {
  do ::
          P(agent);
          printf("AGENTA: Supplying tobacco and paper");
          V(tobacco);
progress: V(paper);
  od
}

proctype AgentB() {
  do ::
          P(agent);
          printf("AGENTB: Supplying paper and match");
          V(paper);
progress: V(match);
  od
}

proctype AgentC() {
  do ::
          P(agent);
          printf("AGENTC: Supplying tobacco and match");
          V(tobacco);
progress: V(match);
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