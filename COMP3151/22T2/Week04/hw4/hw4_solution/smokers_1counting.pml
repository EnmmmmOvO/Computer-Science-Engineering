
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

int tobaccoReady = 0;
int paperReady = 0;
int matchReady = 0;

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
    P(pusher);
    if
    :: matchReady != 0 ->
       matchReady = matchReady - 1;
       V(readyB);
    :: matchReady == 0 && paperReady != 0 ->
       paperReady = paperReady - 1;
       V(readyC);
    :: else ->
      tobaccoReady = tobaccoReady + 1;
    fi
    V(pusher);
  od
}

proctype PaperPusher() {
  do ::
    P(paper);
    P(pusher);
    if
    :: tobaccoReady != 0 ->
       tobaccoReady = tobaccoReady - 1;
       V(readyC);
    :: tobaccoReady == 0 && matchReady != 0 ->
       matchReady = matchReady - 1;
       V(readyA);
    :: else ->
      paperReady = paperReady + 1;
    fi
    V(pusher);
  od
}

proctype MatchPusher() {
  do ::
    P(match);
    P(pusher);
    if
    :: tobaccoReady != 0 ->
       tobaccoReady = tobaccoReady - 1;
       V(readyB);
    :: tobaccoReady == 0 && paperReady != 0 ->
       paperReady = paperReady - 1;
       V(readyA);
    :: else ->
      matchReady = matchReady + 1;
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

ltl zero_one {
  [](  agent <= 1
    && paper <= 1
    && tobacco <= 1
    && match <= 1
    && readyA <= 1
    && readyB <= 1
    && readyC <= 1
    && pusher <= 1
    && matchReady <= 1
    && tobaccoReady <= 1
    && paperReady <= 1
  )
}