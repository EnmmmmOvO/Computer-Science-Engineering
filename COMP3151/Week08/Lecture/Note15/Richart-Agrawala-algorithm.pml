/* Ricart-Agrawala distribute mutual exclusion algorithm

   implementation due to M. Ben-Ari with minor tweaks by K. Engelhardt

   incorrect due to wrap-around of byte-sized myNum
*/

#define PID
#define N 3
#include "critical2.h"

#define MutexDontCare
byte myNum[N];
byte highestNum[N];
bool requestCS[N];
chan deferred[N] = [N] of { byte };

mtype = { request, reply };
chan ch[N] = [N] of { mtype, byte, byte };

proctype MainCS( byte myID ) {
  byte J, K;
  do ::
        non_critical_section();
        atomic {
          requestCS[myID] = true ;
          myNum[myID] = highestNum[myID] + 1 ;
        };

wap:    for (J : 0..(N-1)) {
          if
            :: J != myID ->
               ch[J] ! request, myID, myNum[myID];
            :: else
          fi
        };
        for (K : 0..(N-2)) {
          ch[myID] ?? reply, _ , _
        }
csp:    critical_section();
        requestCS[myID] = false;

        byte num;
        do
          :: empty(deferred[myID]) -> break;
          :: deferred[myID] ? num -> ch[num] ! reply, 0, 0
        od
  od
}

proctype Receive( byte myID ) {
  byte reqNum, source;
  do ::
        ch[myID] ?? request, source, reqNum;
        highestNum[myID] =
        ((reqNum > highestNum[myID]) ->
         reqNum : highestNum[myID]);
        atomic {
          if
            :: requestCS[myID] &&
               ( (myNum[myID] < reqNum) ||
                 ( (myNum[myID] == reqNum) &&
                   (myID < source)
                 ) ) ->
               deferred[myID] ! source
            :: else ->
               ch[source] ! reply, 0, 0
          fi
        }
  od
}

init {
  byte K;
  atomic {
    for (K : 0..(N-1)) {
      run MainCS(K);
      run Receive(K)
    }
  };
  (_nr_pr == 1);
}

/* made for NPROC = 3 */
#define pwap    MainCS[0]@wap
#define pcsp    MainCS[0]@csp
#define qwap    MainCS[1]@wap
#define qcsp    MainCS[1]@csp
#define rwap    MainCS[2]@wap
#define rcsp    MainCS[2]@csp

ltl mutex { !<>(pcsp && qcsp) }
ltl dlf   { [](pwap && qwap -> <>(pcsp || qcsp)) }
ltl aud   { [](pwap && ([]!(qwap || rwap)) -> <>pcsp) }
ltl ee    { [](pwap -> <>pcsp) }