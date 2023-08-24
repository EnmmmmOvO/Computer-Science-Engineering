
/* 
  This example is to illustrate the meaning of the "weak fairness" setting for Spin.
  Try the specs with weak fairness enabled, and without.
 
  Note that weak fairness applies to scheduling of processes, but not to selection of
  cases of the do loop. 

  Also note that processes are never scheduled after they terminate, but one process is
  scheduled to move at every step. 
*/

bit x = 0; 
bit y = 0;
bit z = 0; 

active proctype P() {
  y = 1; 
  do               /* all non-deterministic choices are always enabled */
    :: true ->
         x = 0 ; y = 0
    :: true ->
         x = 1 ; y = 1
  od 
}

active proctype Q() {
  z = 1 
} 

ltl evx { <> x }
ltl evy { <> y } 
ltl evz { <> z }
ltl iox { ([] <> x) implies []<> y }
