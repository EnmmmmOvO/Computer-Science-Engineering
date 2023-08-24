/* 
  Definitions for critical section; derived from Ben-Ari's.

  If PID is defined, prints _pid in CS, otherwise prints a character parameter.

  If MutexDontCare is defined, no assertion is made about the number of
  processes in their CSs.
*/

inline critical_section() {
  inCritical = 1 ;
  /* This is just two steps, so is guaranteed to terminate. 
     we rely on the scheduler to determine the actual amount of time in the Critical section. */ 
  inCritical = 0 ; 
}

/* 
  Definitions for non-critical sections to complement M Ben-Ari's
  critical.h. If PID is defined, prints _pid in non-CS, otherwise
  prints its mandatory character argument.
*/


inline non_critical_section() {
  inNonCritical = 1; 
  /*   printf("MSC: %d in non-CS\n", _pid); */
  do                            /* non-deterministically choose how
                                   long to stay, even forever */
    :: true ->
         skip
    :: true ->
         break
  od ; 
  inNonCritical = 0 ; 
}

