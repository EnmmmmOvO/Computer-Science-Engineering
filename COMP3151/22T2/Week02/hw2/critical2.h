/* 
  Definitions for critical section; derived from Ben-Ari's.

  If PID is defined, prints _pid in CS, otherwise prints a character parameter.

  If MutexDontCare is defined, no assertion is made about the number of
  processes in their CSs.
*/

#ifndef MutexDontCare
byte critical = 0; 
#endif
#define PID
#ifdef PID
inline critical_section() {
     printf("MSC: %d in CS\n", _pid);
#else
inline critical_section(proc) {
     printf("MSC: %c in CS\n", proc);
#endif
#ifndef MutexDontCare
     critical++;
     assert (critical == 1);
     critical--;
#endif
}

/* 
  Definitions for non-critical sections to complement M Ben-Ari's
  critical.h. If PID is defined, prints _pid in non-CS, otherwise
  prints its mandatory character argument.
*/

#ifdef PID
inline non_critical_section() {
  printf("MSC: %d in non-CS\n", _pid);
#else
inline non_critical_section(proc) {
  printf("MSC: %c in non-CS\n", proc);
#endif
  do                            /* non-deterministically choose how
                                   long to stay, even forever */
    :: true ->
         skip
    :: true ->
         break
  od
}