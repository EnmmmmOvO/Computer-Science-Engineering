// shared counter variable
byte c = 0;

proctype counter() {
  // these variables are local to (an instance of) counter
  byte temp = 0;
  byte i = 0;
  /* when we execute a do statement:
     - non-deterministically choose a
       non-blocking branch (delimited by ::)
       the first statements of each branch
       is a conditional.
       conditionals block if they are false.
     - if every branch is blocking,
       we're deadlocked!
   */
  do
  :: i < 10 ->
     temp = c;
     c = temp + 1; // this and the previous line are separate
                   // so that we follow the LCR restriction
     i = i + 1;
  :: i >= 10 ->  // why on earth this?
       // we could say else instead of i >= 10
     break;
  od
}

init {
  run counter();
  run counter();
  _nr_pr == 1; // guard: blocks until the conditional becomes true
               // _nr_pr counts the number of running procs
  assert(2 <= c && c <= 20);
}