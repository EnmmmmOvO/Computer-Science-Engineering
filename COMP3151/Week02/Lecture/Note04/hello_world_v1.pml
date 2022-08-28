//proctype: process type
//a process that we could spawn instances of
//if we felt like it
proctype P(byte id) {
  /*_pid: short for process ID
          that is a number assigned to each running process
   */
  printf("================ Hello world, my PID is %d and my ID is %d!\n",_pid,id);
  /*
   pid is unique among *running* processes,
   but not unique over all time.
   You can have two distinct procs with the same PID,
    if their lifetimes don't overlap.
   Global max: 255 processes at a time
   */
}

/*
  init: a special process that will be active
        at startup.
 */
init {
  run P(1);
  run P(2);
  run P(3);
}