/* a channel called ch
     with queue capacity 1 (asynchronous)
     can transmit messages of type byte
 */ 
chan ch = [1] of { byte }

active proctype P() {
  ch ! 30; // send 30 on channel ch
  ch ! 55;

  /* Two kinds of send:
       ch ! x  // put a message at the end of the queue
       ch !! x // "sort" a message into the queue     
     Four kinds of receive:
       ch ? x    // pop the first message from the queue
                    if it matches our pattern
       ch ? <x>  // read the first message from the queue
                    *without* removing it from the queue
       ch ?? x    // pop the first message from the queue
                     *that* matches our pattern
       ch ?? <x>  // read the first message from the queue
                     *that* matches our pattern
   */
}

active proctype Q() {
  byte x=0;
  ch ? x; // receive a message on ch; save to x
  printf("I received: %d\n",x);
  ch ? x;
  printf("I received: %d\n",x);  
}
