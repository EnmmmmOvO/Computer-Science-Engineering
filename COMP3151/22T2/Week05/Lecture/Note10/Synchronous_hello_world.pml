/* a channel called ch
     with queue capacity 0 (synchronous)
     can transmit messages of type byte
 */ 
chan ch = [0] of { byte }

active proctype P() {
  ch ! 30; // send 30 on channel ch
  ch ! 55;
}

active proctype Q() {
  byte x=0;
  ch ? x; // receive a message on ch; save to xmi
  printf("I received: %d\n",x);
  ch ? x;
  printf("I received: %d\n",x);  
}