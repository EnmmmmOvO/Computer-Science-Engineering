/*
   b,x,y,ch

   b is true if you want to add; false if you want to subtract
   x y: the numbers you want to operate on
   ch: the channel you expect your reply on
 */
chan public = [0] of { bool, int, int, chan }

active proctype server() {
  int x;
  int y;
  chan session;
  do
       /* receive where we only accept messages where the bool component is 1 */
    :: public?1,x,y,session ->
       session!x+y
    :: public?0,x,y,session ->
       session!x-y
  od
  /* Q: will it block or go to the next branch?
     A: the do blocks until at least one branch is non-blocking
        when that happens, one of the non-blocking branches is chosen non-deterministically
   */
}

active proctype add_client() {
  chan add_channel = [0] of { int};
  int x = 0;
  public!1,1,1,add_channel;
  add_channel?x;
  printf("** 1 + 1 is %d, according to the server\n",x)
}

active proctype subtract_client() {
  chan subtract_channel = [0] of { int };
  int x = 0;
  public!0,1,1,subtract_channel;
  subtract_channel?x;
  printf("** 1 - 1 is %d, according to the server\n",x)
}