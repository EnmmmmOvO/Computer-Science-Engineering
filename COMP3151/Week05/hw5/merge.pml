#define MAX 10

chan input1 = [0] of { byte };
chan input2 = [0] of { byte };
chan output = [0] of { byte, byte };

proctype merge() {
   byte a;
   byte b;
   bit status_1 = true;
   bit status_2 = true;
   do
   :: status_1 == true && status_2 == true ->
      input1 ? a;
      input2 ? b;

      if
      :: a > b -> output ! b, a;
      :: else -> output ! a, b;
      fi;

      if 
      :: a == 255 -> status_1 = false;
      :: b == 255 -> status_2 = false;
      :: else -> skip;
      fi;
   :: status_1 == true && status_2 == false ->
      input1 ? a;
      if
      :: a == 255 -> break;
      :: else ->
         input1 ? b;
         if
         :: b == 255 -> break;
         :: else -> skip;
         fi;
      fi;
   :: status_2 == true && status_1 == false ->
      input2 ? a;
      if
      :: a == 255 -> break;
      :: else ->
         input2 ? b;
         if
         :: b == 255 -> break;
         :: else -> skip;
         fi;
      fi;
   :: else -> break;
   od 
}

proctype array_send1() {

   byte array_1[MAX];
   array_1[0] = 1;
   array_1[1] = 4;
   array_1[2] = 5;
   array_1[3] = 8;
   array_1[4] = 255;

   byte i = 0;
   for (i: 0 .. MAX) {
      input1 ! array_1[i];
      if 
      :: array_1[i] == 255 -> break;
      :: else -> skip;
      fi;
   }
}

proctype array_send2() {

   byte array_2[MAX];
   array_2[0] = 2;
   array_2[1] = 3;
   array_2[2] = 6;
   array_2[3] = 7;
   array_2[4] = 9;
   array_2[5] = 255;

   byte i = 0;
   for (i: 0 .. MAX) {
      input2 ! array_2[i];
      if 
      :: array_2[i] == 255 -> break;
      :: else -> skip;
      fi;
   }
}

proctype array_get() {
   byte i = 0;
   byte array[2 * MAX];
   byte a;
   byte b;
   do
   :: output ? a, b;
      if
      :: a == 255 -> break;
      :: b == 255 -> 
         array[i] = a;
         break;
      :: else -> 
         array[i] = a;
         array[i + 1] = b;
         i = i + 2;
      fi; 
   od

   i = 0;
   for (i: 0.. 2 * MAX) {
      if 
      :: array[i] == 0 -> break;
      :: else -> printf("%d ", array[i]);
      fi;
   }
   printf("\n");
}  


init {
   run array_get();
   run merge();
   run array_send1();
   run array_send2();
   
}


