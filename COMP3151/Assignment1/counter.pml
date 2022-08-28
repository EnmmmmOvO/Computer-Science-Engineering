#define B 3
#define R 2
#define k 70000

#define BYTE_MAX 127

byte c[B];


active proctype Writer() {
    byte temp[B];
    int i;
    int loop = 0;

    do
    :: k == 0 || loop < k ->
        for (i : 0..(B-1)) {
            temp[i] = c[i];
        }

        i = B-1;
        do
        ::  (i >= 0) ->
            if
            ::  temp[i] == BYTE_MAX ->
                temp[i] = 0;
            ::  else ->
                temp[i]++;
                break;
            fi
            i--;
        ::  else -> break;
        od;

        for (i : 0..(B-1)) {
            c[i] = temp[i];
        }
    :: else -> break;
    od
}

active[R] proctype Reader() {
    byte temp[B];
    int i;
    int loop = 0;

    do
    :: k == 0 || loop < k ->
        for (i : 0..(B-1)) {
            temp[i] = c[i];
        }
    ::  else -> break;
    od;
}
