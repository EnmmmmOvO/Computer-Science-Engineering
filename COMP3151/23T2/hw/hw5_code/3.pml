#define SIZE 3
#define EOF 255

byte shared_array[SIZE * 2];
byte hasValue[2];
byte value[2];

byte array_x[SIZE];
byte array_y[SIZE];

chan ch_x = [0] of { byte };
chan ch_y = [0] of { byte };

proctype Input_x() {
    byte i = 0;
    do 
    :: i < SIZE ->
        if
        :: array_x[i] == EOF -> break;
        :: else -> 
            ch_x!array_x[i];
            i = i + 1;
        fi
    :: else -> break;
    od
    ch_x!EOF;
}

proctype Input_y() {
    byte i = 0;
    do 
    :: i < SIZE -> 
        if
        :: array_y[i] == EOF -> break;
        :: else -> 
            ch_y!array_y[i];
            i = i + 1;
        fi
    :: else -> break;
    od
    ch_y!EOF;
}

proctype Output() {
    byte i = 0;
    do 
    :: i < SIZE * 2 ->
        if 
        :: hasValue[0] == 2 && hasValue[1] == 2 -> break 
        :: hasValue[0] == 2 && hasValue[1] == 1 -> 
            shared_array[i] = value[1];
            i = i + 1;
            hasValue[1] = 0; 
        :: hasValue[0] == 1 && hasValue[1] == 2 -> 
            shared_array[i] = value[0];
            i = i + 1;
            hasValue[0] = 0; 
        :: hasValue[0] == 1 && hasValue[1] == 1 -> 
            if 
            :: value[0] < value[1] -> 
                shared_array[i] = value[0];
                i = i + 1;
                hasValue[0] = 0;
            :: else -> 
                shared_array[i] = value[1];
                i = i + 1;
                hasValue[1] = 0;
            fi
        :: hasValue[0] == 0 ->
            ch_x?value[0];
            if 
            :: value[0] == EOF -> hasValue[0] = 2; 
            :: else -> hasValue[0] = 1;
            fi 
        :: hasValue[1] == 0 ->
            ch_y?value[1];
            if 
            :: value[1] == EOF -> hasValue[1] = 2; 
            :: else -> hasValue[1] = 1;
            fi 
        fi
    :: else -> break;
    od
}

init {
    hasValue[0] = 0;
    hasValue[1] = 0;

    array_x[0] = 1;
    array_x[1] = EOF;
    array_x[2] = 5;

    array_y[0] = 2;
    array_y[1] = 4;
    array_y[2] = 6;

    run Input_x();
    run Input_y();
    run Output();

    byte i;
    for (i : 0 .. SIZE * 2 - 1) {
        printf("%d ", shared_array[i]);
    }
}
