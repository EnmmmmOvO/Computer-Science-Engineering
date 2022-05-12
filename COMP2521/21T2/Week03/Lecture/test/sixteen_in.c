// Convert string of binary digits to 16-bit signed integer

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define N_BITS 16

int16_t sixteen_in(char *bits);

int main(int argc, char *argv[]) {

    for (int arg = 1; arg < argc; arg++) {
        printf("%d\n", sixteen_in(argv[arg]));
    }

    return 0;
}

//
// given a string of binary digits ('1' and '0')
// return the corresponding signed 16 bit integer
//
int16_t sixteen_in(char *bits) {
    int16_t num = 0;
    int16_t mask = 1;
    for (int i = N_BITS - 1; i >= 0; i--) {
        if (bits[i] == '1') 
            num = num | mask; 
        if (i != 0)
            mask = mask << 1;
    }
    return num;
}

