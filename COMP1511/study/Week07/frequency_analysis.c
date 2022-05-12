#include <stdio.h>
#include <ctype.h>

void frequency(int character, int time[26]);

int main (void) {
    int character;
    int time[26] = {0};
    while ((character = getchar()) != EOF) {
        if (isalpha(character)) {
            frequency(tolower(character), time);
        }
    }

    int loopA = 0;
    int total = 0;
    while(loopA < 26) {
        total += time[loopA];
        loopA ++;
    }

    int loopB = 0;
    while (loopB < 26) {
        double a = (double)time[loopB] / (double)total;
        printf("'%c' %lf %d\n", 97 + loopB, a, time[loopB]);
        loopB ++;
    }
    return 0;
    
}

void frequency(int character, int time[26]) {
    int loop = character - 97;
    time[loop] ++;
}