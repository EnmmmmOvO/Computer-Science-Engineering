//Jinghan Wang
//z5286124

#include <stdio.h>
#include <stdlib.h>

#define SERIES_MAX 46

int main(void) {
    int already_computed[SERIES_MAX + 1] = { 0, 1 };
	int time;
    while (scanf("%d", &time) != EOF) {
        if (time < 2) {
            printf("%d\n", already_computed[time]);
        } else {
            for (int loop = 2; loop <= time; loop ++) {
                already_computed[loop] = already_computed[loop - 1] + 
                already_computed[loop - 2];
                if (loop == time) 
                    printf("%d\n", already_computed[loop]);
            }
        }
    }
    return 0;
}
