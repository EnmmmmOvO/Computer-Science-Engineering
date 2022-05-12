// Prints the first n digits of pi, where n is specified 
// by the user

#include <stdio.h>

#define MAX_DIGITS 10

int main(void) {
    int pi[MAX_DIGITS] = {3, 1, 4, 1, 5, 9, 2, 6, 5, 3};
    printf("How many digits of pi would you like to print? ");

    int digit;
    scanf("%d", &digit);

    if (digit <= 10 && digit >= 0)
    {
        int loop = 0;
        while (loop < digit)
        {
            if (loop == 1)
            {
                printf(".");
            }
            printf("%d", pi[loop]);
            loop = loop + 1;
        }
        printf("\n");
    }

    return 0;
}