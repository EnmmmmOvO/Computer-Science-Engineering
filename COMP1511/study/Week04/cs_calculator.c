#include <stdio.h>


int main (void)
{

    int loopA = 1;
    while (loopA == 1)
    {
        int numberA = 0;
        int numberB = 0;
        int numberC = 2;
        printf("Enter instruction: ");
        if (scanf("%d", &numberA) == 1)
        {
            scanf("%d", &numberB);
            if (numberA == 1 || numberA == 2)
            {
                if (numberA == 2)
                {
                    scanf("%d", &numberC);
                } 
                int loop = 0;
                int multi = 1;
                while (loop < numberC)
                {
                    multi = multi * numberB;
                    loop = loop + 1;
                }
                printf("%d\n", multi);
            } else {
                printf("The first number must be 1 or 2!\n");
            }
            
        } else {
            loopA = 0;
        }
    }
    
    return 0;
}