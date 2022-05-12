#include <stdio.h>

int main (void)
{
    int array[36] = {0};
    
    int number = 0;
    while (scanf("%d", &number) == 1)
    {
        array[number] = 1;
    }

    printf("\n");
    
    int loop = 0;
    while (loop < 36)
    {
        printf("%d", array[loop]);
        if (loop != 35)
        {
            printf(" ");
        } else {
            printf("\n");
        }
        loop = loop + 1;
    }
    return 0;
}