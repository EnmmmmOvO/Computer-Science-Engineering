#include <stdio.h>

int main (void)
{
    int array[100] = {0};
    printf("Enter numbers forwards:\n");
    int time = 0;
    int number;
    while (scanf("%d", &number) == 1)
    {
        array[time] = number;
        time = time + 1;
    }
    printf("\nReversed:\n");
    time = time - 1;
    while (time >= 0)
    {
        printf("%d\n", array[time]);
        time = time - 1;
    }
    return 0;
}