#include <stdio.h>

int main (void)
{
    int size;
    printf("How many numbers: ");
    scanf("%d", &size);

    int loop = 0;
    int sum = 0;
    while (loop < size)
    {
        int number;
        scanf("%d", &number);
        sum = sum + number;
        loop ++;
    }

    printf("The sum is: %d\n", sum);
    return 0;
}