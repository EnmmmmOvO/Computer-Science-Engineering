#include <stdio.h>

int main (void)
{
    //input part
    int number;
    int time = 0;
    int array[10] = {0};
    while (scanf("%d", &number) == 1)
    {
        array[time] = number;
        time = time + 1;
    }
    time = time - 1;
    printf("\n");

    //count part
    int loop = 1;
    int total = array[0];
    int times = 1;
    while (loop <= time)
    {
        
        total = total - 1;
        if (total == 0)
        {
            total = total + array[loop];
            if (loop != time)
            {
                times = times + 1;
            }
        }
        if (total < 0)
        {
            times = 0;
            loop = 10000000;
        } 
        loop = loop + 1;
    }

    printf("%d\n", times);
    return 0;
}