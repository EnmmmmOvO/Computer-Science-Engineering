#include <stdio.h>
#define MAX_VALUE 101 

int main (void)
{
    int size;
    printf("Enter square size: ");
    scanf("%d", &size);

    int array[MAX_VALUE][MAX_VALUE] = {0};

    int loopRow = 0;
    int startA = size - 1;
    int loopMiddle = (size + 1) / 2;
    while (loopRow < loopMiddle)
    {
        int startB = startA;
        int loopLine = 0;
        while (loopLine < loopMiddle)
        {
            array[loopRow][loopLine] = startB;
            startB --;
            loopLine ++;
        }
        startB = startB + 2;
        while (loopLine < size)
        {
            array[loopRow][loopLine] = startB;
            startB ++;
            loopLine ++;
        }
        startA --;
        loopRow ++;
    }

    startA = startA + 2;

    while (loopRow < size)
    {
        int startB = startA;
        int loopLine = 0;
        while (loopLine < loopMiddle)
        {
            array[loopRow][loopLine] = startB;
            startB --;
            loopLine ++;
        }
        startB = startB + 2;
        while (loopLine < size)
        {
            array[loopRow][loopLine] = startB;
            startB ++;
            loopLine ++;
        }
        startA ++;
        loopRow ++;       
    }

    int loopC = 0;
    while (loopC < size)
    {
        int loopD = 0;
        while (loopD < size)
        {
            printf("%d", array[loopC][loopD]);
            if (loopD == size - 1)
            {
                printf("\n");
            } else {
                printf(" ");
            }
            loopD ++;
        }
        loopC ++;
    }


    return 0;

}