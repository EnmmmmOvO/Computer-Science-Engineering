#include <stdio.h>

int remove_duplicates(int length, int source[length], int destination[length]);

int main (void)
{
    int length = 6;
    int source[6] = {3,1,4,1,5,9};
    int destination[6] = {0};

    int integer = remove_duplicates(length, source, destination);

    for (int i = 0; i < integer; i ++)
        printf("%d ", source[i]);
    
    printf("\n%d\n", integer);
    return 0;
}


int remove_duplicates(int length, int source[length], int destination[length]) {
    int loopA = 0;
    int destinations = 0;
    while (loopA < length)
    {
        destination[destinations] = source[loopA];
        destinations ++;
        int loopB = 0;
        while (loopB < destinations - 1)
        {
            if (source[loopA] == destination[loopB])
            {
                destination[destinations - 1] = 0;
                destinations = destinations - 1;
                loopB = 1000000;
            }
            loopB ++;
        }
        loopA ++;
    }
    return destinations;
}