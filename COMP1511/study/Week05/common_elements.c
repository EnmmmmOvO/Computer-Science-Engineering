#include <stdio.h>
#define MAX_VALUE 10

int common_elements(int length, int source1[length], int source2[length], int destination[length]);


int main (void)
{
    int length = 5;
    int source1[5] = {1,2,3,2,1};
    int source2[5] = {1,2,3,4,5};
    int destination[5];

    int a = common_elements(length, source1, source2, destination);
    for (int i = 0; i < a; i ++) 
        printf("%d \n", destination[i]);
    return 0;
}


int common_elements(int length, int source1[length], int source2[length], int destination[length]) {
    int loopA = 0;
    int destinations = 0;
    while (loopA < length)
    {
        int loopB = 0;
        while (loopB < length)
        {
            if (source1[loopA] == source2[loopB])
            {
                destination[destinations] = source1[loopA];
                destinations += 1; 
                loopB = 1000000000;
            }
            loopB ++;
            
        }
        loopA ++;
    }
    return destinations;
}

// You may optionally add a main function to test your common_elements function.
// It will not be marked.
// Only your common_elements function will be marked.