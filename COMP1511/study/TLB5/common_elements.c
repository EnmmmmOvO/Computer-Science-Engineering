#include <stdio.h>

// copy all of the values in source1 which are also found in source2 into destination
// return the number of elements copied into destination

int common_elements(int length, int source1[length], int source2[length], int destination[length])
{
    int number= 0;
    int a = 0;
    while (a < length)
    {
        int b = 0;
        while (b < length)
        {
            if (source1[a] == source2[b])
            {
                destination[number] = source1[a];
                b = 100;
                number ++;
            }
            b ++;
        }
        a ++;
    }
    return number;
}

int main (void)
{
    int d = 6;
    int array1[6] = {1, 4, 1, 5, 9, 2};
    int array2[6] = {1, 1, 8, 2, 5, 3};
    int array3[6];
    int e = common_elements(d, array1, array2, array3);
    printf("%d\n", e);
    return 0;


}
// You may optionally add a main function to test your common_elements function.
// It will not be marked.
// Only your common_elements function will be marked.
