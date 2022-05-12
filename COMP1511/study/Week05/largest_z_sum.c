// Find the largest sum of numbers in a z shape.

#include <stdio.h>
#include <assert.h>

#define MAX_SIZE 100

int largest_z_sum(int size, int array[MAX_SIZE][MAX_SIZE]);

// DO NOT CHANGE THIS MAIN FUNCTION
int main(void) {
    int array[MAX_SIZE][MAX_SIZE];

    // Get the array size.
    int size;
    printf("Enter 2D array side length: ");
    scanf("%d", &size);
    assert(size >= 3);

    // Scan in values for the array.
    printf("Enter 2D array values:\n");
    int i = 0;
    while (i < size) {
        int j = 0;
        while (j < size) {
            assert(scanf("%d", &array[i][j]) == 1);
            j++;
        }
        i++;
    }

    printf("The largest z sum is %d.\n", largest_z_sum(size, array));

    return 0;
}

// Return the largest sum of numbers in a z shape.
int largest_z_sum(int size, int array[MAX_SIZE][MAX_SIZE]) {
    //Compare several zigzags
    int number = 0;
    int loopNumber = 1;
    while (loopNumber <= size - 2)
    {
        number = number + loopNumber * loopNumber;
        loopNumber ++;
    }

    //Create a sequence to place the sum
    int summary[101] = {0};

    //Define each zigzag and sum it
    int loopSize = 3;
    int p = 0;
    //Define the zigzag size
    while (loopSize <= size)
    {
        //Define the starting position of the zigzag (line:row row:column)
        int loopStartLine = 0;
        while (loopStartLine <= size - loopSize)
        {
            int loopStartRow = 0;
           
            while (loopStartRow <= size - loopSize)
            {
                int sum = 0;
                //sum
                int loopSumLine = loopStartLine;
                int loopSumLineB = loopStartLine;
                int loopSumRow = loopStartRow;
                int loopSumRowB = loopStartRow;
                //Sum the first row and the last row
                while (loopSumRow < loopSumRowB + loopSize)
                {
                    sum = sum + array[loopSumLine][loopSumRow] + array[loopSumLine + loopSize - 1][loopSumRow];;
                    loopSumRow ++;
                }
                //Find the middle sum
                loopSumRow = loopSumRow - 2;
                loopSumLine ++;
                while (loopSumLine <= loopSumLineB + loopSize - 2)
                {
                    sum = sum + array[loopSumLine][loopSumRow];
                    loopSumLine ++;
                    loopSumRow = loopSumRow -1;
                }

                //The assignment
                summary[p] = sum;
                p ++;

                loopStartRow ++;
            }
            loopStartLine ++;
        }
        loopSize ++;
    }

    //Compare the size
    int loopCompare = 1;
    int maximum = summary[0];
    while (loopCompare < number)
    {
        if (maximum < summary[loopCompare])
        {
            maximum = summary[loopCompare];
        }
        loopCompare ++;
    }

    return maximum;
}