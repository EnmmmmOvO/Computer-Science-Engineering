//spiral.c
//By Alex Rowell z5116848
//Written 20th/21st March 2017
//A program to print a spiral of stars

#include <stdio.h>
#include <stdlib.h>


//A key part of this implementation is splitting the numbers into lines
//These are the straight lines of numbers, with the first number coming from the line before
//There are 4 cases to deal with each line based on which direction it would go when spiraling inwards
//(For the example below 'r' is for lines going right, 'd' for lines going down, 'u' for lines going up and 'l' for lines going left)
//eg.
// rrrrr
// ----d
// urr-d
// u---d
// lllld

int main(void) {
    int num;

    printf("Enter size: ");
    if (!scanf("%d", &num) || num % 2 == 0) {
        //Did not get a number or the number is even, exit
        return 1;
    }

    int row = 0;
    int col = 0;

    while (row < num) {
        col = 0;

        while (col < num) {
            if (row <= num/2 && row % 2 == 0 && col >= row - 1 && col <= num-row - 1) { //Line going to the right

                printf("*");

            } else if (row > num/2 && row % 2 == 0 && col <= row && col >= num - row - 1) { //Line going to the left

                printf("*");

            } else if (col <= num/2 && col % 2 == 0 && row >= col + 2 && row < num - col - 1) { //Line going upwards

                printf("*");

            } else if (col > num/2 && col % 2 == 0 && row <= col && row >= num - col) { //Line going downwards

                printf("*");

            } else { // Not part of any line

                printf("-");

            }

            col = col + 1;
        }
        printf("\n");
        row = row + 1;
    }

    return 0;
}
