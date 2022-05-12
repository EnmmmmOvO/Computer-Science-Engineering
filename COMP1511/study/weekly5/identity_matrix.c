//z5286124
// identity_matrix.c
// Given a 2D array (or matrix), find the
// Corresponding identity matrix
#include <stdio.h>
#include <stdlib.h>


void make_identity(int size, int matrix[size][size]);
void print_matrix(int size, int matrix[size][size]);

// This is a simple main function that you can use to test your identity_matrix
// function.
// It will not be marked - only your array_sum_prod function will be marked.
//
// Note: the autotest does not call this main function!
// It calls your identity_matrix function directly.
// Any changes that you make to this main function will
// not affect the autotests.
int main(void)
{

    int array3[3][3] = {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}};

    make_identity(3, array3);

    print_matrix(3, array3);

    return 0;
}

//Makes a square matrix into an identity matrix
void make_identity(int size, int matrix[size][size])
{
    int lie = 0;
    while (lie < size)
    {
        int row = 0;
        while (row < size)
        {
            matrix[lie][row] = 0;
            row ++;
        }
        lie ++;
    }
    lie = 0;
    while (lie < size)
    {
        matrix[lie][lie] = 1;
        lie ++;
    }
}

//Prints out a square matrix of any size
void print_matrix(int size, int matrix[size][size])
{
    int i = 0;
    while (i < size)
    {
        int j = 0;
        while (j < size)
        {
            printf("%d ", matrix[i][j]);
            j++;
        }
        printf("\n");
        i++;
    }

}
