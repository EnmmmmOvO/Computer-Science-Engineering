  
// Integer array functions
// F15A

#include <stdio.h>

// prints array in the format [v1, v2, ..., vn]
void print_array(int array[], int size);

// checks if array has int num in it
int check_array(int array[], int size, int num);

int main (void) {

    // create an array with values [1, 2, 3]
    int first[3] = {1, 2, 3};

    // create an array with values [78, 90, 23, 10, 6]
    int second[5] = {78, 90, 23, 10, 6};

    // print both arrays in the format [v1, v2, ..., vn]
    printf("Array 1: ");
    print_array(first, 3);
    printf("Array 2: ");
    print_array(second, 5);

    // check if the first array has the value 6
    if (check_array(first, 3, 6) == 1) {
        printf("Array 1 has 6 in it\n");
    } else {
        printf("Array 1 does not have 6 in it\n");
    }

    // check if the second array has the value 6
    if (check_array(second, 5, 6)) {
        printf("Array 2 has 6 in it\n");
    } else {
        printf("Array 2 does not have 6 in it\n");
    }

    return 0;
}

// print an array in the format [v1, v2, ..., vn]
// takes in an array and its size
// outputs nothing
void print_array(int array[], int size) {
    int i = 0;
    printf("[");
    while (i < size) {
        // printf("%d, ", array[i]);
        if (i == size - 1) {
            printf("%d", array[i]);
        } else {
            printf("%d, ", array[i]);
        }
        
        i++;
    }
    printf("]\n");
    
    return;
}

// checks if array has int num in it
// takes in an array, its size and a number
// outputs 1 if number is found or 0 if not
int check_array(int array[], int size, int num) {
    int i = 0;
    while (i < size) {
        if (array[i] == num) {
            // found the number!
            return 1;
        }
        i++;
    }
    
    return 0;
}
