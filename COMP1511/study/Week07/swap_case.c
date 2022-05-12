// Function to print out a string that has had it's cases swapped.
// swap_case.c
//
// This program was written by YOUR-NAME-HERE (z5555555)
// on INSERT-DATE-HERE
 
#include <stdio.h>
#include <ctype.h>

int swap_case(int character);

int main(void) {
    int alpha;
    while ((alpha = getchar()) != EOF) {
        alpha = swap_case(alpha);
        putchar(alpha);
    }
    return 0;
}

int swap_case(int character) {
    if (isupper(character)) {
        character = tolower(character);
    } else if (islower(character)) {
        character = toupper(character);
    }
    // TODO: Write this function, which should:
    //  - return character in lower case if it is an upper case letter
    //  - return character in upper case if it is an lower case letter
    //  - return the character unchanged otherwise

    return character;
}