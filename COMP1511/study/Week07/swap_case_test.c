// Function to test your swap_case function.
// swap_case.c
//
// This program was written by YOUR-NAME-HERE (z5555555)
// on INSERT-DATE-HERE
#include <ctype.h> 
#include <stdio.h>

#define MEETS_SPEC 1
#define DOES_NOT_MEET_SPEC 0

int swap_case(int character);
int test_lower_to_upper(void);
int test_upper_to_lower(void);
int test_non_alphabetical(void);


int test_lower_to_upper(void) {
    int alpha = 'a';
    int changeAlpha = swap_case(alpha);
    if (isupper(changeAlpha) && islower(alpha) && changeAlpha + 32 == alpha) {
        return MEETS_SPEC;
    } else {
        return DOES_NOT_MEET_SPEC;
    }
}

int test_upper_to_lower(void) {
    int alpha = 'A';
    int changeAlpha = swap_case(alpha);
    if (isupper(alpha) && islower(changeAlpha) && changeAlpha == alpha + 32) {
        return MEETS_SPEC;
    } else {
        return DOES_NOT_MEET_SPEC;
    }
}

int test_non_alphabetical(void) {
    int alpha = ' ';
    int changeAlpha = swap_case(alpha);
    if (isalpha(alpha) || islower(changeAlpha) || changeAlpha != alpha) {
        return DOES_NOT_MEET_SPEC;
    } else {
        return MEETS_SPEC;
    }
}


//////////////////////////////////////////////////////////////////////////
// NOTE: The below function won't be marked! You can use it for testing //
//////////////////////////////////////////////////////////////////////////

int swap_case(int character) {
    if (isupper(character)) {
        character = tolower(character);
    } else if (islower(character)) {
        character = toupper(character);
    }
    return character;
}

//////////////////////////////////////////////////////////////////////////
// NOTE: DO NOT EDIT BELOW THIS COMMENT!                                //
//////////////////////////////////////////////////////////////////////////

int main(void) {

    printf("Testing turning an lowercase into uppercase: ");
    if (test_lower_to_upper() == MEETS_SPEC) {
        printf("MEETS SPEC\n");
    } else {
        printf("DOES NOT MEET SPEC\n");
    }

    printf("Testing turning an uppercase into lowercase: ");
    if (test_upper_to_lower() == MEETS_SPEC) {
        printf("MEETS SPEC\n");
    } else {
        printf("DOES NOT MEET SPEC\n");
    }

    printf("Testing a non-alphabetical character not changing: ");
    if (test_non_alphabetical() == MEETS_SPEC) {
        printf("MEETS SPEC\n");
    } else {
        printf("DOES NOT MEET SPEC\n");
    }

    return 0;
}
