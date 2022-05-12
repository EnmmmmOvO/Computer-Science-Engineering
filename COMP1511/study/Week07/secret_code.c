#include <stdio.h>

int main (void) {
    int characterA;
    int characterB;
    while ((characterA = getchar()) != EOF && (characterB = getchar()) != EOF) {
        putchar(characterA < characterB ? characterA : characterB);
    }
    printf("\n");
    return 0;
}