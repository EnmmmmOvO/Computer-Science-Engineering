#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#define MAX_LENGTH 200

int encrypt(int character, int num);

int main (int argc, char *argv[]) {
    int num = atoi(argv[1]);
    int character;
    while ((character= getchar()) != EOF) {
        if (isalpha(character)) {
            character = encrypt(character, num);
        }
            putchar(character);
    }
    return 0;
}

int encrypt(int character, int num) {
    if (isupper(character)) {
        int sumA = character + num;
        if (sumA <= 90 && sumA >= 65) {
            character = sumA;
        } else if (sumA > 90) {
            character = (sumA - 'A') % 26 + 'A';
        } else {
            character = 'Z' - ('Z' - sumA) % 26;
        }
    } else if (islower(character)) {
        int sumB = character + num;
        if (sumB <= 122 && sumB >= 97) {
            character = sumB;
        } else if (sumB > 122) {
            character = (sumB - 'a') % 26 + 'a';
        } else {
            character = 'z' - ('z' - sumB) % 26;
        }
    }

    return character;
}