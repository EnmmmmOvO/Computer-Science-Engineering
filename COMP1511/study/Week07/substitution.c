#include <stdio.h>
#include <ctype.h>


int substitution(int character, char ch[]);

int main (int argc, char *argv[]) {
    if (argc != 2) {
        return 1;
    } else {
        int character;
        while((character = getchar()) != EOF) {
            if (isalpha(character)) {
                character = substitution(character, argv[1]);
            }
            putchar(character);
        }
    }
    return 0;
}

int substitution(int character, char ch[]) {
    if (isupper(character)) {
        int cipher = character - 65;
        character = toupper(ch[cipher]);
    } else if (islower(character)) {
        int cipher = character - 97;
        character = ch[cipher];
    }
    return character;
}