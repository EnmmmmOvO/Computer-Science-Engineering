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
        character = tolower(character);
        int loop = 0;
        while (loop < 26) {
            if (ch[loop] == character) {
                character = loop + 65;
                loop = 26;
            }
            loop ++;
        }
    } else if (islower(character)) {
        int loop = 0;
        while (loop < 26) {
            if (ch[loop] == character) {
                character =  loop + 97;
                loop = 26;
            }
            loop ++;
        }
    }
    return character;
}