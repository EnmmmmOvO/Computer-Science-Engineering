#include <stdio.h>

#define MAX_VALUE 256

int main (void) {
    char character[MAX_VALUE];
    fgets(character, MAX_VALUE, stdin);
    int a;
    scanf("%d", &a);

    printf("The character in position %d is '%c'\n", a, character[a]);
    return 0;
}