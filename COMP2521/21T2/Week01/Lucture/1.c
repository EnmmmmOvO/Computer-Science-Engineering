#include <stdio.h>
#include <assert.h>

int main (void) {
    char input;
    int a;
    scanf("%c\n", &input);
    switch (input) {
        case'W': a = 1; break;
        default: a = 0;
    }

    assert(a == 0);
    return 0;
}