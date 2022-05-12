#include <stdio.h>
#include <ctype.h>

int test(int alpha);

int main (void)
{
    int alpha;
    while ((alpha = getchar()) != EOF) {
        if (test(alpha) == 0) {
            putchar(alpha);
        }
    }
    return 0;
}

int test(int alpha) {
    if (alpha == 'a' || alpha == 'e' || alpha == 'i' || alpha == 'o' || alpha == 'u') {
        return 1;
    } else {
        return 0;
    }
}