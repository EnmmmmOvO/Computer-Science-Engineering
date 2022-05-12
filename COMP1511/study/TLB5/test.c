#include <stdio.h>

int main (void)
{
    int a = 51;
    printf("%d\n", a % 10);
    printf("%d\n", (a - a % 10 ) / 10);
    return 0;
}
