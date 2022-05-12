#include <stdio.h>

int main (void) {
    double d = 4/7.0;
    printf("%lf, %le, %lg, %100.9lf, %.1lf\n", d, d, d, d, d);
    return 0;
}