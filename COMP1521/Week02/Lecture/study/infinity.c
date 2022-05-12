#include <stdio.h>
#include <math.h>

int main(void) {

    double x = 1.0/0.0;

    printf("%lf\n", x); //prints inf

    printf("%lf\n", -x); //prints -inf

    printf("%lf\n", x - 1); // prints inf

    printf("%lf\n", 2 * atan(x)); // prints 3.141593

    printf("%d\n", 42 < x); // prints 1 (true)

    printf("%d\n", x == INFINITY); // prints 1 (true)

    return 0;
}