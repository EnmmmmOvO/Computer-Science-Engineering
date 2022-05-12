#include <stdio.h>
#include <math.h>

int main(void) {

    double x = 0.0/0.0;

    printf("%lf\n", x); //prints nan

    printf("%lf\n", x - 1); // prints nan

    printf("%d\n", x == x); // prints 0 (false)

    printf("%d\n", isnan(x)); // prints 1 (true)

    return 0;
}