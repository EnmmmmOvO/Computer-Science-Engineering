#include <stdio.h>

int main(void) {
    double d = 4/7.0;

    // prints in decimal with (default) 6 decimal places
    printf("%lf\n", d);        // prints 0.571429

    // prints in scientific notation
    printf("%le\n", d);       // prints 5.714286e-01

    // picks best of decimal and scientific notation
    printf("%lg\n", d);       // prints 0.571429

    //  prints in decimal with 9 decimal places
    printf("%.9lf\n", d);    // prints 0.571428571

    //  prints in decimal with 1 decimal place and field width of 5
    printf("%10.1lf\n", d);  // prints        0.6

    return 0;
} 