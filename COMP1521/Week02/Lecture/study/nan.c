#include <stdio.h>
#include <math.h>

int main(void) {

    double x = 0.0/0.0;

    printf("%lf\n", x); //pri

    printf("%lf\n", -x); //prints -inf

    printf("%lf\n", x - 1);

    printf("%d\n", isnan(x));

    return 0;
}