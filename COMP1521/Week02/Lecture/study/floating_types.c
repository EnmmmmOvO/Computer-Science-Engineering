#include <stdio.h>
#include <float.h>


int main (int argc, char *argv[]) {
    float f;
    double d;
    long double l;

    printf("float          %2lu bytes  min = %-12g     max = %g\n", sizeof f, FLT_MIN, FLT_MAX);
    printf("double         %2lu bytes  min = %-12g     max = %g\n", sizeof d, DBL_MIN, DBL_MAX);
    printf("long double    %2lu bytes  min = %-12Lg     max = %Lg\n", sizeof l, LDBL_MIN, LDBL_MAX);

    return 0;
}