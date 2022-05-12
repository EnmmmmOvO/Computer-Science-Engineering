#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/*```
$ dcc double_not_always.c -o double_not_always
$ ./double_not_always 42.3
d = 42.3
d == d is true
d == d + 1 is false
$  ./double_not_always 4200000000000000000
d = 4.2e+18
d == d is true
d == d + 1 is true
$ ./double_not_always NaN
d = nan
d == d is not true
d == d + 1 is false
````*/

int main(int argc, char *argv[]) {
    assert(argc == 2);

    double d = strtod(argv[1], NULL);

    printf("d = %g\n", d);

    if (d == d) {
        printf("d == d is true\n");
    } else {
        // will be executed if d is a NaN
        printf("d == d is not true\n");
    }

    if (d == d + 1) {
        // may be executed if d is large
        // because closest possible representation for d + 1
        // is also closest possible representation for d
        printf("d == d + 1 is true\n");
    } else {
        printf("d == d + 1 is false\n");
    }

    return 0;
}