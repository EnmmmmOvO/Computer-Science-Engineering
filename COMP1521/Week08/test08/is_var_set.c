#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    char *c;
    if ((c = getenv(argv[1])) && (strlen(c) > 0)) {
        printf ("1\n"); 
    } else {
        printf ("0\n");
    }

    return 0;
}