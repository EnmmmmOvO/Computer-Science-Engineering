#include <stdio.h>
#include <stdlib.h>

int main (void) {
    char *value = getenv("STATUS");
    printf("Environment variable 'STATUS' has value '%s'\n", value);
    return 0;
}