#include <stdio.h>
#include <string.h>

int main (void) {
    char a[4] = "abc";
    char b[100] = "abc";
    strcat(b, a);
    printf("%s\n", b);
    return 0;   

}