#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>

int main (int argc, char *argv[]) {
    char ch[] = "ab10! 0A`";
    for (int loop = 0; ch[loop] != '\0'; loop ++) 
        if (!isalnum(ch[loop])) 
            printf("1");
    return 0;
}