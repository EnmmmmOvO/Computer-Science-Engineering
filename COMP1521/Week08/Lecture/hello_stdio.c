#include <stdio.h>

int main (int argc, char *argv[]) {
    char bytes[] = "Hello world!\n";
    for (int loop = 0; bytes[loop] != '\0'; loop++) {
        fputc(bytes[loop], stdout);
    }
    
    for (int loop = 0; loop < (sizeof bytes) - 1; loop++) {
        fputc(bytes[loop], stdout);
    }

    for (char *loop = &bytes[0]; *loop != '\0'; loop++) {
        fputc(*loop, stdout);
    }    

    return 0;
}
