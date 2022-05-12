#include <unistd.h>

int main (void) {
    char bytes[15] = "Hello, World!\n";
    write(1, bytes, 14);
    return 0;
}