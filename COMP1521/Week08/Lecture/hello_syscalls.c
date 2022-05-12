#include <unistd.h>

int main (void) {
    char bytes[15] = "Hello, World!\n";
    syscall(1, 1, bytes, 14);
    return 0;
}