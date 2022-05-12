#include <unistd.h>

int main (void) {
    while (1) {
        char bytes[4096];
        long byte_read = syscall(0, 0, bytes, 4096);
        if (byte_read <= 0) {
            break;
        }
        syscall(1, 1, bytes, byte_read);
    }
    return 0;
}