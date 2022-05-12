#include <unistd.h>

int main (void) {
    while(1) {
        char bytes[4096];
        ssize_t read_bytes = read(0, bytes, 4096);
        if (read_bytes <= 0) {
            break;
        }
        write(1, bytes, read_bytes);
    }
    return 0;
}