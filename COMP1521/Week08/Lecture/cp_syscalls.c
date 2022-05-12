#include <unistd.h>

int main (int argc, char *argv[]) {
    long read_file_descriptor = syscall(2, argv[1], 0, 0);
    long write_file_descriptor = syscall(2, argv[2], 0x41, 0644);
    while (1) {
        char bytes[4096];
        long bytes_read = syscall(0, read_file_descriptor, bytes, 4096);
        if (bytes_read <= 0) {
            break;
        }
        syscall(1, write_file_descriptor, bytes, bytes_read);
    }
}