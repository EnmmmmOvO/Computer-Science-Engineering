#include <unistd.h>
#include <fcntl.h>

int main (int argc, char *argv[]) {
    int read_file_descriptor = open(argv[1], O_RDONLY);
    int write_file_descriptor = open(argv[2], O_WRONLY | O_CREAT, 0644);
    while (1) {
        char bytes[4096];
        ssize_t bytes_read = read(read_file_descriptor, bytes, 4096);
        if (bytes_read <= 0) {
            break;
        }
        write(write_file_descriptor, bytes, bytes_read);
    }
    return 0;     
}