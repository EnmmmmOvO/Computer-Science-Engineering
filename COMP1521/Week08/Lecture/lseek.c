#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>



int main (int argc, char *argv[]) {
    int read_file_rescriptor = open(argv[1], O_RDONLY);
    char bytes[1];

    lseek(read_file_rescriptor, -2, SEEK_END);
    read(read_file_rescriptor, bytes, 1);
    printf("last byte of the file is %c 0x%02x\n", bytes[0], bytes[0]);

    lseek(read_file_rescriptor, 0, SEEK_SET);
    read(read_file_rescriptor, bytes, 1);
    printf("first byte of the file is %c 0x%02x\n", bytes[0], bytes[0]);

    lseek(read_file_rescriptor, 0, SEEK_CUR);
    read(read_file_rescriptor, bytes, 1);
    printf("first byte of the file is %c 0x%02x\n", bytes[0], bytes[0]);

    lseek(read_file_rescriptor, 4, SEEK_SET);
    read(read_file_rescriptor, bytes, 1);
    printf("first byte of the file is %c 0x%02x\n", bytes[0], bytes[0]);

    return 0;
}