#include <stdio.h>

#include "get_string.h"

// print a line from stream using fgetc (only)
// reads  in at  most one less than size characters from stream and stores them into the
// buffer pointed to by s.  Reading stops after an EOF or a newline.  If a newline is read, it  is
// stored  into  the buffer.  A terminating null byte ('\0') is stored after the last character in the buffer.
void get_string(char *s, int size, FILE *stream) {
    int read = 0;
    int byte;
    while (read < size - 1 && (byte = fgetc(stream)) != EOF) {
        s[read] = byte;
        read++;
        if (byte == '\n') {
            break;
        }
    }
    s[read] = '\0';
    // PUT YOUR CODE HERE

}
