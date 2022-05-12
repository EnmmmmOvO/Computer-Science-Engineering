// Prints out a file with line numbers
// Assumes lines are no longer than MAX_LINE_LENGTH
// Usage: ./linenos [File]

#include <stdio.h>
#include <stdlib.h>

#define MAX_LINE_LENGTH 128

int start(char line[MAX_LINE_LENGTH + 1]) {
	if (line[0] == '*' && line[1] == '*' &&
		line[2] == '*' && line[3] == ' ' &&
		line[4] == 'S' && line[5] == 'T' &&
		line[6] == 'A' && line[7] == 'R' &&
		line[8] == 'T' && line[9] == ' ' &&
		line[10] == 'O' && line[11] == 'F') 
		return 1;
	return 0;
}

int main(int argc, char *argv[]) {
	FILE *fp;
	if (argc == 1) {
		fp = stdin;
	} else if (argc == 2) {
		// fopen takes two strings: a filename and an access mode. The
		// filename is simply the name of the file that should be opened.
		// The access mode determines whether the file should be opened for
		// reading or writing (or both) and if opened for writing whether
		// the file should be truncated (emptied) first.

		// Here we open the file given in the first command-line argument
		// for reading.
		fp = fopen(argv[1], "r");

		// fopen can fail if the file doesn't exist or if the user does not
		// have permission to open it in the specified mode. If fopen fails,
		// it will return NULL. Otherwise, it will return a file pointer,
		// which you can pass into other file handling functions.
		if (fp == NULL) {
			fprintf(stderr, "Can't open %s\n", argv[1]);
			exit(EXIT_FAILURE);
		}
	} else {
		fprintf(stderr, "Usage: %s [File]\n", argv[0]);
		exit(EXIT_FAILURE);
	}

	char line[MAX_LINE_LENGTH + 1];
	int lineNo = 1;

	// fgets takes a string buffer, a size and a file pointer. It reads
	// characters into the given buffer until it has read in `size - 1`
	// characters or a newline, whichever occurs first. The newline is
	// included. A null terminator is added after the last character
	// read in.
	// If fp is already at the end of the file, fgets will return NULL.
	int temp = 0;
	while (fgets(line, MAX_LINE_LENGTH + 1, fp) != NULL && temp == 0) {
		if (start(line) == 1) temp = 1;
	}
	while (fgets(line, MAX_LINE_LENGTH + 1, fp) != NULL) {
		if (line != NULL) {
			printf("%d ", lineNo);
			printf("%s", line);
			lineNo++;
		}
		if (lineNo == 20) {
			break;
		}	
	}

	// fclose closes the given file. Not closing a file will lead to memory
	// leaks. A file pointer can no longer be used after it is closed.
	fclose(fp);
}

