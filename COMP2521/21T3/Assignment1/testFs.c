// Main program for testing the File System ADT

#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Fs.h"

int main(void) {
    Fs fs = FsNew();
	FsMkfile(fs, "hello.txt");
	FsMkfile(fs, "world.txt");
	FsMkdir(fs, "bin");
	FsMkfile(fs, "bin/ls");
	FsMkfile(fs, "bin/pwd");
	FsMkdir(fs, "home");
	FsMkdir(fs, "home/jas");
	FsMkfile(fs, "home/jas/todo.txt");
	FsMkfile(fs, "home/jas/mail.txt");
	FsTree(fs, "/home/jas");
	printf("---\n"); // marker to separate output
	FsTree(fs, NULL);
    FsFree(fs);
}

