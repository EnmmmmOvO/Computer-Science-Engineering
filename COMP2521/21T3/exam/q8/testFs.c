// Main program for testing totalTextSize

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Fs.h"

int totalTextSize(Fs fs);

static void runTest1(void);
static void runTest2(void);
// Add prototypes for your test functions here

int main(int argc, char *argv[]) {
	if (argc != 2) {
		fprintf(stderr, "usage: %s <test number>\n", argv[0]);
		exit(EXIT_FAILURE);
	}

	switch (atoi(argv[1])) {
		case 1:  runTest1(); break;
		case 2:  runTest2(); break;
		// Add cases for your tests here
		default: fprintf(stderr, "%s: invalid test number '%s'\n",
		                 argv[0], argv[1]);
		         exit(EXIT_FAILURE);
	}
}

// Add your test functions here

/*
File system:
/
    a
    b.txt
    c.txt
    d
    e.txt
*/
static void runTest1(void) {
	Fs fs = FsNew();
	File f1 = newDir("a");
	File f2 = newTextFile("b.txt", "hello world");
	File f3 = newTextFile("c.txt", "this is the content of c.txt");
	File f4 = newDir("d");
	File f5 = newTextFile("e.txt", "i am e.txt");
	addFileToDir(getRoot(fs), f1);
	addFileToDir(getRoot(fs), f2);
	addFileToDir(getRoot(fs), f3);
	addFileToDir(getRoot(fs), f4);
	addFileToDir(getRoot(fs), f5);
	
	printf("File system:\n");
	FsPrint(fs);
	printf("\n");
	
	// "hello world" is 11
	// "this is the content of c.txt" is 28
	// "i am e.txt" is 10
	// Expected result: 11 + 28 + 10 = 49
	printf("Total text size: %d\n", totalTextSize(fs));
	
	FsFree(fs);
}

/*
File system:
/
	a
		a1.txt
		a2
	b
		b1
		b2.txt
*/
static void runTest2(void) {
	Fs fs = FsNew();
	File a = newDir("a");
	addFileToDir(a, newTextFile("a1.txt", "hello"));
	addFileToDir(a, newDir("a2"));
	File b = newDir("b");
	addFileToDir(b, newDir("b1"));
	addFileToDir(b, newTextFile("b2.txt", "goodbye"));
	addFileToDir(getRoot(fs), a);
	addFileToDir(getRoot(fs), b);
	
	printf("File system:\n");
	FsPrint(fs);
	printf("\n");
	
	// "hello" is 5
	// "goodbye" is 7
	// Expected result: 5 + 7 = 12
	printf("Total text size: %d\n", totalTextSize(fs));
	
	FsFree(fs);
}

