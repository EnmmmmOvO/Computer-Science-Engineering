// COMP2521 Assignment 1

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef FILE_TYPE_H
#define FILE_TYPE_H

typedef enum {
    REGULAR_FILE,
    DIRECTORY,
} FileType;

void listFile(char *name, FileType type);

#endif

