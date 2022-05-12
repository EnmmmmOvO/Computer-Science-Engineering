//
// DO NOT CHANGE THIS FILE
//
// You do not submit this file. This file is not marked.
// If you think you need to change this file you have
// misunderstood the assignment - ask in the course forum.
//
// Assignment 2 DPST1091: CS Pizzeria
// save_string.c
//
// You must not change this file.
//
// Version 1.0.0: Release

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h> // for mkdir()
#include "save_string.h"

#define MAX_SAVE_NAME_LENGTH 32
#define MAX_PATH_LENGTH 100
#define SAVE_DIRECTORY "saved_orders"

// Determine if a given character is alphanumeric (a-z, A-Z, 0-9).
// Returns 1 if it is, 0 otherwise.
static int is_alphanumeric(char c) {
    return (c >= 'a' && c <= 'z') ||
           (c >= 'A' && c <= 'Z') ||
           (c >= '0' && c <= '9');
}

// Return 1 if `name` is a valid save name, and 0 otherwise
// Valid names are [[ numbers, letteres, underscores, hyphens ]] ?
static int is_valid_save_name(char *name) {
    // Name can not be null
    if (name == NULL) {
        return 0;
    }

    // Is the string valid (so far)?
    int valid = 1;

    // Loop over string
    int i = 0;
    while (name[i] != 0) {
        char current = name[i];

        // If current character is not alphanumeric or '_'/'-', we will
        // mark this name as invalid
        if (!is_alphanumeric(current) && current != '_' && current != '-') {
            valid = 0;
        }

        i = i + 1;
    }

    // Check if string size is valid
    if (i == 0 || i > MAX_SAVE_NAME_LENGTH) {
        valid = 0;
    }

    return valid;
}

void save_string(char *name, char *string) {
    // Check input is valid before continuing
    if (!is_valid_save_name(name) || string == NULL) {
        return;
    }

    int length = strlen(string);

    // Create saved_tracks directory
    mkdir(SAVE_DIRECTORY, 0775);

    // Determine path to file
    char path[MAX_PATH_LENGTH];
    snprintf(path, MAX_PATH_LENGTH, "%s/%s.txt", SAVE_DIRECTORY, name);

    // Write the data to the file
    FILE *f = fopen(path, "wb");
    if (f) {
        fwrite(string, 1, length, f);
        fclose(f);
    }
}

char *load_string(char *name) {
    // Check name is valid before continuing
    if (!is_valid_save_name(name)) {
        return NULL;
    }

    // Determine path to file
    char path[MAX_PATH_LENGTH];
    snprintf(path, MAX_PATH_LENGTH, "%s/%s.txt", SAVE_DIRECTORY, name);

    // Open the file
    FILE *f = fopen(path, "rb");
    if (!f) {
        return NULL;
    }

    // Determine the length of the file
    fseek(f, 0, SEEK_END);
    int length = ftell(f);
    fseek(f, 0, SEEK_SET);

    // Allocate enough space for the string (+1 for null terminator)
    char *string = malloc(length + 1);
    if (string == NULL) {
        fclose(f);
        return NULL;
    }

    // Read file into malloc'd memory and add null terminator
    if (fread(string, 1, length, f) != length) {
        free(string);
        fclose(f);
        return NULL;
    }
    string[length] = 0;

    fclose(f);
    return string;
}
