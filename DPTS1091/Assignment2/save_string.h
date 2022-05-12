//
// DO NOT CHANGE THIS FILE
//
// You do not submit this file. This file is not marked.
// If you think you need to change this file you have
// misunderstood the assignment - ask in the course forum.
//
// Assignment 2 DPST1091: CS Pizzeria
// save_string.h
//
// You must not change this file.
//
// Version 1.0.0: Release

#ifndef _SAVE_H_
#define _SAVE_H_

////////////////////////////////////////////////////////////////////////
//  SAVE STRING
//
// Save a string to disk calling it "name", overwriting anything already there
void save_string(char *name, char *string);

////////////////////////////////////////////////////////////////////////
//  LOAD STRING
//
// Return the string stored as "name" to the user.
// This string is allocated using malloc. The user has the responsibility to
// free it after use.
char *load_string(char *name);


#endif //  _SAVE_H_
