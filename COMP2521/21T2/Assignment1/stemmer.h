// COMP2521 21T2 Assignment 1
// stemmer.h ... interface to stemming module

// !!! DO NOT MODIFY THIS FILE !!!

#ifndef STEMMER_H
#define STEMMER_H

// In stem(p, l, r), p is a char pointer, and the string to be stemmed is from
// p[l] to p[r] inclusive. Typically l is zero and r is the offset to the last
// character of a string, (p[r + 1] == '\0'). The stemmer adjusts the
// characters p[l] ... p[r].

void stem(char *p, int l, int r);

#endif
