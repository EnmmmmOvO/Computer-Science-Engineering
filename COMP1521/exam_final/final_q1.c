// COMP1521 21T2 ... final exam, question 1

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BITS 8

void
and (bool x[BITS], bool y[BITS], bool result[BITS])
{
	for (int loop = 0; loop < BITS; loop++)
		result[loop] = x[loop] & y[loop];
}

void
or (bool x[BITS], bool y[BITS], bool result[BITS])
{
	for (int loop = 0; loop < BITS; loop++)
		result[loop] = x[loop] | y[loop];
}

void
xor (bool x[BITS], bool y[BITS], bool result[BITS])
{
	for (int loop = 0; loop < BITS; loop++)
		result[loop] = x[loop] ^ y[loop];
}

void
not (bool x[BITS], bool result[BITS])
{
	for (int loop = 0; loop < BITS; loop++)
		result[loop] = !x[loop];
}
