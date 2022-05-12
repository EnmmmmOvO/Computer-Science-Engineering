// Tests for the Set ADT

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Set.h"

int main(void) {
	Set s;

	////////////////////////////////////////////////////////////////////
	
	printf("Test 1: Create set\n");

	s = SetNew();
	assert(s != NULL);
	assert(SetSize(s) == 0);

	printf("Passed\n");

	////////////////////////////////////////////////////////////////////

	printf("Test 2: Add to set\n");

	SetAdd(s, 4);
	assert(SetSize(s) == 1);
	assert(SetContains(s, 4) == true); // try number in set
	assert(SetContains(s, 6) == false); // try number not in set

	SetAdd(s, 2);
	assert(SetSize(s) == 2);
	assert(SetContains(s, 2) == true);
	assert(SetContains(s, 3) == false);

	SetAdd(s, 7);
	assert(SetSize(s) == 3);
	assert(SetContains(s, 7) == true);
	assert(SetContains(s, 9) == false);

	// try some other numbers
	assert(SetContains(s, 1) == false);
	assert(SetContains(s, 3) == false);
	assert(SetContains(s, 5) == false);
	assert(SetContains(s, 8) == false);

	printf("Passed\n");

	////////////////////////////////////////////////////////////////////

	printf("Test 3: Try to add duplicates\n");

	SetAdd(s, 4);
	SetAdd(s, 2);
	SetAdd(s, 7);
	assert(SetSize(s) == 3);

	printf("Passed\n");

	////////////////////////////////////////////////////////////////////

	printf("Test 4: Add more to set\n");
	
	SetAdd(s, 9);
	SetAdd(s, 6);
	
	assert(SetSize(s) == 5);
	assert(SetContains(s,  1) == false);
	assert(SetContains(s,  2) == true);
	assert(SetContains(s,  3) == false);
	assert(SetContains(s,  4) == true);
	assert(SetContains(s,  5) == false);
	assert(SetContains(s,  6) == true);
	assert(SetContains(s,  7) == true);
	assert(SetContains(s,  8) == false);
	assert(SetContains(s,  9) == true);
	assert(SetContains(s, 10) == false);

	printf("Passed\n");

	////////////////////////////////////////////////////////////////////

	printf("Test 5: Print set\n");
	
	SetPrint(s);
	
	printf("Check manually\n");

	////////////////////////////////////////////////////////////////////

	printf("Test 6: Free set\n");

	SetFree(s);

	////////////////////////////////////////////////////////////////////

	printf("Now check for memory errors and leaks using valgrind\n");
}
