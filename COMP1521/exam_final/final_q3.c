// COMP1521 21T2 ... final exam, question 3

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void
cp (char *path_from, char *path_to)
{
	FILE *r = fopen(path_from, "r");
	FILE *w = fopen(path_to, "w");
	
	while(1) {
		char bytes[4096];
		ssize_t bytes_read = fread(bytes, 4096, sizeof (char), r);
		if (bytes_read <= 0) {
			break;
		}
		fwrite(bytes, bytes_read, sizeof (char), w);
	}

}

