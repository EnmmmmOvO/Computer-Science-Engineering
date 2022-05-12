// COMP1521 21T2 ... final exam, question 5

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void
print_utf8_count (FILE *file)
{
	unsigned long amount_1_byte = 0;
	unsigned long amount_2_byte = 0;
	unsigned long amount_3_byte = 0;
	unsigned long amount_4_byte = 0;

	uint32_t p;
	while ((p = fgetc(file)) != EOF) {
		if (p >> 7 == 0) {
			amount_1_byte++;
		} else if ((p >> 5) == 0x06) {
			amount_2_byte++;
		} else if ((p >> 4) == 0x0e) {
			amount_3_byte++;
		} else if ((p >> 3) == 30) {
			amount_4_byte++;
		}
	}

	printf("1-byte UTF-8 characters: %lu\n", amount_1_byte);
	printf("2-byte UTF-8 characters: %lu\n", amount_2_byte);
	printf("3-byte UTF-8 characters: %lu\n", amount_3_byte);
	printf("4-byte UTF-8 characters: %lu\n", amount_4_byte);
}
