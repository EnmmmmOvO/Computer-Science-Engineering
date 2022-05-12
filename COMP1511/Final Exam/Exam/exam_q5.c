#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define MAX_LENGTH	(257)

char to_lower(char c) {
	if (c >= 'A' && c <= 'Z') {
		return c + ('a' - 'A');
	}
	return c;
}

int count_differences(char * s, char * t) {
	int len = strlen(s);
	int i;
	int differences = 0;
	for (i = 0; i < len; i++) {
		if (to_lower(s[i]) != to_lower(t[i])) {
			differences++;
		}
	}
	return differences;
}

int main(int argc, char *argv[]) {
    // you can always assume you will have exactly one command line argument.
    assert(argc == 2);

	char first[MAX_LENGTH];
	char second[MAX_LENGTH];

	scanf("%s", first);
	scanf("%s", second);

	int diffFirst = count_differences(first, argv[1]);
	int diffSecond = count_differences(second, argv[1]);

	if (diffFirst <= diffSecond) {
		printf("%d %s\n", diffFirst, first);
	} else {
		printf("%d %s\n", diffSecond, second);
	}

	return 0;
}
