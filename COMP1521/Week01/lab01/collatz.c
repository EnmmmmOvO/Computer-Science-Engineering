//Jinghan Wang
//z5286124

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv)
{
	int number = strtol(argv[1], NULL, 10);
	while (number != 1) {
		printf("%d\n", number);
		if (number % 2 == 0) {
			number = number / 2;
		} else {
			number = 3 * number + 1;
		}
	}
	printf("%d\n", number);
	return 0;
}
