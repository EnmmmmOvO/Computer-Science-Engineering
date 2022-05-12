#include <stdio.h>
#define Totalnumber 10

int main (void) {
	int One;
	int Two;
	printf("Please type the first number:");
	scanf("%d", &One);
	printf("Please type the second number:");
	scanf("%d", &Two);
	int Total = One + Two;
	printf("Total number is: %d\n", Total);

	if (Total == Totalnumber) {
	printf("It is equal to default value\n");
	} else if (Total > Totalnumber) {
	printf("it is greater than default value\n");
	} else {
	printf("it is smaller than default value\n");
	}
	return 0;
}
