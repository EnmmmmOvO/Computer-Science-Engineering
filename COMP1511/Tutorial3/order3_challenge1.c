//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int one;
	int two;
	int three;

	printf("Enter integer: ");
	scanf("%d", &one);
	printf("Enter integer: ");
	scanf("%d", &two);
	printf("Enter integer: ");
	scanf("%d", &three);

	int numberA = (one >= two) ? one:two;
	int numberB = (one < two) ? one:two;

	int max = (three >= numberA) ? three:numberA;
	int min = (three < numberB) ? three:numberB;
	int mid = one + two + three - max -min;

	printf("The integers in order are: %d %d %d\n", min, mid, max);
	return 0;

}
	
