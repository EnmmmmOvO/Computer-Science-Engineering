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
	

	printf("The integers in order are: %d ", (one <= two) * (one <= three) * one
 + (two <= three) * (two < one) * two + (three <= one) * (three < two) * 
three );
	printf("%d ", one + two + three - ((one <= two) * (one <= three) * one + 
(two <= three) * (two < one) * two + (three <= one) * (three < two) * three ) - 
((one >= two) * (one > three) * one + (two >= three) * (two > one) * two + 
(three >= one) * (three >= two) * three) ); 
	printf("%d\n", (one >= two) * (one > three) * one + (two >= three) * 
(two > one) * two + (three >= one) * (three >= two) * three);
	return 0;
}
	
