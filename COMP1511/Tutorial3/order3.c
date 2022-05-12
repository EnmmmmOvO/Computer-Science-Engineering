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

	if (one >= two)
	{
		if (two >= three)
		{
			printf("The integers in order are: %d %d %d\n", three, two, one);
		} else 
		{	
			if (one <= three)
			{	
				printf("The integers in order are: %d %d %d\n", two, one, three);
			} else {
				printf("The integers in order are: %d %d %d\n", two, three, one);
			}
		}
	} else {	
		if (two <= three)
		{
			printf("The integers in order are: %d %d %d\n", one, two, three);
		} else 
		{
			if (one <= three)
			{		
				printf("The integers in order are: %d %d %d\n", one, three, two);
			} else {
				printf("The integers in order are: %d %d %d\n", three, one, two);
			}
		}
	}

	return 0;
}
