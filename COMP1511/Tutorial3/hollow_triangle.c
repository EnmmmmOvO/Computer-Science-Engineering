//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int size;
	printf("Enter size: ");
	scanf("%d", &size);	

	int line = 1;
	printf("*\n");
	line = line + 1;
	printf("**\n");
	line = line + 1;

	
	while (line < size)
	{	
		printf("*");
		int variableA = 1;
		while (variableA <= line - 2)
		{	
			printf(" ");
			variableA ++;
		}
		printf("*\n");
		line ++;
	}
	
	int variableB = 1;
	while (variableB <= size)
	{
		printf("*");
		variableB ++;
	}
	printf("\n");
	return 0;

}
