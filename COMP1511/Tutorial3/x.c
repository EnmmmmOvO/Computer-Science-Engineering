//z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int size;
	
	printf("Enter size: ");
	scanf("%d", &size);

	int line = 1;

	while (line < (size + 1) / 2)
	{
		int variableA = 1;
		int variableB = 1;
		int variableC = 1;

		while (variableA <= line - 1)
		{
			printf("-");
			variableA ++;
		}
		printf("*");
		while (variableB <= size - line * 2)
		{
			printf("-");
			variableB ++;
		}
		printf("*");
		while (variableC <= line - 1)
		{
			printf("-");
			variableC ++;
		}
		printf("\n");
		line ++;
	}

	int variableD = 1;
	while (variableD <= line - 1)
	{
		printf("-");
		variableD ++;
	}
	printf("*");
	int variableE = 1;
	while (variableE <= line - 1)
	{
		printf("-");
		variableE ++;
	}
	printf("\n");
	line = line + 1;

	int line2 = size + 1 - line;
	while (line2 >= 1)
	{
		int variableF = 1;
		int variableG = 1;
		int variableH = 1;

		while (variableF <= line2 - 1)
		{
			printf("-");
			variableF ++;
		}
		printf("*");
		while (variableG <= size - line2 * 2)
		{
			printf("-");
			variableG ++;
		}
		printf("*");
		while (variableH <= line2 - 1)
		{
			printf("-");
			variableH ++;
		}
		printf("\n");
		line2 = line2 - 1;
	}

	return 0;
}

