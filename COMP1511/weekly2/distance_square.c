//z5286124 Jinghan Wang

#include <stdio.h>



int main (void)
{
	int size;
	printf("Enter square size: ");
	scanf("%d", &size);

	int line = 1;
	int row = 1;
	int start_value = size - 1;
	
	while (line < (size + 1) / 2)
	{
		while (row <= size)
		{
			if (row < (size + 1) / 2)
			{
				printf("%d", start_value);
				start_value = start_value - 1;
			} else
			{
				printf("%d", start_value);
				start_value = start_value + 1;
			}
			row ++;
		}
		printf("\n");
		row = 1;
		start_value = start_value - 2; 
		line ++;
	}

	while (line <= size)
	{
		while (row <= size)
			{
			if (row < (size + 1) / 2)
			{
				printf("%d", start_value);
				start_value = start_value - 1;
			} else
			{
				printf("%d", start_value);
				start_value = start_value + 1;
			}
			row ++;
		}
		printf("\n");
		row = 1;
		line ++;
	}

	return 0;
}
