 //z5286124 Jinghan Wang

#include <stdio.h>



int main (void)
{
	int size;
	printf("Enter size: ");
	scanf("%d", &size);
	

	int line = 1;
	int column = 1;
	while (line <= size)
	{	
		if (line == 1 || line == size)
		{	
			while (column <= size)
			{
				printf("*");
				column ++;
			}
			printf("\n");
			column = 1;
		} else
		{
			while (line < size)
			{				
				while (column <= size)
				{	
					if (column == 1||column == size);
					{
						printf("*");
					} else 
					{
						if(line 
			while (column < size)
			{
				printf("-");
				column ++;
			}
			printf("*\n");
			column = 1;
		}

		printf("\n");
		line ++;
	}


	return 0;
}
