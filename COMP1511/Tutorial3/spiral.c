//z5286124 Jinghan Wang

#include <stdio.h>



int main (void)
{
	int size;
	printf("Enter size: ");
	scanf("%d", &size);
	

	int line = 1;


	//line 1
	int line1 = 1;
	while (line1 <= size)
	{
		printf("*");
		line1 ++;
	}
	printf("\n");
	line ++;

	//line 2
	int line2 = 1;
	while (line2 < size)
	{
		printf("-");
		line2 ++;
	}
	printf("*\n");
	line ++;
	
	//The Middle line
	int lineMiddle = 1;
	while (line3 <= size - 2)
	{
		printf("*");
		line3 ++;
	}
	printf("-*\n");
	line ++;

	//line 4
	int line4 = 1;
	




	//the last line
	int lastline = 1;
	while (lastline <= size)
	{
		printf("*");
		lastline ++;
	}	
	printf("\n");




	return 0;
}
