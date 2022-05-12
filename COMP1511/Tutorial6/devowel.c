//z5286124 Jinghan Wang
#include <stdio.h>

int main(void) 
{
	int c = getchar();
	while (c != EOF) 
	{
		if (c != 'a' && c != 'e' && c != 'i' && c != 'o' && c != 'u') 
		{
			putchar(c);
		}
		c = getchar();
	}
	return 0;
}
