//z5286124 Jinghan Wang







#include <stdio.h>
#include <stdlib.h>
#include <string.h>


int main(int argc, char *argv[]) 
{
	int ch;	
	if(argc == 2) 
	{
		if(strlen(argv[1]) == 26) 
		{
			while((ch = getchar()) != EOF) 
			{
				if(ch >= 'a' && ch <= 'z') 
				{
					ch = argv[1][ch-'a'];
				}
				if(ch >= 'A' && ch <= 'Z') 
				{
					ch = ch + 32;
					ch = argv[1][ch-'a'];
					ch = ch - 32;
				}
				printf("%c", ch);
			}
		}
	}
  
	return 0;
}

