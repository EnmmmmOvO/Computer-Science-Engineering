//z5286124 Jinghan Wang

#include <stdio.h>

char* lower(char *i){
	char *t = i;
	while (*t)
	{
		if (*t >= 65 && *t <= 90)
		{
			*t = *t + 32;
		}
		t ++;
	}
		return i;
}

char** change(char **i)
{
	while (*i)
	{
		lower(*i);
		i ++;
	}
	return i;
}

int main(int argc,char* argv[])
{
	change(argv);
	int loop = 1;
	while (loop < argc)
	{
		printf("%s",argv[loop]);
		printf(" ");
		loop ++;
	}
	printf("\n");

	return 0;
}
