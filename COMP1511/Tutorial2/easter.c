//Z5286124 Jinghan Wang

#include <stdio.h>

int main (void)
{
	int year;
	printf("Enter year: ");
	scanf("%d", &year);

	int algebraA = year % 19;
	int algebraB = year / 100;
	int algebraC = year % 100;
	int algebraD = algebraB / 4;
	int algebraE = algebraB % 4;
	int algebraF = (algebraB + 8) / 25;
	int algebraG = (algebraB - algebraF + 1) / 3;
	int algebraH = (19 * algebraA + algebraB - algebraD - algebraG + 15) % 30;
	int algebraI = algebraC / 4;
	int algebraK = algebraC % 4;
	int algebraL = (32 + 2 * algebraE + 2 * algebraI - algebraH - algebraK) % 7;
	int algebraM = (algebraA + 11 * algebraH + 22 * algebraL) / 451;
	int easterMonth = (algebraH + algebraL - 7 * algebraM + 114) / 31;
	int algebraP = (algebraH + algebraL - 7 * algebraM + 114) % 31;
	int eaterDate = algebraP + 1;

	if (easterMonth == 3)
	{
		printf("Easter is March %d ", eaterDate);
	}
	if (easterMonth == 4)
	{
		printf("Easter is April %d ", eaterDate);
	}

	printf("in %d.\n", year);
	
	return 0;
}


