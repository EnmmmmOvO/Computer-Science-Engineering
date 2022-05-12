#include<stdio.h>
#include<string.h>
#define size 100000

int main()
{
   int i=0,j,k=0;
   char c[size],key[26],p[size],ch;

   while(i<strlen(c))
   {
       while(c[i]==' ')
       {
           p[k++]=c[i++];
       }
       for(j=0;j<26;j++)
           if(key[j]==c[i] || key[j]-32==c[i])
           {
               ch=j+97;
               break;
           }
       if(c[i]>='A' && c[i]<='Z')
           p[k++]=ch-32;
       else if(c[i]>='a' && c[i]<='z')
           p[k++]=ch;
       else
           p[k++]=c[i];
       i++;
   }
   printf("%s\n",p);
   return 0;
}
