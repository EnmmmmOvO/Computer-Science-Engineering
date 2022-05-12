#include <stdio.h>
#include <string.h>
//Caesar method
void encrypt(char str[], int key)
{
int i;
char c;
key=key%26;
if (key <0)
key=key+26;
// defining new character array
char s[200];
// Iterating in String
for(i = 0; str[i] != '\0'; ++i){
       c = str[i];
       // Lowercase check
       if(c >= 'a' && c <= 'z'){
           c = (char)((int)(str[i]+key-97)%26 +97);
       }
       //Upper case check
       else if(c >= 'A' && c <= 'Z'){
           c = (char)((int)(str[i]+key-65)%26 +65);
          
       }
       s[i]=c;
   }
   // Printing
   printf("%s", s);
}

// Driver function
int main()
{
int n;
// Character array
char s[200];
scanf("%d \n",&n);
// string Input
fgets(s, sizeof(s), stdin);
// method call
encrypt(s,n);

return 0;
}
