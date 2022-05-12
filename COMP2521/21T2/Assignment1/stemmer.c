// COMP2521 21T2 Assignment 1
// stemmer.c ... Porter stemming algorithm

// !!! DO NOT MODIFY THIS FILE !!!

// Author: Martin Porter
// From: tartarus.org
// Does not follow our style guidelines

/* This is the Porter stemming algorithm, coded up in ANSI C by the
   author. It may be be regarded as cononical, in that it follows the
   algorithm presented in

   Porter, 1980, An algorithm for suffix stripping, Program, Vol. 14,
   no. 3, pp 130-137,

   only differing from it at the points marked --DEPARTURE-- below.

   The algorithm as described in the paper could be exactly replicated
   by adjusting the points of DEPARTURE, but this is barely necessary,
   because (a) the points of DEPARTURE are definitely improvements, and
   (b) no encoding of the Porter stemmer I have seen is anything like
   as exact as this version, even with the points of DEPARTURE!

   The algorithm as encoded here is particularly fast.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TRUE  1
#define FALSE 0

/* The main part of the stemming algorithm starts here. b is a buffer
   holding a word to be stemmed. The letters are in b[k0], b[k0+1] ...
   ending at b[k]. k is readjusted downwards as the stemming progresses.
   Zero termination is not in fact used in the algorithm.

   Note that only lower case sequences are stemmed. Forcing to lower case
   should be done before stem(...) is called.
*/

static char *b;      /* buffer for word to be stemmed */
static int k, k0, j; /* j is a general offset into the string */

/* cons(i) is TRUE <=> b[i] is a consonant. */

static int cons(int i)
{  switch (b[i])
   {  case 'a': case 'e': case 'i': case 'o': case 'u': return FALSE;
      case 'y': return (i == k0) ? TRUE : !cons(i - 1);
      default: return TRUE;
   }
}

/* m() measures the number of consonant sequences between k0 and j. if c is
   a consonant sequence and v a vowel sequence, and <..> indicates arbitrary
   presence,

      <c><v>       gives 0
      <c>vc<v>     gives 1
      <c>vcvc<v>   gives 2
      <c>vcvcvc<v> gives 3
      ....
*/

static int m()
{  int n = 0;
   int i = k0;
   while (TRUE)
   {  if (i > j) return n;
      if (!cons(i)) break;
      i++;
   }
   i++;
   while (TRUE)
   {  while (TRUE)
      {  if (i > j) return n;
         if (cons(i)) break;
         i++;
      }
      i++;
      n++;
      while (TRUE)
      {  if (i > j) return n;
         if (!cons(i)) break;
         i++;
      }
      i++;
   }
}

/* vowelinstem() is TRUE <=> k0,...j contains a vowel */

static int vowelinstem()
{  int i;
   for (i = k0; i <= j; i++) if (!cons(i)) return TRUE;
   return FALSE;
}

/* doublec(i) is TRUE <=> i, (i - 1) contain a double consonant. */

static int doublec(int i)
{  if (i < k0 + 1) return FALSE;
   if (b[i] != b[i - 1]) return FALSE;
   return cons(i);
}

/* cvc(i) is TRUE <=> i - 2, i - 1, i has the form consonant - vowel - consonant
   and also if the second c is not w,x or y. this is used when trying to
   restore an e at the end of a short word. e.g.

      cav(e), lov(e), hop(e), crim(e), but
      snow, box, tray.

*/

static int cvc(int i)
{  if (i < k0 + 2 || !cons(i) || cons(i - 1) || !cons(i - 2)) return FALSE;
   {  int ch = b[i];
      if (ch == 'w' || ch == 'x' || ch == 'y') return FALSE;
   }
   return TRUE;
}

/* ends(s) is TRUE <=> k0,...k ends with the string s. */

static int ends(char *s)
{  int length = s[0];
   if (s[length] != b[k]) return FALSE; /* tiny speed-up */
   if (length > k - k0 + 1) return FALSE;
   if (memcmp(b + k - length + 1, s + 1, length) != 0) return FALSE;
   j = k - length;
   return TRUE;
}

/* setto(s) sets (j+1),...k to the characters in the string s, readjusting
   k. */

static void setto(char *s)
{  int length = s[0];
   memmove(b + j + 1, s + 1, length);
   k = j + length;
}

/* r(s) is used further down. */

static void r(char * s) { if (m() > 0) setto(s); }

/* step1ab() gets rid of plurals and -ed or -ing. e.g.

       caresses  ->  caress
       ponies    ->  poni
       ties      ->  ti
       caress    ->  caress
       cats      ->  cat

       feed      ->  feed
       agreed    ->  agree
       disabled  ->  disable

       matting   ->  mat
       mating    ->  mate
       meeting   ->  meet
       milling   ->  mill
       messing   ->  mess

       meetings  ->  meet

*/

static void step1ab()
{  if (b[k] == 's')
   {  if (ends("\04" "sses")) k -= 2; else
      if (ends("\03" "ies")) setto("\01" "i"); else
      if (b[k - 1] != 's') k--;
   }
   if (ends("\03" "eed")) { if (m() > 0) k--; } else
   if ((ends("\02" "ed") || ends("\03" "ing")) && vowelinstem())
   {  k = j;
      if (ends("\02" "at")) setto("\03" "ate"); else
      if (ends("\02" "bl")) setto("\03" "ble"); else
      if (ends("\02" "iz")) setto("\03" "ize"); else
      if (doublec(k))
      {  k--;
         {  int ch = b[k];
            if (ch == 'l' || ch == 's' || ch == 'z') k++;
         }
      }
      else if (m() == 1 && cvc(k)) setto("\01" "e");
   }
}

/* step1c() turns terminal y to i when there is another vowel in the stem. */

static void step1c() { if (ends("\01" "y") && vowelinstem()) b[k] = 'i'; }


/* step2() maps double suffices to single ones. so -ization ( = -ize plus
   -ation) maps to -ize etc. note that the string before the suffix must give
   m() > 0. */

static void step2()
{  switch (b[k - 1])
   {  case 'a': if (ends("\07" "ational")) { r("\03" "ate");  break; }
                if (ends("\06" "tional"))  { r("\04" "tion"); break; }
                break;
      case 'c': if (ends("\04" "enci"))    { r("\04" "ence"); break; }
                if (ends("\04" "anci"))    { r("\04" "ance"); break; }
                break;
      case 'e': if (ends("\04" "izer"))    { r("\03" "ize");  break; }
                break;
      case 'l': if (ends("\03" "bli"))     { r("\03" "ble");  break; } /*-DEPARTURE-*/

 /* To match the published algorithm, replace this line with
    case 'l': if (ends("\04" "abli")) { r("\04" "able"); break; } */

                if (ends("\04" "alli"))    { r("\02" "al");   break; }
                if (ends("\05" "entli"))   { r("\03" "ent");  break; }
                if (ends("\03" "eli"))     { r("\01" "e");    break; }
                if (ends("\05" "ousli"))   { r("\03" "ous");  break; }
                break;
      case 'o': if (ends("\07" "ization")) { r("\03" "ize");  break; }
                if (ends("\05" "ation"))   { r("\03" "ate");  break; }
                if (ends("\04" "ator"))    { r("\03" "ate");  break; }
                break;
      case 's': if (ends("\05" "alism"))   { r("\02" "al");   break; }
                if (ends("\07" "iveness")) { r("\03" "ive");  break; }
                if (ends("\07" "fulness")) { r("\03" "ful");  break; }
                if (ends("\07" "ousness")) { r("\03" "ous");  break; }
                break;
      case 't': if (ends("\05" "aliti"))   { r("\02" "al");   break; }
                if (ends("\05" "iviti"))   { r("\03" "ive");  break; }
                if (ends("\06" "biliti"))  { r("\03" "ble");  break; }
                break;
      case 'g': if (ends("\04" "logi"))    { r("\03" "log");  break; } /*-DEPARTURE-*/

 /* To match the published algorithm, delete this line */
   }
}

/* step3() deals with -ic-, -full, -ness etc. similar strategy to step2. */

static void step3()
{  switch (b[k])
   {  case 'e': if (ends("\05" "icate")) { r("\02" "ic"); break; }
                if (ends("\05" "ative")) { r("\00" "");   break; }
                if (ends("\05" "alize")) { r("\02" "al"); break; }
                break;
      case 'i': if (ends("\05" "iciti")) { r("\02" "ic"); break; }
                break;
      case 'l': if (ends("\04" "ical"))  { r("\02" "ic"); break; }
                if (ends("\03" "ful"))   { r("\00" "");   break; }
                break;
      case 's': if (ends("\04" "ness"))  { r("\00" "");   break; }
                break;
   }
}

/* step4() takes off -ant, -ence etc., in context <c>vcvc<v>. */

static void step4()
{  switch (b[k - 1])
   {  case 'a': if (ends("\02" "al"))    break;
                return;
      case 'c': if (ends("\04" "ance"))  break;
                if (ends("\04" "ence"))  break;
                return;
      case 'e': if (ends("\02" "er"))    break;
                return;
      case 'i': if (ends("\02" "ic"))    break;
                return;
      case 'l': if (ends("\04" "able"))  break;
                if (ends("\04" "ible"))  break;
                return;
      case 'n': if (ends("\03" "ant"))   break;
                if (ends("\05" "ement")) break;
                if (ends("\04" "ment"))  break;
                if (ends("\03" "ent"))   break;
                return;
      case 'o': if (ends("\03" "ion") && (b[j] == 's' || b[j] == 't')) break;
                if (ends("\02" "ou"))    break;
                return;
                /* takes care of -ous */
      case 's': if (ends("\03" "ism"))   break;
                return;
      case 't': if (ends("\03" "ate"))   break;
                if (ends("\03" "iti"))   break;
                return;
      case 'u': if (ends("\03" "ous"))   break;
                return;
      case 'v': if (ends("\03" "ive"))   break;
                return;
      case 'z': if (ends("\03" "ize"))   break;
                return;
      default:  return;
   }
   if (m() > 1) k = j;
}

/* step5() removes a final -e if m() > 1, and changes -ll to -l if
   m() > 1. */

static void step5()
{  j = k;
   if (b[k] == 'e')
   {  int a = m();
      if (a > 1 || (a == 1 && !cvc(k - 1))) k--;
   }
   if (b[k] == 'l' && doublec(k) && m() > 1) k--;
}

/* In stem(p, l, r), p is a char pointer, and the string to be stemmed is from
   p[l] to p[r] inclusive. Typically l is zero and r is the offset to the last
   character of a string, (p[r + 1] == '\0'). The stemmer adjusts the
   characters p[l] ... p[r].
*/

void stem(char *p, int l, int r)
{  b = p; k = r; k0 = l; /* copy the parameters into statics */
   if (k <= k0 + 1) return; /*-DEPARTURE-*/

   /* With this line, strings of length 1 or 2 don't go through the
      stemming process, although no mention is made of this in the
      published algorithm. Remove the line to match the published
      algorithm. */

   step1ab(); step1c(); step2(); step3(); step4(); step5();
   p[k + 1] = '\0';
}

