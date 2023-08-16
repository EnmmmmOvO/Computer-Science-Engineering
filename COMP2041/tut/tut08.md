<center><font size=6pt>Week 09 Tutorial Questions (Objectives)</font></center>

1. Discuss how Python can be generated for the supplied [examples](https://cgi.cse.unsw.edu.au/~cs2041/23T2/activities/sheepy/examples.html) for subsets 0-3

   > Discussed in tut. 

2. Discuss the assignment specification and possible strategies for the assignment.

   > Discussed in tut. 

3. Write a Python program, `tags.py` which given the URL of a web page fetches it by running [wget](https://manpages.debian.org/jump?q=wget.1) and prints the HTML tags it uses.

   The tag should be converted to lower case and printed in alphabetical order with a count of how often each is used.

   Don't count closing tags.

   Make sure you don't print tags within HTML comments.

   ```
   ./tags.py https://www.cse.unsw.edu.au
   a 141
   body 1
   br 14
   div 161
   em 3
   footer 1
   form 1
   h2 2
   h4 3
   h5 3
   head 1
   header 1
   hr 3
   html 1
   img 12
   input 5
   li 99
   link 3
   meta 4
   noscript 1
   p 18
   script 14
   small 3
   span 3
   strong 4
   title 1
   ul 25
   ```

   Note the counts in the above example will not be current - the CSE pages change almost daily.

   > ```python
   > #! /usr/bin/env python3
   > 
   > # written by Nasser Malibari and Dylan Brotherston
   > # fetch specified web page and count the HTML tags in them
   > 
   > import sys, re, subprocess
   > from collections import Counter
   > 
   > def main():
   > 
   >     if len(sys.argv) != 2:
   >         print(f"Usage: {sys.argv[0]} <url>", file=sys.stderr)
   >         sys.exit(1)
   > 
   >     url = sys.argv[1]
   > 
   >     process = subprocess.run(["wget", "-q", "-O-", url], capture_output=True, text=True)
   >     webpage = process.stdout.lower()
   > 
   >     # remove comments
   >     webpage = re.sub(r"<!--.*?-->", "", webpage, flags=re.DOTALL)
   > 
   >     # get all tags
   >     # note: use of capturing in re.findall returns list of the captured part
   >     tags = re.findall(r"<\s*(\w+)", webpage)
   > 
   >     # using collections.counter, alternatively can use a dict to count
   >     tags_counter = Counter()
   >     for tag in tags:
   >         tags_counter[tag] += 1
   > 
   >     for tag, counter in sorted(tags_counter.items()):
   >         print(f"{tag} {counter}")
   > 
   > if __name__ == "__main__":
   >     main()
   > ```

4. Add an `-f` option to `tags.py` which indicates the tags are to be printed in order of frequency.

   ```
   ./tags.py -f https://www.cse.unsw.edu.au
   head 1
   noscript 1
   html 1
   form 1
   title 1
   footer 1
   header 1
   body 1
   h2 2
   hr 3
   h4 3
   span 3
   link 3
   small 3
   h5 3
   em 3
   meta 4
   strong 4
   input 5
   img 12
   br 14
   script 14
   p 18
   ul 25
   li 99
   a 141
   div 161
   ```

   > ```python
   > #! /usr/bin/env python3
   > 
   > # written by Nasser Malibari and Dylan Brotherston
   > # fetch specified web page and count the HTML tags in them
   > 
   > import re, subprocess
   > from collections import Counter
   > from argparse import ArgumentParser
   > 
   > def main():
   > 
   >     parser = ArgumentParser()
   >     parser.add_argument('-f', '--frequency', action='store_true', help='print tags by frequency')
   >     parser.add_argument("url", help="url to fetch")
   >     args = parser.parse_args()
   > 
   >     process = subprocess.run(["wget", "-q", "-O-", args.url], capture_output=True, text=True)
   >     webpage = process.stdout.lower()
   > 
   >     # remove comments
   >     webpage = re.sub(r"<!--.*?-->", "", webpage, flags=re.DOTALL)
   > 
   >     # get all tags
   >     # note: use of capturing in re.findall returns list of the captured part
   >     tags = re.findall(r"<\s*(\w+)", webpage)
   > 
   >     # using collections.counter, alternatively can use a dict to count
   >     tags_counter = Counter()
   >     for tag in tags:
   >         tags_counter[tag] += 1
   > 
   >     if args.frequency:
   >         for tag, counter in reversed(tags_counter.most_common()):
   >             print(f"{tag} {counter}")
   >     else:
   >         for tag, counter in sorted(tags_counter.items()):
   >             print(f"{tag} {counter}")
   > 
   > if __name__ == "__main__":
   >     main()
   > ```

5. Modify tags.py to use the `requests` and `beautifulsoup4` modules.

   > ```python
   > #! /usr/bin/env python3
   > 
   > # written by Dylan Brotherston
   > # fetch specified web page and count the HTML tags in them
   > 
   > from collections import Counter
   > from argparse import ArgumentParser
   > 
   > import requests
   > from bs4 import BeautifulSoup
   > 
   > def main():
   > 
   >     parser = ArgumentParser()
   >     parser.add_argument('-f', '--frequency', action='store_true', help='print tags by frequency')
   >     parser.add_argument("url", help="url to fetch")
   >     args = parser.parse_args()
   > 
   >     response = requests.get(args.url)
   >     webpage = response.text.lower()
   > 
   >     soup = BeautifulSoup(webpage, 'html5lib')
   > 
   >     tags = soup.find_all()
   >     names = [tag.name for tag in tags]
   > 
   >     tags_counter = Counter()
   >     for tag in names:
   >         tags_counter[tag] += 1
   > 
   >     if args.frequency:
   >         for tag, counter in reversed(tags_counter.most_common()):
   >             print(f"{tag} {counter}")
   >     else:
   >         for tag, counter in sorted(tags_counter.items()):
   >             print(f"{tag} {counter}")
   > 
   > if __name__ == "__main__":
   >     main()
   > ```

6. If you fell like a harder challenge after finishing the challenge activity in the lab this week have a look at the following websites for some problems to solve using regexp:

   - https://regex101.com/quiz
   - https://alf.nu/RegexGolf