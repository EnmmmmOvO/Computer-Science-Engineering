## Use NodeJS and an NPM library to solve a uuid problem

In this exercise we will set up an NPM package, install some modules, and then write a nodejs file that uses them, before minifying our code.

1. Run `npm init`. This will create an NPM package in this folder.

2. Install the `uuid` dependency by running `npm install uuid`. This installs the `uuid` library, which allows you to generate (UUIDs)[https://en.wikipedia.org/wiki/Universally_unique_identifier].

3. Open the file `ids.js`. Modify the file so that when you run `node ids.js`, it outputs 30 randomly generated UUIDs in sorted order, one on each line.

4. After that, print out up the 5 most commonly occuring characters (not including dashes) across ALL of the generate UUIDs. If there are ties (e.g. 6 characters that are equal 3rd), you're allowed to print out more than 5 characters. 

5. Once you have your program working, run `npm install minify` which installs a node based program that allows you to *minify* your code (remove all unnecessary whitespace - usually something we do to code before deploying it. Once code is deployed performance is more important than readability). You can run `npx minify ids.js > ids.min.js`.

An example output is below:
```txt
00d0a144-4837-4f0b-94c2-f274281c8f7e
020c23f9-592a-496a-8d34-febd9940ef74
0c6220ec-d751-4de0-8675-ebaee2a50e26
11f4b97e-7e22-43d7-a9ec-2734fcbe0758
1a115013-fa63-4c96-aaf4-09169d3bfe80
22430824-83c2-4dfd-b5d3-5ad19bca04a0
22acbcbb-8498-4c0b-982d-9c2e1afad624
27967738-10a6-4185-b604-21cc36f01671
2c49fa91-fdb6-4965-bc14-1011cc6c812f
375c1404-33b3-4a35-ad79-dd6ae6fe0f82
3a945cd3-9a9b-4163-9fff-58aefdb3c1d1
43f21a44-49ab-4f4f-852e-e7734fda2b37
47a804e3-c94a-43a4-84df-1a49e7e13058
59340457-3e91-417f-a8b1-746716a508ff
5b7c6b55-d769-46fd-a1d7-9e6cd6709cf8
61ba1338-5c81-495d-9378-e4d0e2f2e8f5
67e7c2c7-fb7f-40e1-8d53-47293fe42fe8
69073023-a72d-4ded-8540-5a80c16666a9
6c1154bb-59e5-4088-8a16-c68165fd2a81
804f39a0-76f5-476b-ba1d-9c020d41ae6c
871db203-529b-4ab3-ab2f-17ea74967b00
8f6e40ca-0675-48f2-84b3-caf8c64e0097
b42e10ce-84da-4d97-b3dd-53e3429d9c86
c048a5ad-a966-4cb8-89fd-df02a7a93497
d1e3fafd-34be-4bac-ab45-566a6ab1c91d
d450737c-e4ad-402c-8700-1e62ff754d0f
d71b3288-ac95-4802-83f7-cfbc98600054
d814e1ca-fbef-4fe2-a7cd-790be73d4d7b
d82166b9-a2b7-4d10-9b0d-3436d9d822c9
fb14997c-831d-4715-a4ea-55c12ed34a4f
4 a 0 1 d
```