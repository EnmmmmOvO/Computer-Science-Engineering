#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Word.h"

typedef struct content *Content;

struct url {
    double weight;
    int time;
    char code[MAX_SIZE];
};

struct word {
    int num;
    char word[MAX_SIZE];
    Url *link;
};

struct graph {
    int numWord;
    int numUrl;      
    Word *word;
    Url *url; 
};

Graph GraphNew() {
    Graph g = malloc(sizeof(g));
    if (g == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    g->numWord = 0;
    g->numUrl = 0;
    return g;
}

Url urlNew(char *c, double w) {
    Url u = malloc(sizeof(u));
    if (u == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    u->weight = w;
    u->time = 0;
    for (int loop = 0; c[loop] != '\0'; loop++) u->code[loop] = c[loop];
    return u;
}

void inputUrl(Graph g, char *code, double w) {
    g->numUrl++;
    Url *temp = malloc(sizeof(Url) * g->numUrl);
    for (int loop = 0; loop < g->numUrl; loop++) {
        if (loop == g->numUrl - 1) {
            temp[loop] = urlNew(code, w);
            break;
        }
        temp[loop] = g->url[loop];
    }
    free(g->url);
    g->url = temp;
}

void inputLine(Graph g, char *line) {
    g->numWord++;
    
    Word w = malloc(sizeof(Word));
    w->num = 0;
    int loop = 0;
    for (; line[loop] != ' '; loop++) {
        w->word[loop] = line[loop];
    } 
    w->word[loop] = '\0';

    for (; line[loop] != '\0'; loop++) {
        if (line[loop] == ' ') continue;
        if (line[loop] == '\n' || line[loop] == '\r') break;
        if (line[loop] == 'u' && line[loop + 1] == 'r' && line[loop+ 2] == 'l') {
            loop += 3;
            int loopA = 0;
            w->num++;
            Url u = malloc(sizeof(Url));
            for (; line[loop] >= '0' && line[loop] <= '9'; loopA++, loop++) {
                u->code[loopA] = line[loop];
            }
            u->code[loopA] = '\0';
            Url *temp = malloc(sizeof(Url) * w->num);
            for (int loopB = 0; loopB < w->num - 1; loopB++) {
                temp[loopB] = w->link[loopB];
            }
            temp[w->num - 1] = u;
            free(w->link);
            w->link = temp;
            continue;
        }
    }

    Word *tempWord = malloc(sizeof(Word) * g->numWord);
    for (int loopC = 0; loopC <g->numWord - 1; loopC++) {
        tempWord[loopC] = g->word[loopC];
    }
    tempWord[g->numWord - 1] = w;
    free(g->word);
    g->word = tempWord;
}

void search(Graph g, char *c) {
    for (int loop = 0; loop < g->numWord; loop++) {
        if (strcmp(c, g->word[loop]->word) == 0) {
            for (int loopA = 0; loopA < g->word[loop]->num; loopA){
                g->word[loop]->link[loopA]->time++;
            }
        }
    }
}

bool compare(Url a, Url b) {
    if (a->time != b->time) return a->time - b->time;
    if (a->weight != b->weight) return a->weight - b->weight;
    return strcmp(a->code, b->code);
}

void print(Graph g) {
    for (int i = 0; i < g->numUrl; i++) {
        for (int j = i; j < g->numUrl; j++) {
            if (compare(g->url[i], g->url[j]) > 0) {
                Url temp = g->url[i];
                g->url[j] = g->url[i];
                g->url[i] = temp;
            }
        }
    }

    int end = 0;
    for (int loop = g->numUrl - 1; loop >= 0 && end < 30; loop--) {
        printf("%s\n", g->url[loop]->code);
        end++;
    }

}