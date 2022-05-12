

#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Graph.h"
#define MAX_SIZE 100

typedef struct content *Content;

struct url {
    char code[MAX_SIZE];
    int line;
    int inLinkUrl;
    int outLinkUrl;
    char content[MAX_SIZE][MAX_SIZE];
    Url *inContact;
    Url *outContact;
    double *weight;
};

struct graph {
    int num;         
    Url *contact; 
                    
};


////////////////////////////////////////////////////////////////////////

Graph GraphNew() {
    Graph g = malloc(sizeof(*g));
    if (g == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    g->num = 0;
    return g;
}

Url UrlNew(char *c) {
    assert(c > 0);

    Url u = malloc(sizeof(*u));
    if (u == NULL) {
        fprintf(stderr, "error: out of memory\n");
        exit(EXIT_FAILURE);
    }
    for (int loop = 0; c[loop] != '\0'; loop++) u->code[loop] = c[loop];
    u->line = 0;
    u->inLinkUrl = 0;
    u->outLinkUrl = 0;
    return u;
}

void GraphFree(Graph g) {
    for (int i = 0; i < g->num; i++) {
        free(g->contact[i]->outContact);
        free(g->contact[i]->inContact);
        free(g->contact[i]->weight);
        free(g->contact[i]);
    }
    free(g->contact);
    free(g);
}

////////////////////////////////////////////////////////////////////////
void GraphUrlInsert(Graph g, char *code) {
    g->num++;
    Url *temp = malloc(sizeof(Url) * g->num);
    int loop;
    for (loop = 0; loop < g->num - 1; loop++) {
        temp[loop] = g->contact[loop];
    }
    temp[loop] = UrlNew(code);
    free(g->contact);
    g->contact = temp;
}

char *getUrlCode(Graph g, int loop) {
    return g->contact[loop]->code;
}

int GraphNumVertices(Graph g) {
    return g->num;
}

void UrlLink(Graph g, int loop, char *c) {
    for (int temp = 0; temp < g->num; temp++) {
        if (strcmp(g->contact[temp]->code, c) == 0) {
            g->contact[temp]->inLinkUrl++;

            //copy inContact
            Url *tempUrlA = malloc(sizeof(Url) * g->contact[temp]->inLinkUrl);;
            for (int loopA = 0; loopA < g->contact[temp]->inLinkUrl; loopA++) {
                if (loopA == g->contact[temp]->inLinkUrl - 1) { 
                    tempUrlA[loopA] = g->contact[loop];
                    break;
                }
                tempUrlA[loopA] = g->contact[temp]->inContact[loopA];
            }
            free(g->contact[temp]->inContact);
            g->contact[temp]->inContact = tempUrlA;
            
            Url u = g->contact[loop];
            u->outLinkUrl++;
            //copy outContact
            Url *tempUrl = malloc(sizeof(Url) * u->outLinkUrl);;
            for (int loopA = 0; loopA < u->outLinkUrl; loopA++) {
                if (loopA == u->outLinkUrl - 1) { 
                    tempUrl[loopA] = g->contact[temp];
                    break;
                }
                tempUrl[loopA] = u->outContact[loopA];
            }
            free(g->contact[loop]->outContact);
            g->contact[loop]->outContact = tempUrl;
        }
    }
}

void UrlContentInsert(Graph g, int loop, char urlContent[MAX_SIZE]) {
    for (int temp = 4; urlContent[temp] != '\r' && urlContent[temp + 1] != '\n'; temp++) {
        g->contact[loop]->content[g->contact[loop]->line][temp - 4] = urlContent[temp];
    }
    g->contact[loop]->line++;
}

void print(Graph g) {
    int p = 1;
    for (int a = 0; a < g->num; a++) {
        printf("%s: inLinks(%d): ", g->contact[a]->code, g->contact[a]->inLinkUrl);

        for (int loop = 0; loop < g->contact[a]->inLinkUrl; loop++) {
            printf("%s ", g->contact[a]->inContact[loop]->code);
        }

        printf("outLinks(%d): ", g->contact[a]->outLinkUrl);
        for (int loop = 0; loop < g->contact[a]->outLinkUrl; loop++) {
            printf("%s ", g->contact[a]->outContact[loop]->code);
        }

        printf("\n");
    }
}

////////////////////////////////////////////////////////////////////////

void setWeight(Graph g, double n) {
    for (int loop = 0; loop < g->num; loop++) {
        g->contact[loop]->weight = malloc(sizeof(double));
        g->contact[loop]->weight[0] = n;
    }
}

double getInLinkWithoutSelf(Url url) {
    for (int loopA = 0; loopA < url->inLinkUrl; loopA++) 
        if (url->inContact[loopA] == url) return url->inLinkUrl - 1;
    return url->inLinkUrl == 0 ? 0.5 : url->inLinkUrl;
}

double getOutLinkWithoutSelf(Url url) {
    for (int loopA = 0; loopA < url->outLinkUrl; loopA++) 
        if (url->outContact[loopA] == url) return url->outLinkUrl - 1;
    return url->outLinkUrl == 0 ? 0.5 : url->outLinkUrl;
}

double weightIn(Url urlA, Url urlB) {
    double numerator = getInLinkWithoutSelf(urlB);
    double temp = 0;
    for (int loop = 0; loop < urlA->outLinkUrl; loop++) {
        if (urlA->outContact[loop] == urlA) continue;
        temp += getInLinkWithoutSelf(urlA->outContact[loop]);
    }
    return numerator/temp;
}

double weightOut(Url urlA, Url urlB) {
    double numerator = getOutLinkWithoutSelf(urlB);
    double temp = 0;
    for (int loop = 0; loop < urlA->outLinkUrl; loop++) {
        if (urlA->outContact[loop] == urlA) continue;
        temp += getOutLinkWithoutSelf(urlA->outContact[loop]);
    }
    return numerator/temp;
}

double changeWeight(Graph g, int t, double d) {
    double diff = 0;
    for (int loopA = 0; loopA < g->num; loopA++) {
        double temp = 0;
        Url u = g->contact[loopA];
        for (int loopB = 0; loopB < u->outLinkUrl; loopB++) {
            if (u->outContact[loopB] == u) continue;
            temp += u->outContact[loopB]->weight[t] * weightIn(u, u->outContact[loopB]) * weightOut(u, u->outContact[loopB]);
        }
        temp = d * temp + ((1.0 - d) / g->num);
        double *tempList = malloc(sizeof(double) * (t + 2));
        for (int loop = 0; loop <= t + 1; loop++) {
            if (loop == t + 1) {
                tempList[loop] = temp;
                break;
            }
            tempList[loop] = u->weight[loop];
        }
        free(u->weight);
        u->weight = tempList;
    }

    for (int loop = 0; loop < g->num; loop++) {
        double temp = g->contact[loop]->weight[t + 1] - g->contact[loop]->weight[t];
        if (temp < 0) {
            diff -= temp;
        } else {
            diff += temp;
        }
    }
    return diff;
}

void printWeight(Graph g, int t) {
    double *temp = malloc(sizeof(double) * g->num);
    double max = 0;
    for (int loop = 0; loop < g->num; loop++) {
        temp[loop] = g->contact[loop]->weight[t];
    }
    
    for (int i = 0; i < g->num - 1; i++) {
        for (int j = i + 1; j < g->num; j++) {
            if (temp[i] > temp[j]) {
                double t = temp[i];
                temp[i] = temp[j];
                temp[j] = t;
            }
        }
    }

    for (int i = 0; i < g->num; i++) {
        for (int loop = g->num - 1; loop >= 0; loop--) {
            if (temp[loop] == g->contact[i]->weight[t]) {
                printf("url%s, %.0lf, %.7lf\n", g->contact[i]->code, getOutLinkWithoutSelf(g->contact[i]), temp[loop]);
                break;
            }
        }
    }
}




