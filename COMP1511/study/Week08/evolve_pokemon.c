#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_NAME_SIZE 50

// Do not edit this struct. You may use it exactly as it is
// but you cannot make changes to it
struct pokemon {
    char name[MAX_NAME_SIZE];
    struct pokemon *evolution;
};

// Create a pokemon 
struct pokemon *create_pokemon(char name[MAX_NAME_SIZE]) {
    struct pokemon *p = malloc(sizeof(struct pokemon));
    int loop;
    for (loop = 0; loop < strlen(name); loop ++)
        p->name[loop] = name[loop];
    p->name[loop] = '\0';
    p->evolution = NULL; 
    return p;
}

// Link a pokemon to another that it evolves into
void evolve_pokemon(struct pokemon *base, struct pokemon *evolution) {
    base->evolution = evolution;
    evolution = NULL;
}

// Print out the evolution of a pokemon
void print_evolution(struct pokemon *p) {
    while (p != NULL) {
        printf("%s\n", p->name);
        p = p->evolution;
    }
}

// This is a simple main function which could be used
// to test your pokemon functions.
// It will not be marked.
// Only your pokemon functions will be marked.

int main(void) {
    struct pokemon *pikachu = create_pokemon("Pikachu");
    struct pokemon *raichu = create_pokemon("Raichu");
    evolve_pokemon(pikachu, raichu);
    print_evolution(pikachu);
    return 0;
}