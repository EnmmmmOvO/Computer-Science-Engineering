#include <stdio.h>
#include <stdint.h>
#include "print_bits.h"


#define POKEMON_TYPE_BITS 16

#define FIRE_TYPE      0x0001
#define FIGHTING_TYPE  0x0002
#define WATER_TYPE     0x0004
#define FLYING_TYPE    0x0008
#define POISON_TYPE    0x0010
#define ELECTRIC_TYPE  0x0020
#define GROUND_TYPE    0x0040
#define PSYCHIC_TYPE   0x0080
#define ROCK_TYPE      0x0100
#define ICE_TYPE       0x0200
#define BUG_TYPE       0x0400
#define DRAGON_TYPE    0x0800
#define GHOST_TYPE     0x1000
#define DARK_TYPE      0x2000
#define STEEL_TYPE     0x4000
#define FAIRY_TYPE     0x8000

int main(void) {

    // example code to create a pokemon with 3 types

    uint16_t our_pokemon = BUG_TYPE | POISON_TYPE | FAIRY_TYPE;

    print_bits(BUG_TYPE, POKEMON_TYPE_BITS);
    printf(" BUG_TYPE\n");
    print_bits(POISON_TYPE, POKEMON_TYPE_BITS);
    printf(" POISON_TYPE\n");
    print_bits(FAIRY_TYPE, POKEMON_TYPE_BITS);
    printf(" FAIRY_TYPE\n");

    print_bits(our_pokemon, POKEMON_TYPE_BITS);
    printf(" our_pokemon type (1)\n");

    // example code to check if a pokemon is of a type:

    if (our_pokemon & POISON_TYPE) {
        printf("Poisonous\n"); // prints
    }

    if (our_pokemon & GHOST_TYPE) {
        printf("Scary\n"); // does not print
    }

    // example code to add a type to a pokemon
    our_pokemon |= GHOST_TYPE;

    // example code to remove a type from a pokemon
    our_pokemon &= ~ POISON_TYPE;

    print_bits(our_pokemon, POKEMON_TYPE_BITS);
    printf(" our_pokemon type (2)\n");

    if (our_pokemon & POISON_TYPE) {
        printf("Poisonous\n"); // does not print
    }

    if (our_pokemon & GHOST_TYPE) {
        printf("Scary\n"); // prints
    }
    return 0;
}