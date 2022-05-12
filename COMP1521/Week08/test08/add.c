#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#include "add.h"

// return the MIPS opcode for add $d, $s, $t
uint32_t make_add(uint32_t d, uint32_t s, uint32_t t) {
    return (s << 21) | (t << 16) | (d << 11) | 32; // REPLACE WITH YOUR CODE
}
