#include <stdio.h>
#include <stdint.h>

typedef uint64_t set;

#define EMPTY_SET 0

set set_read(char *ch);
void print_bits_hex(set a, char *ch);
void print_bits(set a);
void print_set(set a, char *ch);
void print_union(set a, set b);
void print_intersection(set a, set b);
void cardinality(set a, char *ch);
void is_member(int position, set a, char *ch);


int main (int argc, char *argv[]) {
    printf("Set members can be 0-63, negative number to finish\n");
    set a = set_read("a");
    set b = set_read("b");
    print_bits_hex(a, "a");
    print_bits_hex(b, "b");
    print_set(a, "a");
    print_set(b, "b");
    print_union(a, b);
    print_intersection(a, b);
    cardinality(a, "a");
    is_member(32, a, "a");
    return 0;
}

set set_read(char *ch) {
    printf("Enter set %s: ", ch);
    set a = EMPTY_SET;
    int value;
    while (scanf("%d", &value) == 1 && value >= 0) {
        a = a | ((set)1 << value);
    } 
    return a;
}

void print_bits_hex(set a, char *ch) {
    printf("%s = ", ch);
    print_bits(a);
    printf(" = 0x%08jx = %jd\n", (intmax_t)a, (intmax_t)a);
}

void print_bits(set a) {
    for (int loop = 63; loop >= 0; loop --) {
        int value = (a >> loop) & 1;
        printf("%d", value);
    }
}

void print_set(set a, char *ch) {
    printf("%s = {", ch);
    for (int loop = 0, temp = 0; loop < 64; loop ++) {
        if (((a >> loop) & 1) == 1) {
            if (temp == 0) {
                temp = 1;
            } else {
                printf(",");
            }
            printf("%d", loop);
        }
    }
    printf("}\n");
}

void print_union(set a, set b) {
    uint64_t value = a | b;
    print_set(value, "a union b");
}

void print_intersection(set a, set b) {
    uint64_t value = a & b;
    print_set(value, "a intersection b");
}

void cardinality(set a, char *ch) {
    printf("cardinality(%s) = ", ch);
    int time = 0;
    for (int loop = 0; loop < 64; loop ++) {
        if (((a >> loop) & 1) == 1) 
            time ++;                   
    }
    printf("%d\n", time);
}

void is_member(int position, set a, char *ch) {
    int value = (a >> position) & 1;
    printf("is_member(%d, %s) = %d\n", position, ch, value);
}
