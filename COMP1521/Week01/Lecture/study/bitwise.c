#include <stdio.h>
#include <stdint.h>

void print(char *ch, uint16_t value);
void print_bits(uint64_t value, int number);

int main (void) {
    uint16_t a = 0;
    uint16_t b;
    int c;

    printf("Enter a: ");
    scanf("%hd", &a);
    printf("Enter b: ");
    scanf("%hd", &b);
    printf("Enter c: ");
    scanf("%d", &c);

    print("     a = ", a);
    print("     b = ", b);
    print("    ~a = ", ~a);
    print(" a & b = ", a & b);
    print(" a | b = ", a | b);
    print(" a ^ b = ", a ^ b);
    print("a >> c = ", a >> c);
    print("a << c = ", a << c);
    return 0;

}

void print(char*ch, uint16_t value) {
    printf("%s", ch);
    print_bits(value, 8 * sizeof value);
    printf(" = 0x%04x = %d\n", value & 0xffff, value);
}

void print_bits(uint64_t value, int number) {
    for (int loop = number - 1; loop >= 0; loop --) {
        uint64_t uint64_value = value >> loop;
        int bit = uint64_value & 1;
        printf("%d", bit);
    }
}