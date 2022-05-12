# Read a number n and print the first n tetrahedral numbers
# https://en.wikipedia.org/wiki/Tetrahedral_number

main:                  # int main(void) {

    la   $a0, prompt   # printf("Enter how many: ");
    li   $v0, 4
    syscall

    li   $v0, 5         # scanf("%d", number);
    syscall

    move   $t0, $v0     # how_many = scanf("%d", number);
    li   $t1, 1         # n = 1

loop1:
    bgt   $t1, $t0, end # while (n <= how_many)
    li   $t2, 0         # total = 0
    li   $t3, 0         # j = 1

    j   loop2_1

loop2_1:
    bgt   $t3, $t1, print # while (j <= n)
    move   $a0, $t1     # Store the value of n
    li   $t1, 1         # i = 1
    
    j   loop3
    
loop2_2:
    addi   $t3, $t3, 1  # j ++
    move   $t1, $a0     # get the value of n

    j   loop2_1

loop3:
    bgt   $t1, $t3, loop2_2  # while (i <= j)
    add   $t2, $t2, $t1 # total = total + i
    addi   $t1, $t1, 1  # i ++

    j   loop3


print:
    move   $a0, $t2     # printf("%d", total);
    li   $v0, 1
    syscall

    li   $a0, '\n'      # printf("%c", '\n');
    li   $v0, 11
    syscall

    addi   $t1, $t1, 1    # n ++

    j   loop1

end:
    jr   $ra           # return

    .data
prompt:
    .asciiz "Enter how many: "
