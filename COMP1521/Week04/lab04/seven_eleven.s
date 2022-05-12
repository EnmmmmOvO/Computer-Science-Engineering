# Read a number and print positive multiples of 7 or 11 < n

main:                  # int main(void) {

    la   $a0, prompt   # printf("Enter a number: ");
    li   $v0, 4
    syscall

    li   $v0, 5         # scanf("%d", number);
    syscall

    li   $t0, 1         #i = 1;
    move   $t1, $v0     #number = scanf(...)

loop:
    bge   $t0, $t1, end #while (i < number)

    li   $t2, 7         #i % 7             
    div   $t0, $t2
    mfhi   $t2

    li   $t3, 11        #i % 11 
    div   $t0, $t3
    mfhi   $t3

    beqz   $t2, equal   #if (i % 7 == 0)
    beqz   $t3, equal   #if (i % 11 == 0)

    j   skip             

equal:
    move   $a0, $t0      # printf("%d", 'i');
    li   $v0, 1
    syscall

    li   $a0, '\n'       # printf("%c", '\n');
    li   $v0, 11
    syscall

skip:
    addi   $t0, $t0, 1   # i ++
    j   loop

end:
    jr   $ra           # return

    .data
prompt:
    .asciiz "Enter a number: "
