# read a line and print its length

main:
    la   $a0, str0       # printf("Enter a line of input: ");
    li   $v0, 4
    syscall

    la   $a0, line
    la   $a1, 256
    li   $v0, 8          # fgets(buffer, 256, stdin)
    syscall              #

    li   $t0, 1          # int i = 0;

    lb   $t1, line       # int temp = line[0]
loop:
    beq   $t1, 0, end    # while (line[i] != 0) {

    addi   $t0, $t0, 1   #     i++;
    lb   $t1, line($t0)  
    j   loop             # }

end:
    la   $a0, str1       # printf("Line length: ");
    li   $v0, 4
    syscall

    move   $a0, $t0         # printf("%d", i);
    li   $v0, 1
    syscall

    li   $a0, '\n'       # printf("%c", '\n');
    li   $v0, 11
    syscall

    li   $v0, 0          # return 0
    jr   $ra


.data
str0:
    .asciiz "Enter a line of input: "
str1:
    .asciiz "Line length: "


# line of input stored here
line:
    .space 256

