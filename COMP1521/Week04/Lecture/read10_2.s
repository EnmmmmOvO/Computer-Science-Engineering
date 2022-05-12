main:
    li   $s0, 0               # int i = 0

loop_scanf: 
    la   $a0, string1          # printf("Enter a number: ")
    li   $v0, 4
    syscall
    
    li   $v0, 5               # scanf("%d", &number[i])
    syscall
    
    mul   $t1, $s0, 4
    la   $t2, numbers
    add   $t3, $t1, $t2
    sw   $v0, ($t3)

    addi   $s0, $s0, 1         # i ++

    blt   $s0, 10, loop_scanf  # if (i < 10) goto loop_scanf

print:
    la   $a0, string2           # printf("Reverse order: ")
    li   $v0, 4
    syscall

    li   $s0, 9                # i = 9

loop_printf:
    mul   $t1, $s0, 4          # printf("%d\n", numbers[i])
    la   $t2, numbers
    add   $t3, $t1, $t2
    lw   $a0, ($t3)
    li   $v0, 1
    syscall

    li   $a0, ' '
    li   $v0, 11
    syscall

    addi   $s0, $s0, -1         # i ++

    bge   $s0, 0, loop_printf  # if (i < 10) goto loop_printf

end:
    li   $a0, '\n'
    li   $v0, 11
    syscall

    li   $v0, 0
    jr   $ra

.data
numbers:  .word 0 0 0 0 0 0 0 0 0 0
string1:  .asciiz "Enter a number: "
string2:  .asciiz "Reverse order: "