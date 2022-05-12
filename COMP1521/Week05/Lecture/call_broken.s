main:
    la   $a0, string0
    li   $v0, 4
    syscall

    sub   $sp, $sp, 4
    sw   $ra, 0($sp)

    jal   f

    lw   $ra, 0($sp)
    addi   $sp, $sp, 4

    la   $a0, string1
    li   $v0, 4
    syscall

    li   $v0, 0
    jr   $ra

f:
    la   $a0, string1
    li   $v0, 4
    syscall

    jr   $ra


.data
string0:  .asciiz "calling function f \n"
string1:  .asciiz "back from function f \n"
string2:  .asciiz "in function f \n"
