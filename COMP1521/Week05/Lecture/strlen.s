main:
    addi   $sp, $sp, -4
    sw   $ra, 0($sp)

    la   $a0, string

    jal   my_strlen

    move   $a0, $v0, 
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    lw   $ra, 0($sp)
    addi   $sp, $sp, 4

    li   $v0, 0
    jr   $ra

my_strlen:
    li   $t0, 0

loop:
    add   $t1, $a0, $t0
    lb   $t2, 0($t1)
    beq   $t2, 0, end
    addi   $t0, $t0, 1
    j   loop

end:
    move   $v0, $t0
    jr   $ra


.data
string:
    .asciiz "Hello"