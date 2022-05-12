main:
    addi   $sp, $sp, -4
    sw   $ra, 0($sp)

    li   $a0, 10
    li   $a1, 12

    jal   sum_product

    move   $a0, $v0
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall
        
    lw   $ra, 0($sp)
    addi   $sp, $sp, 4

    li   $v0, 0
    jr   $ra

sum_product:
    addi   $sp, $sp, -12
    sw   $ra, 8($sp)
    sw   $a1, 4($sp)
    sw   $a0, 0($sp)

    li   $a0, 6
    li   $a1, 7

    jal   product

    lw   $a1, 4($sp)
    lw   $a0, 0($sp)

    add   $v0, $v0, $a0
    add   $v0, $v0, $a1

    lw   $ra, 8($sp)
    addi   $sp, $sp, 12

    jr   $ra

product:
    mul   $v0, $a0, $a1

    jr   $ra