main:
    addi   $sp, $sp, -4
    sw   $ra, 0($sp)

    li   $a0, 1

    jal   two

    lw   $ra, 0($sp)
    addi   $sp, $sp, 4

    li   $v0, 0
    jr   $ra

two:
    addi   $sp, $sp, -8
    sw   $ra, 4($sp)
    sw   $a0, 0($sp)

print:
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    lw   $a0, 0($sp)

    bge   $a0, 1000000, end
    mul   $a0, $a0, 2
    jal   two

end:
    lw   $ra, 4($sp)
    addi   $sp, $sp, 8
    jr   $ra