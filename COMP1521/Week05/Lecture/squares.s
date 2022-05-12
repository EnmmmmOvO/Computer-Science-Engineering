main:
    addi   $sp, $sp, -40
    li   $t0, 0

loop0:
    mul   $t1, $t0, 4
    add   $t2, $t1, $sp
    mul   $t3, $t0, $t0
    sw   $t3, 0($t2)

    addi   $t0, $t0, 1
    blt   $t0, 10, loop0

    li   $t0, 0

loop1:
    bge   $t0, 10, end
    
    mul   $t1, $t0, 4
    add   $t2, $t1, $sp
    lw   $a0, 0($t2)
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    addi   $t0, $t0, 1
    j   loop1

end:
    add   $sp, $sp, 40
    li   $v0, 0
    jr   $ra

.data
squares:
    .space 40