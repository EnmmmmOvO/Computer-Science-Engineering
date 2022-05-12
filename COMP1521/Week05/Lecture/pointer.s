main:
    la   $t0, number
    lw   $t1, ($t0)

    move   $a0, $t1
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    li   $t2, 27
    sw   $t2, ($t0)

    lw   $a0, number
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    li   $v0, 0

    jr   $ra



.data
number:
    .word 42