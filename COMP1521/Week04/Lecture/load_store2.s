main:
    li   $t0, 42
    la   $t1, x
    sb   $t0, 0($t1)

    lb   $a0, 0($t1)
    li   $v0, 1
    syscall

    li   $a0, '\n'
    li   $v0, 11
    syscall

    li   $v0, 0 
    jr   $ra

.data
x:    .space 1