main:
    la   $t0, x
    lw   $t1, 0($t0)
    lw   $t2, 4($t0)
    add  $t3, $t1, $t2 # z = x + y
    sw   $t3, 8($t0)

    lw   $a0, 8($t0)
    li   $v0, 1       # printf("%d", z);
    syscall

    li   $a0, '\n'    # printf("%c", '\n');
    li   $v0, 11
    syscall

    li   $v0, 0       # return 0
    jr   $ra 

.data
x:  .word 17, 25, 0