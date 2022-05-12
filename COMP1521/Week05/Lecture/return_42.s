main: 
    addi   $sp, $sp, -4
    sw   $ra, 0($sp)

    jal   answer

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

answer:
    li   $v0, 42
    jr   $ra