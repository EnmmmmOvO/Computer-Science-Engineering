main:
    li   $s0, 0

loop_low:
    bge   $s0, 3, end1
    li   $s1, 0

loop_col:
    bge   $s1, 5, end2
    la   $t0, numbers

    mul   $t1, $s0, 20
    add   $t2, $t1, $t0
    mul   $t3, $s1, 4
    add   $t4, $t3, $t2
    lw   $a0, ($t4)
    li   $v0, 1
    syscall

    li   $a0, ' '
    li   $v0, 11
    syscall

    addi  $s1, $s1, 1
    j   loop_col

end2:
    li   $a0, '\n'
    li   $v0, 11
    syscall

    addi   $s0, $s0, 1
    j   loop_low

end1:
    li   $v0, 0
    jr   $ra


.data
numbers:  .word 3, 9, 27, 81, 243, 4, 16, 64, 256, 1024, 5, 25, 125, 625, 3125