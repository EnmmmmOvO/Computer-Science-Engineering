.text
main:
    li   $t0, 0

loop:
    bge   $t0, 5, end     # if (i >= 5) go to end

    la   $t1, numbers     # int j = numbers[i]
    mul   $t2, $t0, 4
    add   $t3, $t2, $t1
    
    lw   $a0, 0($t3)
    li   $v0, 1
    syscall
    li   $a0, '\n'
    li   $v0, 11
    syscall

    addi   $t0, $t0, 1
    j   loop

end:
    li   $v0, 0
    jr   $ra


.data
numbers:  .word 3, 9, 27, 81, 243
    