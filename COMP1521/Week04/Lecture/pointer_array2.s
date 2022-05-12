main:
    la   $s0, numbers     # int *p = &numbers[0]
    addi   $s1, $s0, 16   # int *q = $numbers[4]

loop:
    lw   $a0, 0($s0)      # int j = *p

    li   $v0, 1           # printf("%d", j)
    syscall

    li   $a0, '\n'        # printf("\n")
    li   $v0, 11           
    syscall              

    addi   $s0, $s0, 4    # p ++
    ble   $s0, $s1, loop

end:
    li   $v0, 0           # return 0
    jr   $ra

.data
numbers:  .word 3, 9, 27, 81, 243