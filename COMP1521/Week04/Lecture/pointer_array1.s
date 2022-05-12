main:
    la   $t0, numbers     # int *p = &numbers[0]
    addi   $t1, $t0, 16   # int *q = $numbers[4]

loop:
    bgt   $t0, $t1, end   # if (*p > *q) goto end

    lw   $a0, 0($t0)      # int j = *p

    li   $v0, 1           # printf("%d", j)
    syscall

    li   $a0, '\n'        # printf("\n")
    li   $v0, 11           
    syscall              

    addi   $t0, $t0, 4    # p ++
 
    j   loop              # goto loop

end:
    li   $v0, 0           # return 0
    jr   $ra

.data
numbers:  .word 3, 9, 27, 81, 243