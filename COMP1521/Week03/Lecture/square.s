main:
        li $t0, 0 # i = 0
        li $t1, 0 # sum = 1

loop:
        bgt $t0, 100, end
        mul $t2, $t0, $t0 # square *= i
        add $t1, $t1, $t2 # sum += square

        move $a0, $t0
        li $v0, 1
        syscall

        li $a0 ' '
        li $v0, 11
        syscall

        move $a0, $t1
        li $v0, 1
        syscall

        li $a0 '\n'
        li $v0, 11
        syscall

        addi $t0, $t0, 1

	j loop

end:
        move $a0, $t1
        li $v0, 1
        syscall

        li $a0 '\n'
        li $v0, 11
        syscall

        li $v0, 0
        jr $ra