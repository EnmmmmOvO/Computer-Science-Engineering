main:
        li $t0, 1 # i = 1

loop:
        bgt	$t0, 10, end # i > 10

        move $a0, $t0 
        li $v0, 1
        syscall

        li $a0, '\n' 
        li $v0, 11
        syscall


        addi $t0, $t0, 1
        j loop

end :
        li $v0 ,0
        jr $ra