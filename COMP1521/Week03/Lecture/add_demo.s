main:
        li $t0, 17 #x = 17
        li $t1, 25 #y =25
        add $t2, $t1, $t0 #$t2 = 25 + 17
        move $a0, $t2 #printf of an integer
        li $v0 ,1

        syscall

        li $a0, '\n' #printf a newline
        li, $v0, 11 
        syscall

        li $v0, 0
        jr $ra