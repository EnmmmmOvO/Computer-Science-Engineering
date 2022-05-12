main:
		li $t0, 0
		li $t1, 0

loop:
		bge $t0, 5, end
		add $t1, $t1, $t0
		addi $t0, $t0, 1
		j loop

end:
		move $a0, $t1
		li $v0, 1
		syscall

		li $a0, '\n' 
		li $v0, 11
		syscall


		li $v0 , 0
		jr $ra
    