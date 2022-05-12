main:
	la $t0, string
	move $a0, $t0
	li $v0, 4
	syscall


	li $v0, 0
	jr $ra

	.data
string:
	.asciiz "I MIPS you!\n"