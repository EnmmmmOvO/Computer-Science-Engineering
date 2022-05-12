# COMP1521 21T2 ... final exam, question 2

	.data
even_parity_str:	.asciiz "the parity is even\n"
odd_parity_str:		.asciiz "the parity is odd\n"

	.text
main:
	li	$v0, 5
	syscall
	move	$t0, $v0
	# input is in $t0

	li   $t1, 0						# int bit_idx = 0;
	li   $t2, 0						# int n_bits_set = 0;

loop0:
	beq   $t1, 32, end0				# while (bit_idx != 32) {
	srl   $t3, $t0, $t1				# 	  int bit = n >> bit_idx;
	andi   $t3, $t3, 1				#     bit = (n >> bit_idx) & 1;
	add   $t2, $t2, $t3				#     n_bits_set = n_bits_set + bit;
	addi   $t1, $t1, 1				#     bit_idx++;
	j   loop0						# }

end0:
	li   $t0, 2						# 
	div   $t2, $t0					# 
	mfhi   $t2 						# n_bits_set % 2
	beq   $t2, 0, if0				# if (n_bits_set % 2 == 0) goto if0
	li	$v0, 4						# else {
	la	$a0, odd_parity_str			#     printf ("the parity is odd\n");
	syscall							#
	j   end							# }

if0:
	li	$v0, 4						# {
	la	$a0, even_parity_str		#     printf ("the parity is even\n");
	syscall							# }

end:
	li	$v0, 0
	jr	$ra
