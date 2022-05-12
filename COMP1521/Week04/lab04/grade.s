# read a mark and print the corresponding UNSW grade

main:
	la   $a0, prompt    # printf("Enter a mark: ");
	li   $v0, 4
	syscall

	li   $v0, 5         # scanf("%d", mark);
	syscall

	bge   $v0, 85, HD
	bge   $v0, 75, DN
	bge   $v0, 65, CR
	bge   $v0, 50, PS

	la   $a0, fl
	li   $v0, 4
	syscall
	j   end

HD:
	la   $a0, hd
	li   $v0, 4
	syscall
	j   end

PS:
	la   $a0, ps
	li   $v0, 4
	syscall
	j   end

CR:
	la   $a0, cr
	li   $v0, 4
	syscall
	j   end

DN:
	la   $a0, dn
	li   $v0, 4
	syscall
	j   end

end:
	jr   $ra            # return


	.data
prompt:
	.asciiz "Enter a mark: "
fl:
	.asciiz "FL\n"
ps:
	.asciiz "PS\n"
cr:
	.asciiz "CR\n"
dn:
	.asciiz "DN\n"
hd:
	.asciiz "HD\n"
