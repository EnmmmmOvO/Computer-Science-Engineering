main:
        la $a0, string0 # printf Enter 0
        li $v0, 4
        syscall

        li $v0, 5 #scanf x
        syscall

        and $t0, $v0, 1
        beq $t0, 1, odd

        la $a0, string1 #printf Even
        li $v0, 4
        syscall

        j end

odd:
        la $a0, string2 #printf Even
        li $v0, 4
        syscall

        j end

end:
        li $v0, 0
        jr $ra

        .data

string0:
        .asciiz "Enter a number: "

string1:
        .asciiz "Even\n"

string2:
        .asciiz "Odd\n"

