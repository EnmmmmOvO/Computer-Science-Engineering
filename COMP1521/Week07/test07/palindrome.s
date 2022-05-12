# read a line and print whether it is a palindrom

main:
    la   $a0, str0       # printf("Enter a line of input: ");
    li   $v0, 4
    syscall

    la   $a0, line
    la   $a1, 256
    li   $v0, 8          # fgets(buffer, 256, stdin)
    syscall              #

    li   $t0, 0          # int i = 0;
    lb   $t1, line       # int temp = line[0];

loop0:
    beq   $t1, 0, end0    # while (line[0] != 0) {

    addi   $t0, $t0, 1   #     i++;
    lb   $t1, line($t0)  #     
    j   loop0             # }

end0:
    li   $t1, 0          # int j = 0;
    addi   $t0, $t0, -2  # int k = i -2;

loop1:
    bge   $t1, $t0, end1 # while (j < k) {

    lb   $t2, line($t0)  
    lb   $t3, line($t1)

    bne   $t2, $t3, if0  #     if (line[j] != line[k]) goto if0  

    addi   $t1, $t1, 1   #     j++;
    addi   $t0, $t0, -1  #     k--;

    j   loop1            # }

if0:
    la   $a0, not_palindrome  # printf("not palindrome\n");
    li   $v0, 4               
    syscall
    j   end2                  # return 0;

end1:
    la   $a0, palindrome      # printf("palindrome\n");
    li   $v0, 4
    syscall

end2:
    li   $v0, 0          # return 0
    jr   $ra


.data
str0:
    .asciiz "Enter a line of input: "
palindrome:
    .asciiz "palindrome\n"
not_palindrome:
    .asciiz "not palindrome\n"


# line of input stored here
line:
    .space 256

