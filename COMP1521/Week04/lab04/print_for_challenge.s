# print a string without using pre-initialized data
# for the dynamic load challenge exercise

main:
    li   $a0, 'H'       # printf("%c", 'Hi');
    li   $v0, 11
    syscall

    li   $a0, 'i'       # printf("%c", 'i');
    li   $v0, 11
    syscall

    li   $a0, '\n'      # printf("%c", '\n');
    li   $v0, 11
    syscall

    jr   $ra
