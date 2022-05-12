# print 42

main:
    li   $a0, 42      # printf("%d", 42);
    li   $v0, 1
    syscall
    jr   $ra          # return
