main:
    li   $v0, 5         #   scanf("%d", &x);
    syscall             #
    move $t0, $v0

    li   $v0, 5         #   scanf("%d", &y);
    syscall             #
    move $t1, $v0

    addi   $t2, $t0, 1 #   int i = x + 1;

loop_1:
    bge   $t2, $t1, end #   while (i < y)

    beq   $t2, 13 loop_2    #  if (i == 13)

    move   $a0, $t2      #   printf("%d", i);
    li   $v0, 1
    syscall

    li   $a0, '\n'      #   printf('\n');
    li   $v0, 11
    syscall

    j   loop_2


loop_2:
    addi   $t2, $t2, 1  #    i = i + 1;
    
    j   loop_1

end:

    li   $v0, 0         # return 0
    jr   $ra
