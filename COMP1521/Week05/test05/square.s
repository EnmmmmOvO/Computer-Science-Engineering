main:
    li   $v0, 5         #   scanf("%d", &x);
    syscall             #
    move $t0, $v0

    li   $t1, 0         #   int i = 0;



loop1_1:
    bge   $t1, $t0, end #  while (i < x)

    li   $t2, 0         #   int j = 0;

    j   loop2



loop1_2:
    addi   $t1, $t1, 1  #   i = i + 1
    
    li   $a0, '\n'      #   printf("%c", '\n');
    li   $v0, 11
    syscall

    j   loop1_1



loop2:
    bge   $t2, $t0, loop1_2  #   while (j < x)

    li   $a0, '*'          #   printf("*");
    li   $v0, 11
    syscall

    addi   $t2, $t2, 1      #   j = j + 1;

    j   loop2


end:

    li   $v0, 0         # return 0
    jr   $ra
