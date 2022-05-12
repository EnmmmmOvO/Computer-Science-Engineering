# Sieve of Eratosthenes
# https://en.wikipedia.org/wiki/Sieve_of_Eratosthenes
main:
    li   $s0, 0             # int i = 0;

loop0:
    bge   $s0, 1000, end0   # while (i < 1000) {
    li   $t0, 1             #     
    sb   $t0, prime($s0)    #     prime[i] = 1;
                            #
    addi   $s0, $s0, 1      #     i++;
                            #
    j   loop0               #
                            # }

end0:
    li   $s0, 2             # i = 2;
    
loop1:
    bge   $s0, 1000, end    # while (i < 1000) {
    lb   $t0, prime($s0)    #
    bne   $t0, 1, end1      #     if (prime[i]) {
    
    move   $a0, $s0         #
    li   $v0, 1             #
    syscall                 #         printf("%d", i);
    
    li   $a0, '\n'          #
    li   $v0, 11            #
    syscall                 #         printf("\n");

    mul   $t0, $s0, 2       #         int j = 2 * i

loop2:
    bge   $t0, 1000, end1   #         while (j < 1000) {
    li   $t1, 0             #
    sb   $t1, prime($t0)    #             prime[j] = 0;

    add   $t0, $t0, $s0     #             j = j + i;
    j   loop2               #         }

end1:
    addi   $s0, $s0, 1      #         i++;
    j   loop1               #     }
                            # }

end:
    li   $v0, 0             # return 0
    jr   $ra

.data
prime:
    .space 1000