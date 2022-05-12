# read 10 numbers into an array
# swap any pairs of of number which are out of order
# then print the 10 numbers

# i in register $t0,
# registers $t1 - $t3 used to hold temporary results

main:

    li   $t0, 0         # i = 0
loop0:
    bge  $t0, 10, end0  # while (i < 10) {

    li   $v0, 5         #   scanf("%d", &numbers[i]);
    syscall             #

    mul  $t1, $t0, 4    #   calculate &numbers[i]
    la   $t2, numbers   #
    add  $t3, $t1, $t2  #
    sw   $v0, ($t3)     #   store entered number in array

    addi $t0, $t0, 1    #   i++;
    j    loop0          # }
end0:
    li   $t0, 1         # i = 1

loop2:
    mul   $t1, $t0, 4   # int x = numbers[i];
    la   $t2, numbers
    add   $t3, $t2, $t1
    lw   $s0, ($t3)

    addi   $t0, $t0, -1

    mul   $t1, $t0, 4   # int y = numbers[i - 1];
    la   $t2, numbers
    add   $t3, $t2, $t1
    lw   $s1, ($t3)

    bge   $s0, $s1, loop3 #if (x >= y) goto loop3

    sw   $s0, ($t3)      # numbers[i] = y;

    addi   $t0, $t0, 1   # numbers[i - 1] = x;
    mul   $t1, $t0, 4
    la   $t2, numbers
    add   $t3, $t2, $t1
    sw   $s1, ($t3)

    addi   $t0, $t0, -1

loop3:
    addi   $t0, $t0, 2  # i ++
    blt   $t0, 10, loop2 #while (i < 10) goto loop2


    li   $t0, 0         # i = 0
loop1:
    bge  $t0, 10, end1  # while (i < 10) {

    mul  $t1, $t0, 4    #   calculate &numbers[i]
    la   $t2, numbers   #
    add  $t3, $t1, $t2  #
    lw   $a0, ($t3)     #   load numbers[i] into $a0
    li   $v0, 1         #   printf("%d", numbers[i])
    syscall

    li   $a0, '\n'      #   printf("%c", '\n');
    li   $v0, 11
    syscall

    addi $t0, $t0, 1    #   i++
    j    loop1          # }

end1:
    li   $v0, 0
    jr   $ra            # return 0

.data

numbers:
    .word 0 0 0 0 0 0 0 0 0 0  # int numbers[10] = {0};

