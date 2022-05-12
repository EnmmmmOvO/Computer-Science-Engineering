# read 10 numbers into an array
# bubblesort them
# then print the 10 numbers

# i in register $t0
# registers $t1, $t2 & $t3 used to hold temporary results

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
    li   $s0, 1         # int swapped = 1;

loop2:
    beq   $s0, 0, loop3 # while (swapped == 0) goto loop3
    li   $s0, 0         # swapped = 0;
    li   $t0, 1         # i = 0

loop4:
    bge   $t0, 10, end2 # while (i >= 10) goto end2
    
    mul   $t1, $t0, 4   # int x = numbers[i];
    la   $t2, numbers
    add   $t3, $t2, $t1
    lw   $s1, ($t3)

    addi   $t0, $t0, -1 # int x = numbers[i - 1];
    mul   $t1, $t0, 4
    la   $t2, numbers
    add   $t3, $t2, $t1
    lw   $s2, ($t3)

    bge   $s1, $s2, end4 # if (x >= y) goto end4

    sw   $s1, ($t3)      # numbers[i] = y;

    addi   $t0, $t0, 1   # numbers[i - 1] = x;
    mul   $t1, $t0, 4
    la   $t2, numbers
    add   $t3, $t2, $t1
    sw   $s2, ($t3)

    li   $s0, 1          # swapped = 1
    addi   $t0, $t0, -1

end4:
    addi   $t0, $t0, 2   # i ++
    j   loop4

end2:
    j   loop2

loop3:
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

    jr   $ra            # return

.data

numbers:
    .word 0 0 0 0 0 0 0 0 0 0  # int numbers[10] = {0};

