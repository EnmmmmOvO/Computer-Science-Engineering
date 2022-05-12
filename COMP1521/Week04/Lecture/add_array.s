main: 
    li   $t0, 13

    mul   $t0, $t0, 2
    la   $t1, x
    add   $t2, $t1, $t0
    li   $t3, 23
    sh   $t3, 0($t2)

    jr   $ra


.data
x:  .space 60