======= The VC compiler =======

Pass 1: Lexical and syntactic Analysis
Pass 2: Semantic Analysis
ERROR: 3(5)..3(5): *18: array size missing: b
ERROR: 8(9)..8(11): *14: invalid initialiser: array initialiser for scalar
ERROR: 9(15)..9(17): *13: wrong type for element in array initialiser: at position 1
ERROR: 9(20)..9(27): *13: wrong type for element in array initialiser: at position 2
ERROR: 9(5)..9(30): *16: excess elements in array initialiser: x
ERROR: 11(5)..11(12): *15: invalid initialiser: scalar initialiser for array: z
ERROR: 14(1)..14(3): *12: attempt to use a scalar/function as an array
ERROR: 15(1)..15(1): *11: attempt to use an array/function as a scalar: x
ERROR: 15(1)..15(5): *9: incompatible type for this binary operator: +
ERROR: 16(1)..16(8): *17: array subscript is not an integer
ERROR: 18(3)..18(3): *27: wrong type for actual parameter: x
ERROR: 3(1)..19(1): *0: main function is missing
Compilation was unsuccessful.
