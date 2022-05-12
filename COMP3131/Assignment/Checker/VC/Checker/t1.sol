======= The VC compiler =======

Pass 1: Lexical and syntactic Analysis
Pass 2: Semantic Analysis
ERROR: 3(6)..3(6): *3: identifier declared void: v
ERROR: 4(1)..4(11): *31: missing return statement
ERROR: 5(9)..5(9): *2: identifier redeclared: f
ERROR: 6(5)..6(5): *2: identifier redeclared: f
ERROR: 6(27)..6(27): *2: identifier redeclared: i
ERROR: 6(35)..6(35): *4: identifier declared void[]: k
ERROR: 7(7)..7(7): *2: identifier redeclared: r
ERROR: 8(3)..8(4): *10: incompatible type for this unary operator: !
ERROR: 9(3)..9(11): *7: invalid lvalue in assignment
ERROR: 10(3)..10(11): *6: incompatible type for =
ERROR: 11(3)..11(10): *9: incompatible type for this binary operator: +
ERROR: 12(3)..12(13): *8: incompatible type for return
ERROR: 13(3)..20(20): *30: statement(s) not reached
ERROR: 14(7)..14(9): *20: if conditional is not boolean (found: float)
ERROR: 16(10)..16(10): *22: while conditional is not boolean (found: int)
ERROR: 18(9)..18(9): *21: for conditional is not boolean (found: int)
ERROR: 20(3)..20(3): *11: attempt to use an array/function as a scalar: f
ERROR: 20(7)..20(7): *5: identifier undeclared: g
ERROR: 20(11)..20(13): *5: identifier undeclared: h
ERROR: 20(17)..20(17): *19: attempt to reference a scalar/array as a function: i
ERROR: 20(3)..20(19): *7: invalid lvalue in assignment: f
ERROR: 23(5)..23(5): *26: too few actual parameters
ERROR: 24(5)..24(7): *27: wrong type for actual parameter: i
ERROR: 24(16)..24(16): *27: wrong type for actual parameter: k
ERROR: 24(19)..24(19): *25: too many actual parameters
ERROR: 25(3)..25(8): *23: break must be in a while/for
ERROR: 26(3)..26(11): *24: continue must be in a while/for
ERROR: 29(5)..29(5): *2: identifier redeclared: x
ERROR: 2(1)..29(6): *1: return type of main is not int
Compilation was unsuccessful.
