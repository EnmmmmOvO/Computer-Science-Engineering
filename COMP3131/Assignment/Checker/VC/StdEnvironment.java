/*
 * StdEnvironment.java     
 * 
 * Most programming languages contain a standard collection of 
 * pre-defined constants, variables, types and functions that
 * the programmer can use without having to introduce them themselves.
 * For example, there is the package java.lang for Java and the
 * standard prelude in Haskell. Such a collection is called the
 * standard environment.
 *
 * In VC, the standard environment contains five built-in primitive
 * types and 11 built-in I/O functions. There is also an errorType,
 * which is assigned to an expression when there is a type error
 * detected in the expression. This errorType will be used to 
 * reduce the number of spurious errors produced. See 
 * VC.ASTs.IntType.java and VC.ASTs.FloatType.java.
 *
 * In our current implementation of the symbol table, the attribute 
 * of an identifier is represented by a pointer to the corresponding 
 * declaration. In the case of a built-in function, its declaration
 * will not be given by the programmer. The compiler must construct
 * explicitly its "declaration" and enter the name of the corresponding 
 * function into the symbol table. This is accomplished by the method
 * establishStdEnvironment of the class Checker in Checker.java.
 * 
 */

package VC;

import VC.ASTs.*;

public final class StdEnvironment {

  public static Type booleanType, intType, floatType, stringType, voidType, errorType;

  // Small ASTs representing "declarations" of nine built-in functions

  public static FuncDecl
    putBoolDecl, putBoolLnDecl, 
    getIntDecl, putIntDecl, putIntLnDecl, 
    getFloatDecl, putFloatDecl, putFloatLnDecl, 
    putStringDecl, putStringLnDecl, putLnDecl;

}
