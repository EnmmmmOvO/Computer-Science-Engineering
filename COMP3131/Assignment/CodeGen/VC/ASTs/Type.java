/*
 * Type.java                      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public abstract class Type extends AST {

  public Type(SourcePosition Position) {
    super (Position);
  }

  // The following methods will be used in Assignments 4 and 5.

  // if obj and "this" are of the same type
  public abstract boolean equals(Object obj);

  //  In v = e, let "this" be the type of v and obj be the type of e. 
  //  returns true if obj is assignment compatible with "this" and
  //  false otherwise.
  public abstract boolean assignable(Object obj);

  public boolean isVoidType() {
    return (this instanceof VoidType);
  }

  public boolean isIntType() {
    return (this instanceof IntType);
  }

  public boolean isFloatType() {
    return (this instanceof FloatType);
  }

  public boolean isStringType() {
    return (this instanceof StringType);
  }

  public boolean isBooleanType() {
    return (this instanceof BooleanType);
  }

  public boolean isArrayType() {
    return (this instanceof ArrayType);
  }

  public boolean isErrorType() {
    return (this instanceof ErrorType);
  }

}
