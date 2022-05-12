/*
 * FloatType.java               
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class FloatType extends Type {

  public FloatType (SourcePosition Position) {
    super (Position);
  }

  public Object visit (Visitor v, Object o) {
    return v.visitFloatType(this, o);
  }

  public boolean equals(Object obj) {
    if (obj != null && obj instanceof ErrorType)
      return true;
    else    
      return (obj != null && obj instanceof FloatType);
  }

  public boolean assignable(Object obj) {
    if (obj != null && obj instanceof ErrorType)
      return true;
    else    
      return (obj != null && (obj instanceof IntType
	     || obj instanceof FloatType));
  }

  public String toString() {
    return "float";
  }

}
