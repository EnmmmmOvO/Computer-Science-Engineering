/*
 * BooleanType.java               
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class BooleanType extends Type {

  public BooleanType (SourcePosition Position) {
    super (Position);
  }

  public Object visit (Visitor v, Object o) {
    return v.visitBooleanType(this, o);
  }

  public boolean equals(Object obj) {
    if (obj != null && obj instanceof ErrorType)
      return true;
    else    
      return (obj != null && obj instanceof BooleanType);
  }

  public boolean assignable(Object obj) {
    return equals(obj);
  }

  public String toString() {
    return "boolean";
  }

}
