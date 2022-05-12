/*
 * StringType.java               
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class StringType extends Type {

  public StringType (SourcePosition Position) {
    super (Position);
  }

  public Object visit (Visitor v, Object o) {
    return v.visitStringType(this, o);
  }

  public boolean equals(Object obj) {
    if (obj != null && obj instanceof ErrorType)
      return true;
    else    
      return (obj != null && obj instanceof StringType);
  }

  // not used this year
  public boolean assignable(Object obj) {
    if (obj != null && obj instanceof ErrorType)
      return true;
    else    
      return (obj != null && obj instanceof StringType);
  }

  public String toString() {
    return "string";
  }

}
