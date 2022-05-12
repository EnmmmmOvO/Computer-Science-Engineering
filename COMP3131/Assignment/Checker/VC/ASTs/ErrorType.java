/*
 * ErrorType.java   
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ErrorType extends Type {

  public ErrorType(SourcePosition thePosition) {
    super (thePosition);
  }

  public Object visit (Visitor v, Object o) {
    return v.visitErrorType(this, o);
  }

  public boolean equals (Object obj) {
    return true;
  }
  public boolean assignable (Object obj) {
    return true;
  }

  public String toString() {
    return "error";
  }
}
