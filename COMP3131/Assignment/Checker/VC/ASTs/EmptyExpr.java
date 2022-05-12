/*
 * EmptyExpr.java 
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyExpr extends Expr {

  public EmptyExpr (SourcePosition thePosition) {
    super (thePosition);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyExpr(this, o);
  }
}
