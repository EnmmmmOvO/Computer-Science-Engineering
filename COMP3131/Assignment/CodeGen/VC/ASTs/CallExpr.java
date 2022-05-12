/*
 * CallExpr.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class CallExpr extends Expr {

  public Ident I;
  public List AL;

  public CallExpr(Ident id, List aplAST, SourcePosition Position) {
    super (Position);
    I = id;
    AL = aplAST;
    I.parent = AL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitCallExpr(this, o);
  }

}
