/*
 * UnaryExpr.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class UnaryExpr extends Expr {

  public Operator O;
  public Expr E;

  public UnaryExpr(Operator oAST, Expr eAST, SourcePosition Position) {
    super (Position);
    O = oAST;
    E = eAST;
    O.parent = E.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitUnaryExpr(this, o);
  }

}
