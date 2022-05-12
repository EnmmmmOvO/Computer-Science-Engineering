/*
 * IntExpr.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class IntExpr extends Expr {

  public IntLiteral IL;

  public IntExpr(IntLiteral ilAST, SourcePosition Position) {
    super (Position);
    IL = ilAST;
    IL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitIntExpr(this, o);
  }

}
