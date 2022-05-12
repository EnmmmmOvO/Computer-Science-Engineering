/*
 * InitExpr.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class InitExpr extends Expr {

  public List IL;

  public InitExpr (List ilAST, SourcePosition position) {
    super (position);
    IL = ilAST;
    IL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitInitExpr(this, o);
  }

}
