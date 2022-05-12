/*
 * AssignExpr.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class AssignExpr extends Expr {

  public Expr E1, E2;

  public AssignExpr (Expr e1AST, Expr e2AST, SourcePosition Position) {
    super (Position);
    E1 = e1AST;
    E2 = e2AST;
    E1.parent = E2.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitAssignExpr(this, o);
  }

}
