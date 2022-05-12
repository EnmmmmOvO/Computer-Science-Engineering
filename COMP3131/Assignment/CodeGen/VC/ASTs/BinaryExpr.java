/*
 * BinaryExpr.java       
 *
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class BinaryExpr extends Expr {

  public Expr E1, E2;
  public Operator O;

  public BinaryExpr(Expr e1AST, Operator oAST, Expr e2AST, SourcePosition Position) {
    super (Position);
    O = oAST;
    E1 = e1AST;
    E2 = e2AST;
    O.parent = E1.parent = E2.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitBinaryExpr(this, o);
  }

}
