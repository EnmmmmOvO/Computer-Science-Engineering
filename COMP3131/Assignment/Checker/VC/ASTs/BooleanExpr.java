/*
 * BooleanExpr.java       
 *
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class BooleanExpr extends Expr {

  public BooleanLiteral BL;

  // ********* NOTE *********
  // The two fields below are not used for this year's assignments
  public AST trueSuccessor, falseSuccessor;

  public BooleanExpr(BooleanLiteral blAST, SourcePosition position) {
    super (position);
    BL = blAST;
    BL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitBooleanExpr(this, o);
  }

}
