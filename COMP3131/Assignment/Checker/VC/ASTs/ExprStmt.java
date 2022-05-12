/*
 * ExprStmt.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ExprStmt extends Stmt {

  public Expr E;

  public ExprStmt (Expr eAST, SourcePosition Position) {
    super (Position);
    E = eAST;
    E.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitExprStmt(this, o);
  }

}
