/*
 * ReturnStmt.java    
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ReturnStmt extends Stmt {

  public Expr E;

  public ReturnStmt(Expr eAST, SourcePosition Position) {
    super (Position);
    E = eAST;
    E.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitReturnStmt(this, o);
  }

}
