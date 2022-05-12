package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ForStmt extends Stmt {

  public Expr E1;
  public Expr E2;
  public Expr E3;
  public Stmt S;


  public ForStmt(Expr e1AST, Expr e2AST, Expr e3AST, Stmt sAST,
                                              SourcePosition Position) {
    super (Position);
    E1 = e1AST;
    E2 = e2AST;
    E3 = e3AST;
    S = sAST;
    E1.parent = E2.parent = E3.parent = S.parent = this;
  }
  public Object visit(Visitor v, Object o) {
    return v.visitForStmt(this, o);
  }
}
