/*
 * IfStmt.java    
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class IfStmt extends Stmt {

  public Expr E;
  public Stmt S1, S2;

  // ********* NOTE *********
  // The two fields below are not used for this year's assignments
  public AST trueSuccessor, falseSuccessor;

  public IfStmt(Expr eAST, Stmt sAST, SourcePosition position) {
    super (position);
    E = eAST;
    S1 = sAST;
    S2 = new EmptyStmt(new SourcePosition());
    E.parent = S1.parent = S2.parent = this;
  }

  public IfStmt(Expr eAST, Stmt s1AST, Stmt s2AST, SourcePosition Position) {
    super (Position);
    E = eAST;
    S1 = s1AST;
    S2 = s2AST;
    E.parent = S1.parent = S2.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitIfStmt(this, o);
  }

}
