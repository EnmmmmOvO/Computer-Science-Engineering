/*
 * StmtList.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class StmtList extends List {

  public Stmt S;
  public List SL;

  public StmtList(Stmt sAST, List slAST, SourcePosition Position) {
    super (Position);
    S = sAST;
    SL = slAST;
    S.parent = SL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitStmtList(this, o);
  }

}
