/*
 * CompoundStmt.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class CompoundStmt extends Stmt {

  public List DL;
  public List SL;

  public CompoundStmt(List dlAST, List slAST, SourcePosition position) {
    super (position);
    DL = dlAST;
    SL = slAST;
    DL.parent = SL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitCompoundStmt(this, o);
  }

}
