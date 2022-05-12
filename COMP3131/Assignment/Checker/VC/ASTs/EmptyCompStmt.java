/*
 * EmptyCompStmt.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyCompStmt extends Stmt {

  public EmptyCompStmt(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyCompStmt(this, o);
  }
}
