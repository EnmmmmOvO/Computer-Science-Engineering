/*
 * EmptyStmt.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyStmt extends Stmt {

  public EmptyStmt(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyStmt(this, o);
  }

}
