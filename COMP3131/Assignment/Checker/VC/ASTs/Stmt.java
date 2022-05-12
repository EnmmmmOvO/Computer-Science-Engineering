/*
 * Stmt.java        
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public abstract class Stmt extends AST {

  public Stmt (SourcePosition Position) {
    super (Position);
  }

  // The following methods will be used in Assignments 4 and 5.

  public boolean isEmptyStmt() {
    return this instanceof EmptyStmt;
  }

  public boolean isEmptyCompStmt() {
    return this instanceof EmptyCompStmt;
  }
}
