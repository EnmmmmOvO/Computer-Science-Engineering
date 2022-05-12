/*
 * Expr.java       
 */

package VC.ASTs;

import java.util.LinkedList;

import VC.Scanner.SourcePosition;

public abstract class Expr extends AST {

  public Type type;

 

  public Expr (SourcePosition Position) {
    super (Position);
    type = null;
  }


  // The following method will be used in Assignments 4 and 5.

  public boolean isEmptyExpr() {
    return this instanceof EmptyExpr;
  }

}
