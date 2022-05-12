/*
 * EmptyExprList.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyExprList extends List {

  public EmptyExprList(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyExprList(this, o);
  }

}
