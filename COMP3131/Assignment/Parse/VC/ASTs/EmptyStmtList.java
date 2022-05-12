/*
 * EmptyStmtList.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyStmtList extends List {

  public EmptyStmtList(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyStmtList(this, o);
  }

}
