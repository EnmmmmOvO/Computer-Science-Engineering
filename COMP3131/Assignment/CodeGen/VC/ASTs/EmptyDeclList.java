/*
 * EmptyDeclList.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyDeclList extends List {

  public EmptyDeclList(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyDeclList(this, o);
  }

}
