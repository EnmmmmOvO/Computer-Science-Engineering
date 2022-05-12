/*
 * EmptyParaList.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyParaList extends List {

  public EmptyParaList(SourcePosition Position) {
    super (Position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyParaList(this, o);
  }

}
