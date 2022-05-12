/*
 * EmptyArgList.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class EmptyArgList extends List {

  public EmptyArgList(SourcePosition position) {
    super (position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitEmptyArgList(this, o);
  }

}
