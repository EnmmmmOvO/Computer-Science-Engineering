/*
 * ArgList.java  
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ArgList extends List {
  public Arg A;
  public List AL;

  public ArgList(Arg aAST, List alAST, SourcePosition thePosition) {
    super (thePosition);
    A = aAST;
    AL = alAST;
    A.parent = AL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitArgList(this, o);
  }

}
