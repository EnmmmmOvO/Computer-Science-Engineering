/*
 * SimpleVar.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class SimpleVar extends Var {

  public Ident I;

  public SimpleVar(Ident idAST, SourcePosition thePosition) {
    super (thePosition);
    I = idAST;
    I.parent = this;
  }

  public Object visit (Visitor v, Object o) {
    return v.visitSimpleVar(this, o);
  }

}
