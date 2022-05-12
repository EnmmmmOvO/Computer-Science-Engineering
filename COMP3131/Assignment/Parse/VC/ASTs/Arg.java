/*
 * Arg.java               
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class Arg extends Expr {

  public Expr E;

  public Arg (Expr eAST, SourcePosition position) {
    super (position);
    E = eAST;
    eAST.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitArg(this, o);
  }

}
