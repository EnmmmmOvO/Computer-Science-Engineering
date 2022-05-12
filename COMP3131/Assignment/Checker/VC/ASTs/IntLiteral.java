/*
 * IntLiteral.java
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class IntLiteral extends Terminal {

  public IntLiteral (String value, SourcePosition position) {
    super (value, position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitIntLiteral(this, o);
  }

}
