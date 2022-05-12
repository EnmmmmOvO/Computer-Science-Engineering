/*
 * BooleanLiteral.java
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class BooleanLiteral extends Terminal {

  public BooleanLiteral (String value, SourcePosition position) {
    super (value, position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitBooleanLiteral(this, o);
  }

}
