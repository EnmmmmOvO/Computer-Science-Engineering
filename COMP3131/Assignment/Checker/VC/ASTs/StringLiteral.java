/*
 * StringLiteral.java
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class StringLiteral extends Terminal {

  public StringLiteral (String value, SourcePosition position) {
    super (value, position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitStringLiteral(this, o);
  }

}
