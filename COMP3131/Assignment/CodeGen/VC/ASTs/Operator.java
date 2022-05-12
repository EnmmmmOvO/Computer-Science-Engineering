/*
 * Operator.java             
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class Operator extends Terminal {

  public Operator (String value, SourcePosition position) {
    super (value, position);
  }

  public Object visit(Visitor v, Object o) {
    return v.visitOperator(this, o);
  }

}
