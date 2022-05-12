/*
 * Ident.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class Ident extends Terminal {

  public AST decl; 

  public Ident(String value , SourcePosition position) {
    super (value, position);
    decl = null;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitIdent(this, o);
  }

}
