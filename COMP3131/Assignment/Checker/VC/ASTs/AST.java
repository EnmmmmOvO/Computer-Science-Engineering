/*
 * AST.java    
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public abstract class AST {

  public SourcePosition	position;
  public AST parent;
 
  public AST (SourcePosition Position) {
    position = Position;
  }

  public SourcePosition getPosition() {
    return position;
  }

  public abstract Object visit(Visitor v, Object o);

}
