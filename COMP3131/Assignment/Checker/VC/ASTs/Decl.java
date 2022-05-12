/*
 * Decl.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public abstract class Decl extends AST {

  public Type T;
  public Ident I;

  // the index of this variable or formal parameter
  // See page 72, the JVM spec, 2nd edition.
  public int index; 

  public Decl(SourcePosition Position) {
    super (Position);
  }

  // The following methods will be used in Assignments 4 and 5.

  public boolean isFuncDecl() {
    return this instanceof FuncDecl;
  }

  public boolean isGlobalVarDecl() {
    return this instanceof GlobalVarDecl;
  }

  public boolean isLocalVarDecl() {
    return this instanceof LocalVarDecl;
  }

  public boolean isParaDecl() {
    return this instanceof ParaDecl;
  }

}
