/*
 * FuncDecl.java      
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class FuncDecl extends Decl {

  public List PL;
  public Stmt S;

  public AST entryNode;

  public FuncDecl(Type tAST, Ident idAST, List fplAST, 
         Stmt cAST, SourcePosition Position) {
    super (Position);
    T = tAST;
    I = idAST;
    PL = fplAST;
    S = cAST;
    T.parent = I.parent = PL.parent = S.parent = this;
  }

  public Object visit (Visitor v, Object o) {
    return v.visitFuncDecl(this, o);
  }

}
