/*
 * DeclList.java       
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class DeclList extends List {

  public Decl D;
  public List DL;

  public DeclList(Decl dAST, List dlAST, SourcePosition position) {
    super (position);
    D = dAST;
    DL = dlAST;
    D.parent = DL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitDeclList(this, o);
  }

}
