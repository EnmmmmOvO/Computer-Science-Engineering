/*
 * ParaList.java  
 */

package VC.ASTs;

import VC.Scanner.SourcePosition;

public class ParaList extends List {
  public ParaDecl P;
  public List PL;

  public ParaList(ParaDecl pAST, List plAST,
                                   SourcePosition thePosition) {
    super (thePosition);
    P = pAST;
    PL = plAST;
    P.parent = PL.parent = this;
  }

  public Object visit(Visitor v, Object o) {
    return v.visitParaList(this, o);
  }

}
