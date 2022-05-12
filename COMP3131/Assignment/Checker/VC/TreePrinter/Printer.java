/*
 * Printer.java      
 *
 * Prints the AST in the text form, which can be used 
 *  (1) either for automarking, or
 *  (2) for debugging the parser
 * --- Jingling
 */

package VC.TreePrinter;


import VC.ASTs.*;
import java.io.FileWriter;
import java.io.PrintWriter;

public class Printer implements Visitor {

  private int indent;
  private boolean firstFunction; 
  private PrintWriter textOut;

  public Printer(String filename) {
    indent = 0;

    try {
      textOut = new PrintWriter(new FileWriter(filename));
    } catch (java.io.IOException e) {
      System.out.println("Caught IOException: " + e.getMessage());
      System.exit(1);
    }
  }

  private String indentString() {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < indent; ++i) {
      sb.append("  ");
    }
    return sb.toString();
  }

  void print(String s) {
    textOut.println(s);
  }

  public final void print(AST ast) {
    ast.visit(this, null);
    textOut.close();
  }

  /*
   * In all methods,
   * (1) The second argument "o" is not used, and
   * (2) The returned object is not used.
   */

  // Programs
  public Object visitProgram(Program ast, Object o) {
    print(indentString() + "Program");
    ++indent;
    ast.FL.visit(this, o);
    --indent;
    return null;
  }

 // Lists

  public Object visitEmptyDeclList(EmptyDeclList ast, Object o) {
    print(indentString() + "EmptyDeclList");
    return null;
  }

  public Object visitEmptyStmtList(EmptyStmtList ast, Object o) {
    print(indentString() + "EmptyStmtList");
    return null;
  }

  public Object visitEmptyExprList(EmptyExprList ast, Object o) {
    print(indentString() + "EmptyExprList");
    return null;
  }

  public Object visitEmptyParaList(EmptyParaList ast, Object o) {
    print(indentString() + "EmptyParaList");
    return null;
  }

  public Object visitEmptyArgList(EmptyArgList ast, Object o) {
    print(indentString() + "EmptyArgList");
    return null;
  }


  // Declarations
  public Object visitDeclList(DeclList ast, Object o) {
    print(indentString() + "DeclList");
    ++indent;
    ast.D.visit(this, o);
    ast.DL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitFuncDecl(FuncDecl ast, Object o) {
    print(indentString() + "FuncDecl");
    ++indent;
    ast.T.visit(this, o);
    ast.I.visit(this, o);
    ast.PL.visit(this, o);
    ast.S.visit(this, o); 
    --indent;
    return null;
  }

  public Object visitGlobalVarDecl(GlobalVarDecl ast, Object o) {
    print(indentString() + "GloablVarDecl");
    ++indent;
    ast.T.visit(this, o);
    ast.I.visit(this, o);
    if (! (ast.E instanceof EmptyExpr)) {
      print(indentString() + "=");
      ast.E.visit(this, o);
    }
    --indent;
    return null;
  }

  public Object visitLocalVarDecl(LocalVarDecl ast, Object o) {
    print(indentString() + "LocalVarDecl");
    ++indent;
    ast.T.visit(this, o);
    ast.I.visit(this, o);
    if (! (ast.E instanceof EmptyExpr)) {
      print(indentString() + "=");
      ast.E.visit(this, o);
    }
    --indent;
    return null;
  }

  // Stmts

  public Object visitStmtList(StmtList ast, Object o) {
    print(indentString() + "StmtList");
    ++indent;
    ast.S.visit(this, o);
    ast.SL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitIfStmt(IfStmt ast, Object o) {

    print(indentString() + "IfStmt");
    ++indent;
    ast.E.visit(this, o);
    ast.S1.visit(this, null);
    ast.S2.visit(this, null);
    --indent;
    return null;
  }

  public Object visitWhileStmt(WhileStmt ast, Object o) {
    print(indentString() + "WhileStmt");
    ++indent;
    ast.E.visit(this, o); 
    ast.S.visit(this, o); 
    --indent;
    return null;
  }

  public Object visitForStmt(ForStmt ast, Object o) {
    print(indentString() + "ForStmt");
    ++indent;
    ast.E1.visit(this, o); 
    ast.E2.visit(this, o); 
    ast.E3.visit(this, o); 
    ast.S.visit(this, o); 
    --indent;
    return null;
  }

  public Object visitBreakStmt(BreakStmt ast, Object o) {
    print(indentString() + "BreakStmt");
    return null;
  }

  public Object visitContinueStmt(ContinueStmt ast, Object o) {
    print(indentString() + "ContinuekStmt");
    return null;
  }

  public Object visitReturnStmt(ReturnStmt ast, Object o) {
    print(indentString() + "ReturnStmt");
    ++indent;
    ast.E.visit(this, o);
    --indent;
    return null;
  }

  public Object visitCompoundStmt(CompoundStmt ast, Object o) {
    print(indentString() + "CompoundStmt");
    ++indent;
    ast.DL.visit(this, o);
    ast.SL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitExprStmt(ExprStmt ast, Object o) {
    print(indentString() + "ExprStmt");
    ++indent;
    ast.E.visit(this, o);
    --indent;
    return null;
  }

  public Object visitEmptyCompStmt(EmptyCompStmt ast, Object o) {
    print(indentString() + "EmptyCompStmt");
    return null;
  }

  public Object visitEmptyStmt(EmptyStmt ast, Object o) {
    print(indentString() + "EmptyStmt");
    return null;
  }


  // Expressions

  public Object visitAssignExpr(AssignExpr ast, Object o) {
    print(indentString() + "AssignExpr");
    ++indent;
    ast.E1.visit(this, o);
    ast.E2.visit(this, o);
    --indent;
    return null;
  }

  public Object visitBinaryExpr(BinaryExpr ast, Object o) {
    print(indentString() + "BinaryExpr");
    ++indent;
    ast.E1.visit(this, o);
    ast.O.visit(this, o);
    ast.E2.visit(this, o);
    --indent;
    return null;
  }

  public Object visitUnaryExpr(UnaryExpr ast, Object o) {
    print(indentString() + "UnaryExpr");
    ++indent;
    ast.O.visit(this, o);
    ast.E.visit(this, o);
    --indent;
    return null;
  }

  public Object visitIntExpr(IntExpr ast, Object o) {
    print(indentString() + "IntExpr");
    ++indent;
    ast.IL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitFloatExpr(FloatExpr ast, Object o) {
    print(indentString() + "FloatExpr");
    ++indent;
    ast.FL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitBooleanExpr(BooleanExpr ast, Object o) {
    print(indentString() + "BooleanExpr");
    ++indent;
    ast.BL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitStringExpr(StringExpr ast, Object o) {
    print(indentString() + "StringExpr");
    ++indent;
    ast.SL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitCallExpr(CallExpr ast, Object o) {
    print(indentString() + "CallExpr");
    ++indent;
    ast.I.visit(this, o);
    ast.AL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitVarExpr(VarExpr ast, Object o) {
    print(indentString() + "VarExpr");
    ++indent;
    ast.V.visit(this, o);
    --indent;
    return null;
  }

  public Object visitArrayExpr(ArrayExpr ast, Object o) {
    print(indentString() + "ArrayExpr");
    ++indent;
    ast.V.visit(this, o);
    ast.E.visit(this, o);
    --indent;
    return null;
  }

  public Object visitInitExpr(InitExpr ast, Object o) {
    print(indentString() + "InitExpr");
    ++indent;
    ast.IL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitExprList(ExprList ast, Object o) {
    print(indentString() + "ExprList");
    ++indent;
    ast.E.visit(this, o);
    ast.EL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitEmptyExpr(EmptyExpr ast, Object o) {
    print(indentString() + "EmptyExpr");
    return null;
  }


  // Parameters

  public Object visitParaList (ParaList ast, Object o) {
    print(indentString() + "ParaList");
    ++indent;
    ast.P.visit(this, o);
    ast.PL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitParaDecl(ParaDecl ast, Object o) {
    print(indentString() + "ParaDecl");
    ++indent;
    ast.T.visit(this, o);
    ast.I.visit(this, o);
    --indent;
    return null;
  }


  // Arguments

  public Object visitArgList(ArgList ast, Object o) {
    print(indentString() + "ArgList");
    ++indent;
    ast.A.visit(this, o);
    ast.AL.visit(this, o);
    --indent;
    return null;
  }

  public Object visitArg(Arg ast, Object o) {
    print(indentString() + "Arg");
    ++indent;
    ast.E.visit(this, o);
    --indent;
    return null;
  }

  // Types
  public Object visitBooleanType(BooleanType ast, Object o) {
    print(indentString() + "boolean");
    return null;
  }

  public Object visitIntType(IntType ast, Object o) {
    print(indentString() + "int");
    return null;
  }

  public Object visitFloatType(FloatType ast, Object o) {
    print(indentString() + "float");
    return null;
  }

  // not called
  public Object visitStringType(StringType ast, Object o) {
    print(indentString() + "string");
    return null;
  }

  public Object visitVoidType(VoidType ast, Object o) {
    print(indentString() + "void");
    return null;
  }

  public Object visitArrayType(ArrayType ast, Object o) {
    print(indentString() + "ArrayType");
    ++indent;
    ast.T.visit(this, o);
    ast.E.visit(this, o);
    --indent;
 /*
    if (ast.T instanceof IntType)
      print(indentString() + "int");
    else if (ast.T instanceof FloatType)
      print(indentString() + "float");
    else if (ast.T instanceof BooleanType)
      print(indentString() + "bool");
    else // if (ast.T instanceof VoidType)
      print(indentString() + "void");
*/
    return null;
  }


  public Object visitErrorType(ErrorType ast, Object o) {
    print(indentString() + "error");
    return null;
  }

  // Literals, Identifiers and Operators

  public Object visitIntLiteral(IntLiteral ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  public Object visitFloatLiteral(FloatLiteral ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  public Object visitBooleanLiteral(BooleanLiteral ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  public Object visitStringLiteral(StringLiteral ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  public Object visitIdent(Ident ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  public Object visitOperator(Operator ast, Object o) {
    print(indentString() + ast.spelling);
    return null;
  }

  // Variable names

  public Object visitSimpleVar(SimpleVar ast, Object o) {
    print(indentString() + "SimpleVar");
    ++indent;
    ast.I.visit(this, o);
    --indent;
    return null;
  }

}
