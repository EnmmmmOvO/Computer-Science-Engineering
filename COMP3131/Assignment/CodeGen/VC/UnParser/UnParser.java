/*
 * UnParser.java      
 *
 * This tool was written for the purposes of auto-marking assignment 3.
 *
 * But it also serves to demonstrate that the visitor design pattern is 
 * a useful OO technique for building modern software tools such as 
 * code generators. In addition, it also shows that how understanding
 * a few compiling techniques will allow one to construct easily tools 
 * such as pretty printers and translators between languages of similar 
 * programming styles. For example, it is fairly straightforward to
 * write a converter between C and Pascal.
 *
 * --- Jingling
 */

package VC.UnParser;


import VC.ASTs.*;
import java.io.FileWriter;
import java.io.PrintWriter;

public class UnParser implements Visitor {

  private int level;
  private boolean firstFunction; 
  private PrintWriter textOut;
  
  private char[] escapeChars = { '\b', '\f', '\n', '\r', '\t', '\'', '\"', '\\' };      
  private String[] escapeStrings = { "\\b", "\\f", "\\n", "\\r", "\\t", "\\\'",
"\\\"", "\\\\" };      

  public UnParser(String filename) {
    // By definition, all function declarations are in scope level 1
    level = 1;
    firstFunction = true; 

    try {
      textOut = new PrintWriter(new FileWriter(filename));
    } catch (java.io.IOException e) {
      System.out.println("Caught IOException: " + e.getMessage());
      System.exit(1);
    }
  }

  public final void unparse(AST ast) {
    ast.visit(this, null);
    textOut.close();
  }

  String  addEscape(String s) {
    StringBuffer t = new StringBuffer();
    for (int i=0; i < s.length(); i++) {
      boolean flag = false;
      for (int j=0; j < escapeChars.length; j++) {
        if (s.charAt(i) == escapeChars[j]) {
 	  flag = true;	   
          t.append(escapeStrings[j]);
        }
      }
      if (!flag) 
 	t.append(s.charAt(i));
    }
    return t.toString();
  }

  void  printIndentation() {
    if (firstFunction)
      firstFunction = false; // no newline for the first line
    else
      textOut.println();
    for (int i=1; i <= 2 * (level-1) ; i++)
      textOut.print(" ");
  }

  void  print(String s) {
    textOut.print(s);
  }


  // Programs
  public Object visitProgram(Program ast, Object o) {
    ast.FL.visit(this, o);
    textOut.println();
    return null;
  }

 // Lists

  public Object visitEmptyDeclList(EmptyDeclList ast, Object o) {
    return null;
  }

  public Object visitEmptyStmtList(EmptyStmtList ast, Object o) {
    return null;
  }

  public Object visitEmptyExprList(EmptyExprList ast, Object o) {
    return null;
  }

  public Object visitEmptyParaList(EmptyParaList ast, Object o) {
    print(")");
    return null;
  }

  public Object visitEmptyArgList(EmptyArgList ast, Object o) {
    print(")");
    return null;
  }


  // Declarations
  public Object visitDeclList(DeclList ast, Object o) {
    ast.D.visit(this, o);
    ast.DL.visit(this, o);
    return null;
  }

  public Object visitFuncDecl(FuncDecl ast, Object o) {
    printIndentation();
    ast.T.visit(this, o);
    print(" ");
    ast.I.visit(this, o);
    print("(");
    ast.PL.visit(this, o);
    ast.S.visit(this, o); // must be a block
    return null;
  }

/*
  public Object visitGlobalVarDecl(GlobalVarDecl ast, Object o) {
    printIndentation();
    ast.T.visit(this, o);
    print(" ");
    ast.I.visit(this, o);
    if (! (ast.E instanceof EmptyExpr)) {
      print(" = ");
      ast.E.visit(this, o);
    }
    print(";");
    return null;
  }
*/

  public Object visitGlobalVarDecl(GlobalVarDecl ast, Object o) {
    printIndentation();
    ast.T.visit(this, o);
    print(" ");
    ast.I.visit(this, o);
    if (ast.T instanceof ArrayType) {
      print("[");
      if (! (((ArrayType)ast.T).E instanceof EmptyExpr)) {
        ((ArrayType)ast.T).E.visit(this, o);
      }
      print("]");
    }
    if (! (ast.E instanceof EmptyExpr)) {
      print(" = ");
      ast.E.visit(this, o);
    }
    print(";");
    return null;
  }

  public Object visitLocalVarDecl(LocalVarDecl ast, Object o) {
    printIndentation();
    ast.T.visit(this, o);
    print(" ");
    ast.I.visit(this, o);
    if (ast.T instanceof ArrayType) {
      print("[");
      if (! (((ArrayType)ast.T).E instanceof EmptyExpr)) {
        ((ArrayType)ast.T).E.visit(this, o);
      }
      print("]");
    }
    if (! (ast.E instanceof EmptyExpr)) {
      print(" = ");
      ast.E.visit(this, o);
    }
    print(";");
    return null;
  }

  // Stmts

  public Object visitStmtList(StmtList ast, Object o) {
    ast.S.visit(this, o);
    ast.SL.visit(this, o);
    return null;
  }

  public Object visitIfStmt(IfStmt ast, Object o) {

    if (o == null || !(o instanceof IfStmt)) { // the first if
      printIndentation();
      print("if (");
    } else
      print(" if ("); // else if statement
    ast.E.visit(this, o);
    print(")");
    if (ast.S1 instanceof CompoundStmt)
      ast.S1.visit(this, null);
    else { // the if has a single statement
      level++;
      ast.S1.visit(this, null);
      level--;
    }
    if (! (ast.S2 instanceof EmptyStmt)) {
      printIndentation();
      print("else");
      if (ast.S2 instanceof IfStmt)
        // pass ast to let visitIfStmt know that this is else if
        ast.S2.visit(this, ast);
      else if (ast.S2 instanceof CompoundStmt) 
        ast.S2.visit(this, null);
      else {
        level++;
        ast.S2.visit(this, ast);
        level--;
      }
    }
    return null;
  }

  public Object visitWhileStmt(WhileStmt ast, Object o) {
    printIndentation();
    print("while (");
    ast.E.visit(this, o); 
    print(")");
    if (! (ast.S instanceof CompoundStmt))
      level++;
    ast.S.visit(this, o); 
    if (! (ast.S instanceof CompoundStmt))
      level--;
    return null;
  }

  public Object visitForStmt(ForStmt ast, Object o) {
    printIndentation();
    print("for (");
    ast.E1.visit(this, o); 
    print(";");
    ast.E2.visit(this, o); 
    print(";");
    ast.E3.visit(this, o); 
    print(")");
    if (! (ast.S instanceof CompoundStmt))
      level++;
    ast.S.visit(this, o); 
    if (! (ast.S instanceof CompoundStmt))
      level--;
    return null;
  }

  public Object visitBreakStmt(BreakStmt ast, Object o) {
    printIndentation();
    print("break;");
    return null;
  }

  public Object visitContinueStmt(ContinueStmt ast, Object o) {
    printIndentation();
    print("continue;");
    return null;
  }

  public Object visitReturnStmt(ReturnStmt ast, Object o) {
    printIndentation();
    print("return ");
    ast.E.visit(this, o);
    print(";");
    return null;
  }

  public Object visitCompoundStmt(CompoundStmt ast, Object o) {
    printIndentation();
    print("{");
    level++;
    ast.DL.visit(this, o);
    ast.SL.visit(this, o);
    level--;
    printIndentation();
    print("}");
    return null;
  }

  public Object visitExprStmt(ExprStmt ast, Object o) {
    printIndentation();
    ast.E.visit(this, o);
    print(";");
    return null;
  }

  public Object visitEmptyCompStmt(EmptyCompStmt ast, Object o) {
    printIndentation();
    print("{");
    printIndentation();
    print("}");
    return null;
  }

  public Object visitEmptyStmt(EmptyStmt ast, Object o) {
    return null;
  }


  // Expressions

  public Object visitAssignExpr(AssignExpr ast, Object o) {
    print("(");
    ast.E1.visit(this, o);
    print("=");
    ast.E2.visit(this, o);
    print(")");
    return null;
  }

  public Object visitBinaryExpr(BinaryExpr ast, Object o) {
    print("(");
    ast.E1.visit(this, o);
    ast.O.visit(this, o);
    ast.E2.visit(this, o);
    print(")");
    return null;
  }

  public Object visitUnaryExpr(UnaryExpr ast, Object o) {
    ast.O.visit(this, o);
    ast.E.visit(this, o);
    return null;
  }

  public Object visitIntExpr(IntExpr ast, Object o) {
    return ast.IL.visit(this, o);
  }

  public Object visitFloatExpr(FloatExpr ast, Object o) {
    return ast.FL.visit(this, o);
  }

  public Object visitBooleanExpr(BooleanExpr ast, Object o) {
    return ast.BL.visit(this, o);
  }

  public Object visitStringExpr(StringExpr ast, Object o) {
    return ast.SL.visit(this, o);
  }

  public Object visitCallExpr(CallExpr ast, Object o) {
    ast.I.visit(this, o);
    print("(");
    ast.AL.visit(this, o);
    return null;
  }

  public Object visitVarExpr(VarExpr ast, Object o) {
    ast.V.visit(this, o);
    return null;
  }

  public Object visitArrayExpr(ArrayExpr ast, Object o) {
    ast.V.visit(this, o);
    print("[");
    ast.E.visit(this, o);
    print("]");
    return null;
  }

  public Object visitInitExpr(InitExpr ast, Object o) {
    print("{");
    ast.IL.visit(this, o);
    print("}");
    return null;
  }

  public Object visitExprList(ExprList ast, Object o) {
    ast.E.visit(this, o);
    if (! (ast.EL instanceof EmptyExprList))
      print(",");
    ast.EL.visit(this, o);
    return null;
  }

  public Object visitEmptyExpr(EmptyExpr ast, Object o) {
    return null;
  }


  // Parameters

  public Object visitParaList (ParaList ast, Object o) {
    ast.P.visit(this, o);
    if (! (ast.PL instanceof EmptyParaList))
      print(", ");
    ast.PL.visit(this, o);
    return null;
  }

  public Object visitParaDecl(ParaDecl ast, Object o) {
    ast.T.visit(this, o);
    print(" ");
    ast.I.visit(this, o);
    if (ast.T instanceof ArrayType) {
      print("[");
      if (! (((ArrayType)ast.T).E instanceof EmptyExpr)) {
        ((ArrayType)ast.T).E.visit(this, o);
      }
      print("]");
    }
    return null;
  }

  // Arguments

  public Object visitArgList(ArgList ast, Object o) {
    ast.A.visit(this, o);
    if (! (ast.AL instanceof EmptyArgList))
      print(", ");
    ast.AL.visit(this, o);
    return null;
  }

  public Object visitArg(Arg ast, Object o) {
    ast.E.visit(this, o);
    return null;
  }


  // Types

  public Object visitBooleanType(BooleanType ast, Object o) {
    print("boolean");
    return null;
  }

  public Object visitIntType(IntType ast, Object o) {
    print("int");
    return null;
  }

  public Object visitFloatType(FloatType ast, Object o) {
    print("float");
    return null;
  }

  // not called
  public Object visitStringType(StringType ast, Object o) {
    print("string");
    return null;
  }

  public Object visitVoidType(VoidType ast, Object o) {
    print("void");
    return null;
  }

  public Object visitArrayType(ArrayType ast, Object o) {
    ast.T.visit(this, o);
    return null;
  }

  public Object visitErrorType(ErrorType ast, Object o) {
    print("error");
    return null;
  }

  // Literals, Identifiers and Operators

  public Object visitIntLiteral(IntLiteral ast, Object o) {
    print(ast.spelling);
    return null;
  }

  public Object visitFloatLiteral(FloatLiteral ast, Object o) {
    print(ast.spelling);
    return null;
  }

  public Object visitBooleanLiteral(BooleanLiteral ast, Object o) {
    print(ast.spelling);
    return null;
  }

  public Object visitStringLiteral(StringLiteral ast, Object o) {
    print("\"");
    print(addEscape(ast.spelling));
    print("\"");
    return null;
  }

  public Object visitIdent(Ident ast, Object o) {
    print(ast.spelling);
    return null;
  }

  public Object visitOperator(Operator ast, Object o) {
    print(ast.spelling);
    return null;
  }

  // Variable names

  public Object visitSimpleVar(SimpleVar ast, Object o) {
    ast.I.visit(this, o);
    return null;
  }

}
