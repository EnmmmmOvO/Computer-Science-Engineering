/*
 * LayoutVisitor.java      
 */

package VC.TreeDrawer;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

// import VC.ASTs.Visitor;
import VC.ASTs.*;

import VC.Scanner.SourcePosition;

public class LayoutVisitor implements Visitor {

  private final int BORDER = 5;
  private final int PARENT_SEP = 30;

  private FontMetrics fontMetrics;

  private boolean debug;

  public LayoutVisitor (FontMetrics fontMetrics) {
    this.fontMetrics = fontMetrics;
    debug = false; // do not draw SourcePosition
  }

  void enableDebugging() {
    debug = true;
  }

  // Programs
  public Object visitProgram(Program ast, Object obj) {
    return layoutUnary("Program", ast.FL);
  }

 // Lists

  public Object visitEmptyDeclList(EmptyDeclList ast, Object obj) {
    return layoutNullary("EmptyDecList");
  }

  public Object visitEmptyStmtList(EmptyStmtList ast, Object obj) {
    return layoutNullary("EmptyStmtList");
  }

  public Object visitEmptyExprList(EmptyExprList ast, Object obj) {
    return layoutNullary("EmptyExprList");
  }

  public Object visitEmptyStmt(EmptyStmt ast, Object obj) {
    return layoutNullary("EmptyStmt");
  }

  public Object visitEmptyParaList(EmptyParaList ast, Object obj) {
    return layoutNullary("EmptyParaList");
  }

  public Object visitEmptyArgList(EmptyArgList ast, Object obj) {
    return layoutNullary("EmptyArgList");
  }


  // Declarations
  public Object visitDeclList(DeclList ast, Object obj) {
    return layoutBinary("DecList", ast.D, ast.DL);
  }

  public Object visitFuncDecl(FuncDecl ast, Object obj) {
    return layoutQuaternary("FunDec", ast.T, ast.I, ast.PL, ast.S);
  }

  public Object visitGlobalVarDecl(GlobalVarDecl ast, Object obj) {
    return layoutTernary("G.VarDec", ast.T, ast.I, ast.E);
  }

  public Object visitLocalVarDecl(LocalVarDecl ast, Object obj) {
    return layoutTernary("L.VarDec", ast.T, ast.I, ast.E);
  }

  // Stmts

  public Object visitStmtList(StmtList ast, Object obj) {
    return layoutBinary("StmtList", ast.S, ast.SL);
  }

  public Object visitIfStmt(IfStmt ast, Object obj) {
    if (ast.S2 instanceof EmptyStmt)
      return layoutBinary("IfStmt", ast.E, ast.S1);
    else
      return layoutTernary("IfStmt", ast.E, ast.S1, ast.S2);
  }

  public Object visitWhileStmt(WhileStmt ast, Object obj) {
    return layoutBinary("WhileStmt", ast.E, ast.S);
  }

  public Object visitForStmt(ForStmt ast, Object obj) {
    return layoutQuaternary("ForStmt", ast.E1, ast.E2, ast.E3, ast.S);
  }

  public Object visitBreakStmt(BreakStmt ast, Object obj) {
    return layoutNullary("BrkStmt");
  }

  public Object visitContinueStmt(ContinueStmt ast, Object obj) {
    return layoutNullary("ConStmt");
  }

  public Object visitReturnStmt(ReturnStmt ast, Object obj) {
    return layoutUnary("RetStmt", ast.E);
  }

  public Object visitCompoundStmt(CompoundStmt ast, Object obj) {
    return layoutBinary("CompStmt", ast.DL, ast.SL);
  }

  public Object visitExprStmt(ExprStmt ast, Object obj) {
    return layoutUnary("ExpStmt", ast.E);
  }

  public Object visitEmptyCompStmt(EmptyCompStmt ast, Object obj) {
    return layoutNullary("EmptyCompStmt");
  }


  // Expressions

  public Object visitAssignExpr(AssignExpr ast, Object obj) {
    return layoutBinary("AssignExp", ast.E1, ast.E2);
  }

  public Object visitBinaryExpr(BinaryExpr ast, Object obj) {
    return layoutTernary("BinExp", ast.E1, ast.O, ast.E2);
  }

  public Object visitUnaryExpr(UnaryExpr ast, Object obj) {
    return layoutBinary("UnaExp", ast.O, ast.E);
  }

  public Object visitIntExpr(IntExpr ast, Object obj) {
    return layoutUnary("IntExp", ast.IL);
  }

  public Object visitStringExpr(StringExpr ast, Object obj) {
    return layoutUnary("StrExp", ast.SL);
  }

  public Object visitFloatExpr(FloatExpr ast, Object obj) {
    return layoutUnary("FloatExp", ast.FL);
  }

  public Object visitBooleanExpr(BooleanExpr ast, Object obj) {
    return layoutUnary("BoolExp", ast.BL);
  }

  public Object visitCallExpr(CallExpr ast, Object obj) {
    return layoutBinary("CallExp", ast.I, ast.AL);
  }

  public Object visitVarExpr(VarExpr ast, Object obj) {
    return layoutUnary("VarExp", ast.V);
  }

  public Object visitArrayExpr(ArrayExpr ast, Object obj) {
    return layoutBinary("ArrExp", ast.V, ast.E);
  }

  public Object visitInitExpr(InitExpr ast, Object obj) {
    return layoutUnary("InitExp", ast.IL);
  }

  public Object visitExprList(ExprList ast, Object obj) {
    return layoutBinary("ExprList", ast.E, ast.EL);
  }

  public Object visitEmptyExpr(EmptyExpr ast, Object obj) {
    return layoutNullary("EmptyExp");
  }

  // Formal Parameters

  public Object visitParaList (ParaList ast, Object obj) {
    return layoutBinary("ParaLst", ast.P, ast.PL);
  }

  public Object visitParaDecl(ParaDecl ast, Object obj) {
    return layoutBinary("ParaDec", ast.T, ast.I);
  }

  // Arguments

  public Object visitArgList(ArgList ast, Object obj) {
    return layoutBinary("ArgList", ast.A, ast.AL);
  }

  public Object visitArg(Arg ast, Object obj) {
    return layoutUnary("Arg", ast.E);
  }


  // Types

  public Object visitBooleanType(BooleanType ast, Object obj) {
    return layoutNullary("bool");
  }

  public Object visitIntType(IntType ast, Object obj) {
    return layoutNullary("int");
  }

  public Object visitFloatType(FloatType ast, Object obj) {
    return layoutNullary("float");
  }

  public Object visitVoidType(VoidType ast, Object obj) {
    return layoutNullary("void");
  }

  // not called
  public Object visitStringType(StringType ast, Object obj) {
    return layoutNullary("string");
  }

  public Object visitArrayType(ArrayType ast, Object obj) {
    return layoutBinary("ArrType", ast.T, ast.E);
  }

  public Object visitErrorType(ErrorType ast, Object obj) {
    return layoutNullary("err");
  }

  // Literals, Identifiers and Operators

  public Object visitIntLiteral(IntLiteral ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  public Object visitFloatLiteral(FloatLiteral ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  public Object visitBooleanLiteral(BooleanLiteral ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  public Object visitStringLiteral(StringLiteral ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  public Object visitIdent(Ident ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  public Object visitOperator(Operator ast, Object obj) {
    return layoutNullary(ast.spelling);
  }

  // Variable names

  public Object visitSimpleVar(SimpleVar ast, Object obj) {
    return layoutUnary("SimVar", ast.I);
  }

//   for lecture 7 only
//  public Object visitS(S ast, Object obj) {
//     return layoutUnary("S", ast.E);
// }

  private DrawingTree layoutCaption (String name) {
    int w = fontMetrics.stringWidth(name) + 4;
    int h = fontMetrics.getHeight() + 4;
    return new DrawingTree(name, w, h, fontMetrics);
  }

  private DrawingTree layoutNullary (String name) {
    DrawingTree dt = layoutCaption(name);
    dt.contour.upper_tail = new Polyline(0, dt.height + 2 * BORDER, null);
    dt.contour.upper_head = dt.contour.upper_tail;
    dt.contour.lower_tail = new Polyline(-dt.width - 2 * BORDER, 0, null);
    dt.contour.lower_head = new Polyline(0, dt.height + 2 * BORDER, dt.contour.lower_tail);
    return dt;
  }

  private DrawingTree layoutUnary (String name, AST child1) {
    if (debug) {
      SourcePosition pos = child1.parent.position;
      name += " " + pos.lineStart 
              + "(" + pos.charStart + ").." 
              + pos.lineFinish+ "(" 
              + pos.charFinish + ")";
    }
    DrawingTree dt = layoutCaption(name);
    DrawingTree d1 = (DrawingTree) child1.visit(this, null);
    dt.setChildren(new DrawingTree[] {d1});
    attachParent(dt, join(dt));
    return dt;
  }

  private DrawingTree layoutBinary (String name, AST child1, AST child2) {
    if (debug) {
      SourcePosition pos = child1.parent.position;
      name += " " + pos.lineStart 
              + "(" + pos.charStart + ").." 
              + pos.lineFinish+ "(" 
              + pos.charFinish + ")";
    }
    DrawingTree dt = layoutCaption(name);
    DrawingTree d1 = (DrawingTree) child1.visit(this, null);
    DrawingTree d2 = (DrawingTree) child2.visit(this, null);
    dt.setChildren(new DrawingTree[] {d1, d2});
    attachParent(dt, join(dt));
    return dt;
  }

  private DrawingTree layoutTernary (String name, AST child1, AST child2,
                                     AST child3) {
    if (debug) {
      SourcePosition pos = child1.parent.position;
      name += " " + pos.lineStart 
              + "(" + pos.charStart + ").." 
              + pos.lineFinish+ "(" 
              + pos.charFinish + ")";
    }
    DrawingTree dt = layoutCaption(name);
    DrawingTree d1 = (DrawingTree) child1.visit(this, null);
    DrawingTree d2 = (DrawingTree) child2.visit(this, null);
    DrawingTree d3 = (DrawingTree) child3.visit(this, null);
    dt.setChildren(new DrawingTree[] {d1, d2, d3});
    attachParent(dt, join(dt));
    return dt;
  }

  private DrawingTree layoutQuaternary (String name, AST child1, AST child2,
                                        AST child3, AST child4) {
    if (debug) {
      SourcePosition pos = child1.parent.position;
      name += " " + pos.lineStart 
              + "(" + pos.charStart + ").." 
              + pos.lineFinish+ "(" 
              + pos.charFinish + ")";
    }
    DrawingTree dt = layoutCaption(name);
    DrawingTree d1 = (DrawingTree) child1.visit(this, null);
    DrawingTree d2 = (DrawingTree) child2.visit(this, null);
    DrawingTree d3 = (DrawingTree) child3.visit(this, null);
    DrawingTree d4 = (DrawingTree) child4.visit(this, null);
    dt.setChildren(new DrawingTree[] {d1, d2, d3, d4});
    attachParent(dt, join(dt));
    return dt;
  }

  private void attachParent(DrawingTree dt, int w) {
    int y = PARENT_SEP;
    int x2 = (w - dt.width) / 2 - BORDER;
    int x1 = x2 + dt.width + 2 * BORDER - w;

    dt.children[0].offset.y = y + dt.height;
    dt.children[0].offset.x = x1;
    dt.contour.upper_head = new Polyline(0, dt.height,
                                new Polyline(x1, y, dt.contour.upper_head));
    dt.contour.lower_head = new Polyline(0, dt.height,
                                new Polyline(x2, y, dt.contour.lower_head));
  }

  private int join (DrawingTree dt) {
    int w, sum;

    dt.contour = dt.children[0].contour;
    sum = w = dt.children[0].width + 2 * BORDER;

    for (int i = 1; i < dt.children.length; i++) {
      int d = merge(dt.contour, dt.children[i].contour);
      dt.children[i].offset.x = d + w;
      dt.children[i].offset.y = 0;
      w = dt.children[i].width + 2 * BORDER;
      sum += d + w;
    }
    return sum;
  }

  private int merge(Polygon c1, Polygon c2) {
    int x, y, total, d;
    Polyline lower, upper, b;

    x = y = total = 0;
    upper = c1.lower_head;
    lower = c2.upper_head;

    while (lower != null && upper != null) {
        d = offset(x, y, lower.dx, lower.dy, upper.dx, upper.dy);
	x += d;
	total += d;

	if (y + lower.dy <= upper.dy) {
	  x += lower.dx;
	  y += lower.dy;
	  lower = lower.link;
	} else {
	  x -= upper.dx;
	  y -= upper.dy;
	  upper = upper.link;
	}
      }

      if (lower != null) {
        b = bridge(c1.upper_tail, 0, 0, lower, x, y);
        c1.upper_tail = (b.link != null) ? c2.upper_tail : b;
        c1.lower_tail = c2.lower_tail;
      } else {
        b = bridge(c2.lower_tail, x, y, upper, 0, 0);
        if (b.link == null) {
          c1.lower_tail = b;
        }
      }

      c1.lower_head = c2.lower_head;

      return total;
    }

  private int offset (int p1, int p2, int a1, int a2, int b1, int b2) {
    int d, s, t;

    if (b2 <= p2 || p2 + a2 <= 0) {
      return 0;
    }

    t = b2 * a1 - a2 * b1;
    if (t > 0) {
      if (p2 < 0) {
        s = p2 * a1;
        d = s / a2 - p1;
      } else if (p2 > 0) {
        s = p2 * b1;
        d = s / b2 - p1;
      } else {
        d = -p1;
      }
    } else if (b2 < p2 + a2) {
      s = (b2 - p2) * a1;
      d = b1 - (p1 + s / a2);
    } else if (b2 > p2 + a2) {
      s = (a2 + p2) * b1;
      d = s / b2 - (p1 + a1);
    } else {
      d = b1 - (p1 + a1);
    }

    if (d > 0) {
      return d;
    } else {
      return 0;
    }
  }

  private Polyline bridge (Polyline line1, int x1, int y1,
                           Polyline line2, int x2, int y2) {
    int dy, dx, s;
    Polyline r;

    dy = y2 + line2.dy - y1;
    if (line2.dy == 0) {
      dx = line2.dx;
    } else {
      s = dy * line2.dx;
      dx = s / line2.dy;
    }

    r = new Polyline(dx, dy, line2.link);
    line1.link = new Polyline(x2 + line2.dx - dx - x1, 0, r);

    return r;
  }

}
