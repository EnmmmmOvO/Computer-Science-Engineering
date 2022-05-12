/***
 * Checker.java   
 * Sat 12 Mar 17:17:12 AEDT 2022
 ****/

package VC.Checker;

import VC.ASTs.*;
import VC.Scanner.SourcePosition;
import VC.ErrorReporter;
import VC.StdEnvironment;

public final class Checker implements Visitor {

    private String errMesg[] = {
        "*0: main function is missing",                            
        "*1: return type of main is not int",                    

        // defined occurrences of identifiers
        // for global, local and parameters
        "*2: identifier redeclared",                             
        "*3: identifier declared void",                         
        "*4: identifier declared void[]",                      

        // applied occurrences of identifiers
        "*5: identifier undeclared",                          

        // assignments
        "*6: incompatible type for =",                       
        "*7: invalid lvalue in assignment",                 

        // types for expressions 
        "*8: incompatible type for return",                
        "*9: incompatible type for this binary operator", 
        "*10: incompatible type for this unary operator",

        // scalars
        "*11: attempt to use an array/function as a scalar", 

        // arrays
        "*12: attempt to use a scalar/function as an array",
        "*13: wrong type for element in array initialiser",
        "*14: invalid initialiser: array initialiser for scalar",   
        "*15: invalid initialiser: scalar initialiser for array",  
        "*16: excess elements in array initialiser",              
        "*17: array subscript is not an integer",                
        "*18: array size missing",                              

        // functions
        "*19: attempt to reference a scalar/array as a function",

        // conditional expressions in if, for and while
        "*20: if conditional is not boolean",                    
        "*21: for conditional is not boolean",                  
        "*22: while conditional is not boolean",               

        // break and continue
        "*23: break must be in a while/for",                  
        "*24: continue must be in a while/for",              

        // parameters 
        "*25: too many actual parameters",                  
        "*26: too few actual parameters",                  
        "*27: wrong type for actual parameter",           

        // reserved for errors that I may have missed (J. Xue)
        "*28: misc 1",
        "*29: misc 2",

        // the following two checks are optional 
        "*30: statement(s) not reached",     
        "*31: missing return statement",    
    };


    private SymbolTable idTable;
    private static SourcePosition dummyPos = new SourcePosition();
    private ErrorReporter reporter;
    public int WhileTime = 0;

    // Checks whether the source program, represented by its AST, 
    // satisfies the language's scope rules and type rules.
    // Also decorates the AST as follows:
    //  (1) Each applied occurrence of an identifier is linked to
    //      the corresponding declaration of that identifier.
    //  (2) Each expression and variable is decorated by its type.

    public Checker (ErrorReporter reporter) {
        this.reporter = reporter;
        this.idTable = new SymbolTable ();
        establishStdEnvironment();
    }
    
    public void check(AST ast) {
        ast.visit(this, null);
    }

    // auxiliary methods

    private void declareVariable(Ident ident, Decl decl) {
        IdEntry entry = idTable.retrieveOneLevel(ident.spelling);
        if (entry != null) {
            reporter.reportError(errMesg[2] + ": %", ident.spelling, ident.position);
        }
    
        idTable.insert(ident.spelling, decl);
    }

    private void declareFunction(Ident ident, Decl decl) {
        IdEntry entry = idTable.retrieveOneLevel(ident.spelling);
        if (entry != null) {
            reporter.reportError(errMesg[2] + ": %", ident.spelling, ident.position);
        }

        idTable.insert(ident.spelling, decl);
    }

    // ProgramsreportError

    public Object visitProgram(Program ast, Object o) {
        ast.FL.visit(this, null);
        Decl decl = idTable.retrieve("main");
        if (decl != null && decl instanceof FuncDecl) {
            if (!StdEnvironment.intType.equals(((FuncDecl)decl).T))
                reporter.reportError(errMesg[1], "", ast.position);
        } else {
            reporter.reportError(errMesg[0], "", ast.position);
        }

        return null;
    }

    void reportError(String string, Type type, String string1, SourcePosition Pos) {
        if (type == StdEnvironment.errorType) {
            reporter.reportError(string, "", Pos);
        } else {
            reporter.reportError(string + " (found: " + type + ", required: " + string1 + ")", "", Pos);
        }

    }

    private Expr checkAss(Type type, Expr expr, String string, SourcePosition Pos) {
        if (!type.assignable(expr.type)) {
            reporter.reportError(string, "", Pos);
        } else if (!type.equals(expr.type)) {
            return checkIf(expr);
        }

        return expr;
    }

    private Expr checkIf(Expr expr) {
        UnaryExpr uexpr = new UnaryExpr(new Operator("checkIf", expr.position), expr, expr.position);
        uexpr.type = StdEnvironment.floatType;
        uexpr.parent = expr;
        return uexpr;
    }


    // Statements

    public Object visitIfStmt(IfStmt ast, Object o) {
        Type type = (Type)ast.E.visit(this, null);
        if (!type.equals(StdEnvironment.booleanType)) 
            reporter.reportError(errMesg[20] + " (found: " + type.toString() + ")", "", ast.E.position);

        ast.S1.visit(this, o);
        ast.S2.visit(this, o);

        return null;
    }

    public Object visitCompoundStmt(CompoundStmt ast, Object o) {
        idTable.openScope();

        if (o != null && o instanceof FuncDecl) {
            FuncDecl decl = (FuncDecl)o;
            decl.PL.visit(this, null);

            ast.DL.visit(this, null);
            ast.SL.visit(this, decl.T.visit(this, null));
        } else {
            ast.DL.visit(this, null);
            ast.SL.visit(this, o);
        }

        idTable.closeScope();
        return null;
    }

    public Object visitForStmt(ForStmt ast, Object o) {
        WhileTime++;

        ast.E1.visit(this, null);
        Type type = (Type)ast.E2.visit(this, null);
        if (!ast.E2.isEmptyExpr() && !type.equals(StdEnvironment.booleanType))
            reporter.reportError(errMesg[21] + " (found: " + type.toString() + ")", "", ast.E2.position);

        ast.E3.visit(this, null);
        ast.S.visit(this, o);
        
        WhileTime--;
        return null;
    }

    public Object visitWhileStmt(WhileStmt ast, Object o) {
        WhileTime++;

        Type type = (Type)ast.E.visit(this, null);
        if (!type.equals(StdEnvironment.booleanType))
            reporter.reportError(errMesg[22] + " (found: " + type.toString() + ")", "", ast.E.position);

        ast.S.visit(this, o);

        WhileTime--;
        return null;
    }

    public Object visitBreakStmt(BreakStmt ast, Object o) {
        if (WhileTime < 1) 
            reporter.reportError(errMesg[23], "", ast.position);

        return null;
    }

    public Object visitContinueStmt(ContinueStmt ast, Object o) {
        if (WhileTime < 1) 
            reporter.reportError(errMesg[24], "", ast.position);

        return null;
    }

    public Object visitReturnStmt(ReturnStmt ast, Object o) {

        ast.E.visit(this, o);
        ast.E = checkAss((Type)o, ast.E, errMesg[8], ast.position);
        
        return null;
    }

    public Object visitExprStmt(ExprStmt ast, Object o) {
        ast.E.visit(this, o);
        return null;
    }

    public Object visitEmptyCompStmt(EmptyCompStmt ast, Object o) {
        idTable.openScope();
        
        if (o != null && o instanceof FuncDecl) {
            FuncDecl var3 = (FuncDecl)o;
            var3.PL.visit(this, (Object)null);
        }

        idTable.closeScope();
        return null;
    }

    public Object visitEmptyStmt(EmptyStmt ast, Object o) {
        return null;
    }

    public Object visitStmtList(StmtList ast, Object o) {
        ast.S.visit(this, o);
        if (ast.S instanceof ReturnStmt && ast.SL instanceof StmtList)
            reporter.reportError(errMesg[30], "", ast.SL.position);
        ast.SL.visit(this, o);
        return null;
    }

    public Object visitEmptyStmtList(EmptyStmtList ast, Object o) {
        return null;
    }

    // Returns the Type denoting the type of the expression. Does
    // not use the given object.

    // Expressions

    public Object visitExprList(ExprList ast, Object o) {

        ast.E.visit(this, o);
        ast.E = checkAss((Type)o, ast.E, errMesg[13] + ": at position " + ast.index, ast.E.position);
        if (ast.EL instanceof ExprList) {
            ((ExprList)ast.EL).index = ast.index + 1;
            return ast.EL.visit(this, o);
        } else {
            return ast.index + 1;
        }
    }

    public Object visitEmptyExprList(EmptyExprList ast, Object var2) {
        return null;
    }

    public Object visitBinaryExpr(BinaryExpr ast, Object o) {
    
        Type typeE1 = (Type)ast.E1.visit(this, o);
        Type typeE2 = (Type)ast.E2.visit(this, o);
    
        Type tempType = typeE1;
        
        String spelling = ast.O.spelling;
    
        boolean check = false;
        boolean checkAndOr = ast.O.spelling.equals("&&") || ast.O.spelling.equals("||");
        boolean CheckEqNeq = ast.O.spelling.equals("==") || ast.O.spelling.equals("!=");
        boolean CheckGtSt = ast.O.spelling.equals("<=") || ast.O.spelling.equals(">=") 
                            || ast.O.spelling.equals("<") || ast.O.spelling.equals(">");
        
        if (!typeE1.isErrorType() && !typeE2.isErrorType()) {
            if (!typeE1.isVoidType() && !typeE2.isVoidType()) {
                if (!typeE1.isStringType() && !typeE2.isStringType()) {
                    if (!typeE1.isArrayType() && !typeE2.isArrayType()) {
                        if (!typeE1.isBooleanType() && !typeE2.isBooleanType()) {
                            if (checkAndOr) {
                                check = true;
                            } else if (!typeE1.equals(typeE2)) {
                                tempType = StdEnvironment.floatType;
                                ast.O.spelling = "f" + ast.O.spelling;
                                if (!tempType.equals(typeE1)) {
                                    ast.E1 = checkIf(ast.E1);
                                } else {
                                    ast.E2 = checkIf(ast.E2);
                                }
                            } else if (typeE1.isFloatType()) {
                                ast.O.spelling = "f" + ast.O.spelling;
                            } else {
                                ast.O.spelling = "i" + ast.O.spelling;
                            }
                        } else {
                            if (!typeE1.equals(typeE2) || !checkAndOr && !CheckEqNeq) {
                                check = true;
                            }
    
                            ast.O.spelling = "i" + ast.O.spelling;
                        }
                    } else {
                        check = true;
                    }
                } else {
                    check = true;
                }
            } else {
                check = true;
            }
        } else {
            tempType = StdEnvironment.errorType;
        }
    
        if (check) {
            reporter.reportError(errMesg[9] + ": %", spelling, ast.position);
            tempType = StdEnvironment.errorType;
        }
    
        ast.type = !CheckEqNeq && !CheckGtSt ? tempType : StdEnvironment.booleanType;
        return ast.type;

    }

    public Object visitAssignExpr(AssignExpr ast, Object o) {
        ast.E1.visit(this, o);
        ast.E2.visit(this, null);
    
        if (!(ast.E1 instanceof VarExpr) && !(ast.E1 instanceof ArrayExpr)) {
            reporter.reportError(errMesg[7], "", ast.position);
        } else if (ast.E1 instanceof VarExpr) {
            SimpleVar simvar = (SimpleVar)((SimpleVar)((VarExpr)ast.E1).V);
            Decl decl = (Decl)simvar.I.decl;
            if (decl instanceof FuncDecl) {
                reporter.reportError(errMesg[7] + ": %", simvar.I.spelling, ast.position);
            }
        }
    
        ast.E2 = checkAss(ast.E1.type, ast.E2, errMesg[6], ast.position);
        ast.type = ast.E2.type;
        return ast.type;
    }

    

    public Object visitUnaryExpr(UnaryExpr ast, Object o) {
        Type type = (Type)ast.E.visit(this, o);
        boolean check = false;
    
        if (type.isErrorType()) {
            type = StdEnvironment.errorType;
        } else if (!type.isVoidType() && !type.isStringType() && !type.isArrayType()) {
            if (ast.O.spelling.equals("!") && !type.isBooleanType() || !ast.O.spelling.equals("!") && type.isBooleanType()) 
                check = true;
        } else {
            check = true;
        }
    
        if (check) {
            reporter.reportError(errMesg[10] + ": %", ast.O.spelling, ast.position);
            type = StdEnvironment.errorType;
        } else if (type.isFloatType()) {
            ast.O.spelling = "f" + ast.O.spelling;
        } else
            ast.O.spelling = "i" + ast.O.spelling;
    
        ast.type = type;
        return ast.type;
    }

    public Object visitCallExpr(CallExpr ast, Object o) {
        Decl decl = (Decl)ast.I.visit(this, null);
        if (decl == null) {
            reporter.reportError(errMesg[5] + ": %", ast.I.spelling, ast.position);
            return StdEnvironment.errorType;
        } else if (decl instanceof FuncDecl) {
            ast.AL.visit(this, ((FuncDecl)decl).PL);
            return ((FuncDecl)decl).T;
        } else {
            reporter.reportError(errMesg[19] + ": %", ast.I.spelling, ast.I.position);
            return StdEnvironment.errorType;
        }
    }
    

    public Object visitArrayExpr(ArrayExpr ast, Object o) {
        Type type = (Type)ast.V.visit(this, o);
        if (type.isArrayType()) {
            type = ((ArrayType)type).T;
        } else if (!type.isErrorType()) {
            reporter.reportError(errMesg[12], "", ast.position);
            type = StdEnvironment.errorType;
        }
    
    
        Type t = (Type)ast.E.visit(this, o);
        if (!t.isIntType() && !t.isErrorType()) 
            reporter.reportError(errMesg[17], "", ast.position);
    
        ast.type = type;
        return type;
    }

    public Object visitInitExpr(InitExpr ast, Object o) {

        if (!((Type)o).isArrayType()) {
            reporter.reportError(errMesg[14], " ", ast.position);
            ast.type = StdEnvironment.errorType;
            return ast.type;
        } else {
            return ast.IL.visit(this, ((ArrayType)o).T);
        }
    }

    public Object visitEmptyExpr(EmptyExpr ast, Object o) {
        if (ast.parent instanceof ReturnStmt) {
            ast.type = StdEnvironment.voidType;
        } else {
            ast.type = StdEnvironment.errorType;
        }
    
        return ast.type;
    }

    public Object visitBooleanExpr(BooleanExpr ast, Object o) {
        ast.type = StdEnvironment.booleanType;
        return ast.type;
    }
    
    public Object visitIntExpr(IntExpr ast, Object o) {
        ast.type = StdEnvironment.intType;
        return ast.type;
    }
    
    public Object visitFloatExpr(FloatExpr ast, Object o) {
        ast.type = StdEnvironment.floatType;
        return ast.type;
    }
    
    public Object visitStringExpr(StringExpr ast, Object o) {
        ast.type = StdEnvironment.stringType;
        return ast.type;
    }
    
    public Object visitVarExpr(VarExpr ast, Object o) {
        ast.type = (Type) ast.V.visit(this, null);
        return ast.type;
    }

    // Declarations

    // Always returns null. Does not use the given object.
    
    public Object visitFuncDecl(FuncDecl ast, Object o) {    
        // Your code goes here
    
        // HINT
        // Pass ast as the 2nd argument (as done below) so that the
        // formal parameters of the function an be extracted from ast when the
        // function body is later visited
    
        declareFunction(ast.I, ast);
        if (ast.S.isEmptyCompStmt() && !ast.T.equals(StdEnvironment.voidType))
            reporter.reportError(errMesg[31], "", ast.position);
    
        ast.S.visit(this, ast);
        return null;
    }

    public Object visitDeclList(DeclList ast, Object o) {
        ast.D.visit(this, null);
        ast.DL.visit(this, null);
        return null;
    }

    public Object visitEmptyDeclList(EmptyDeclList ast, Object o) {
        return null;
    }

    public Object visitGlobalVarDecl(GlobalVarDecl ast, Object o) {
        declareVariable(ast.I, ast);
        if (ast.T.isVoidType()) {
            reporter.reportError(errMesg[3] + ": %", ast.I.spelling, ast.I.position);
        } else if (ast.T.isArrayType()) {
            if (((ArrayType)ast.T).T.isVoidType()) {
                reporter.reportError(errMesg[4] + ": %", ast.I.spelling, ast.I.position);
            }
    
            if (((ArrayType)ast.T).E.isEmptyExpr() && !(ast.E instanceof InitExpr)) {
                reporter.reportError(errMesg[18] + ": %", ast.I.spelling, ast.I.position);
            }
        }
    
        Object tempObject = ast.E.visit(this, ast.T);
        if (ast.T.isArrayType()) {
            if (ast.E instanceof InitExpr) {
                Integer i = (Integer)tempObject;
                ArrayType arraytype = (ArrayType)ast.T;
                if (arraytype.E.isEmptyExpr()) {
                    arraytype.E = new IntExpr(new IntLiteral(i.toString(), dummyPos), dummyPos);
                } else {
                    if (Integer.parseInt(((IntExpr)arraytype.E).IL.spelling) < i) 
                        reporter.reportError(errMesg[16] + ": %", ast.I.spelling, ast.position);
                }
            } else if (!ast.E.isEmptyExpr()) {
                reporter.reportError(errMesg[15] + ": %", ast.I.spelling, ast.position);
            }
        } else {
            ast.E = checkAss(ast.T, ast.E, errMesg[6], ast.position);
        }
    
        return null;
    }

    public Object visitLocalVarDecl(LocalVarDecl ast, Object o) {
        declareVariable(ast.I, ast);
        if (ast.T.isVoidType()) {
            reporter.reportError(errMesg[3] + ": %", ast.I.spelling, ast.I.position);
        } else if (ast.T.isArrayType()) {
            if (((ArrayType)ast.T).T.isVoidType()) 
                reporter.reportError(errMesg[4] + ": %", ast.I.spelling, ast.I.position);
    
            if (((ArrayType)ast.T).E.isEmptyExpr() && !(ast.E instanceof InitExpr)) 
                reporter.reportError(errMesg[18] + ": %", ast.I.spelling, ast.I.position);
        }
    
        Object objectTemp = ast.E.visit(this, ast.T);
        if (ast.T.isArrayType()) {
            if (ast.E instanceof InitExpr) {
                Integer i = (Integer)objectTemp;
                ArrayType arraytype = (ArrayType)ast.T;
                if (arraytype.E.isEmptyExpr()) {
                    arraytype.E = new IntExpr(new IntLiteral(i.toString(), dummyPos), dummyPos);
                } else {
                    if (Integer.parseInt(((IntExpr)arraytype.E).IL.spelling) < i) 
                        reporter.reportError(errMesg[16] + ": %", ast.I.spelling, ast.position);
                }
            } else if (!ast.E.isEmptyExpr()) {
                reporter.reportError(errMesg[15] + ": %", ast.I.spelling, ast.position);
            }
        } else {
            ast.E = checkAss(ast.T, ast.E, errMesg[6], ast.position);
        }
    
        return null;
    }

    // Parameters

    // Always returns null. Does not use the given object.

    public Object visitParaList(ParaList ast, Object o) {
        ast.P.visit(this, null);
        ast.PL.visit(this, null);
        return null;
    }

    public Object visitParaDecl(ParaDecl ast, Object o) {
        declareVariable(ast.I, ast);

        if (ast.T.isVoidType()) {
            reporter.reportError(errMesg[3] + ": %", ast.I.spelling, ast.I.position);
        } else if (ast.T.isArrayType()) {
            if (((ArrayType) ast.T).T.isVoidType())
                reporter.reportError(errMesg[4] + ": %", ast.I.spelling, ast.I.position);
        }
        return null;
    }

    public Object visitEmptyParaList(EmptyParaList ast, Object o) {
        return null;
    }

    // Arguments

    // Your visitor methods for arguments go here

    public Object visitEmptyArgList(EmptyArgList ast, Object o) {

        if (!((List)o).isEmptyParaList()) 
            reporter.reportError(errMesg[26], "", ast.position);

        return null;
    }

    public Object visitArgList(ArgList ast, Object o) {

        if (((List)o).isEmptyParaList()) {
            reporter.reportError(errMesg[25], "", ast.position);
        } else {
            ast.A.visit(this, ((ParaList)o).P);
            ast.AL.visit(this, ((ParaList)o).PL);
        }

        return null;
    }

    public Object visitArg(Arg ast, Object o) {

        boolean check = false;
        if (((Type)((ParaDecl)o).T).isArrayType()) {
            if (!((Type)ast.E.visit(this, null)).isArrayType()) {
                check = true;
            } else {
                Type t1 = ((ArrayType)((ParaDecl)o).T).T;
                Type t2 = ((ArrayType)ast.E.visit(this, null)).T;
                if (!t1.assignable(t2)) {
                    check = true;
                }
            }
        } else if (!((ParaDecl)o).T.assignable(ast.E.visit(this, null))) {
            check = true;
        }

        if (check) {
            reporter.reportError(errMesg[27] + ": %", ((ParaDecl)o).I.spelling, ast.E.position);
        }

        if (((ParaDecl)o).T.equals(StdEnvironment.floatType) && ast.E.visit(this, null).equals(StdEnvironment.intType)) {
            ast.E = checkIf(ast.E);
        }

        return null;
    }


    // Types 

    // Returns the type predefined in the standard environment. 

    public Object visitErrorType(ErrorType ast, Object o) {
        return StdEnvironment.errorType;
    }

    public Object visitBooleanType(BooleanType ast, Object o) {
        return StdEnvironment.booleanType;
    }

    public Object visitIntType(IntType ast, Object o) {
        return StdEnvironment.intType;
    }

    public Object visitFloatType(FloatType ast, Object o) {
        return StdEnvironment.floatType;
    }

    public Object visitStringType(StringType ast, Object o) {
        return StdEnvironment.stringType;
    }

    public Object visitVoidType(VoidType ast, Object o) {
        return StdEnvironment.voidType;
    }

    public Object visitArrayType(ArrayType ast, Object o) {
        return ast;
    }


    //Var

    public Object visitSimpleVar(SimpleVar ast, Object o) {
        ast.type = StdEnvironment.errorType;
        Decl decl = (Decl)ast.I.visit(this, null);
        if (decl == null) {
            reporter.reportError(errMesg[5] + ": %", ast.I.spelling, ast.position);
        } else if (decl instanceof FuncDecl) {
            reporter.reportError(errMesg[11] + ": %", ast.I.spelling, ast.I.position);
        } else {
            ast.type = decl.T;
        }

        if (ast.type.isArrayType() && ast.parent instanceof VarExpr && !(ast.parent.parent instanceof Arg)) {
            reporter.reportError(errMesg[11] + ": %", ast.I.spelling, ast.I.position);
        }

        return ast.type;
    }

    // Literals, Identifiers and Operators

    public Object visitIdent(Ident I, Object o) {
        Decl binding = idTable.retrieve(I.spelling);
        if (binding != null)
            I.decl = binding;
        return binding;
    }

    public Object visitBooleanLiteral(BooleanLiteral SL, Object o) {
        return StdEnvironment.booleanType;
    }

    public Object visitIntLiteral(IntLiteral IL, Object o) {
        return StdEnvironment.intType;
    }

    public Object visitFloatLiteral(FloatLiteral IL, Object o) {
        return StdEnvironment.floatType;
    }

    public Object visitStringLiteral(StringLiteral IL, Object o) {
        return StdEnvironment.stringType;
    }

    public Object visitOperator(Operator O, Object o) {
        return null;
    }

    // Creates a small AST to represent the "declaration" of each built-in
    // function, and enters it in the symbol table.

    private FuncDecl declareStdFunc (Type resultType, String id, List pl) {

        FuncDecl binding;

        binding = new FuncDecl(resultType, new Ident(id, dummyPos), pl, 
            new EmptyStmt(dummyPos), dummyPos);
        idTable.insert (id, binding);
        return binding;
    }

    // Creates small ASTs to represent "declarations" of all 
    // build-in functions.
    // Inserts these "declarations" into the symbol table.

    private final static Ident dummyI = new Ident("x", dummyPos);

    private void establishStdEnvironment () {

        // Define four primitive types
        // errorType is assigned to ill-typed expressions

        StdEnvironment.booleanType = new BooleanType(dummyPos);
        StdEnvironment.intType = new IntType(dummyPos);
        StdEnvironment.floatType = new FloatType(dummyPos);
        StdEnvironment.stringType = new StringType(dummyPos);
        StdEnvironment.voidType = new VoidType(dummyPos);
        StdEnvironment.errorType = new ErrorType(dummyPos);

        // enter into the declarations for built-in functions into the table

        StdEnvironment.getIntDecl = declareStdFunc( StdEnvironment.intType,
        "getInt", new EmptyParaList(dummyPos)); 
        StdEnvironment.putIntDecl = declareStdFunc( StdEnvironment.voidType,
        "putInt", new ParaList(
        new ParaDecl(StdEnvironment.intType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 
        StdEnvironment.putIntLnDecl = declareStdFunc( StdEnvironment.voidType,
        "putIntLn", new ParaList(
        new ParaDecl(StdEnvironment.intType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 
        StdEnvironment.getFloatDecl = declareStdFunc( StdEnvironment.floatType,
        "getFloat", new EmptyParaList(dummyPos)); 
        StdEnvironment.putFloatDecl = declareStdFunc( StdEnvironment.voidType,
        "putFloat", new ParaList(
        new ParaDecl(StdEnvironment.floatType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 
        StdEnvironment.putFloatLnDecl = declareStdFunc( StdEnvironment.voidType,
        "putFloatLn", new ParaList(
        new ParaDecl(StdEnvironment.floatType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 
        StdEnvironment.putBoolDecl = declareStdFunc( StdEnvironment.voidType,
        "putBool", new ParaList(
        new ParaDecl(StdEnvironment.booleanType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 
        StdEnvironment.putBoolLnDecl = declareStdFunc( StdEnvironment.voidType,
        "putBoolLn", new ParaList(
        new ParaDecl(StdEnvironment.booleanType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 

        StdEnvironment.putStringLnDecl = declareStdFunc( StdEnvironment.voidType,
        "putStringLn", new ParaList(
        new ParaDecl(StdEnvironment.stringType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 

        StdEnvironment.putStringDecl = declareStdFunc( StdEnvironment.voidType,
        "putString", new ParaList(
        new ParaDecl(StdEnvironment.stringType, dummyI, dummyPos),
        new EmptyParaList(dummyPos), dummyPos)); 

        StdEnvironment.putLnDecl = declareStdFunc( StdEnvironment.voidType,
        "putLn", new EmptyParaList(dummyPos));

    }
}
