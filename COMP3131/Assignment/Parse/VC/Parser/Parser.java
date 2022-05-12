/*
+-------------+
+ Parser.java +
+-------------+
*
* PLEASE COMPARE Recogniser.java PROVIDED IN ASSIGNMENT 2 AND Parser.java
* PROVIDED BELOW TO UNDERSTAND HOW THE FORMER IS MODIFIED TO OBTAIN THE LATTER.
*
* This parser for a subset of the VC language is intended to
*  demonstrate how to create the AST nodes, including (among others):
*  [1] a list (of statements)
*  [2] a function
*  [3] a statement (which is an expression statement),
*  [4] a unary expression
*  [5] a binary expression
*  [6] terminals (identifiers, integer literals and operators)
*
* In addition, it also demonstrates how to use the two methods start
* and finish to determine the position information for the start and
* end of a construct (known as a phrase) corresponding an AST node.
*
* NOTE THAT THE POSITION INFORMATION WILL NOT BE MARKED. HOWEVER, IT CAN BE
* USEFUL TO DEBUG YOUR IMPLEMENTATION.
*
*
* --- 27 February 2022 ---
program       -> func-decl
func-decl     -> type identifier "(" ")" compound-stmt
type          -> void
identifier    -> ID
// statements
compound-stmt -> "{" stmt* "}"
stmt          -> expr-stmt
expr-stmt     -> expr? ";"
// expressions
expr                -> additive-expr
additive-expr       -> multiplicative-expr
                    |  additive-expr "+" multiplicative-expr
                    |  additive-expr "-" multiplicative-expr
multiplicative-expr -> unary-expr
                |  multiplicative-expr "*" unary-expr
                |  multiplicative-expr "/" unary-expr
unary-expr          -> "-" unary-expr
            |  primary-expr
primary-expr        -> identifier
            |  INTLITERAL
            | "(" expr ")"
*/

package VC.Parser;

import VC.Scanner.Scanner;
import VC.Scanner.SourcePosition;
import VC.Scanner.Token;
import VC.ErrorReporter;
import VC.ASTs.*;

public class Parser {
    private Scanner scanner;
    private ErrorReporter errorReporter;
    private Token currentToken;
    private SourcePosition previousTokenPosition;
    private SourcePosition dummyPos = new SourcePosition();

    public Parser (Scanner lexer, ErrorReporter reporter) {
        scanner = lexer;
        errorReporter = reporter;

        previousTokenPosition = new SourcePosition();

        currentToken = scanner.getToken();
    }

    public class innerClass {
        Type tAST;
        Ident iAST;

        public innerClass(Type tAST, Ident iAST) {
            this.tAST = tAST;
            this.iAST = iAST;
        }
    }

    // match checks to see f the current token matches tokenExpected.
    // If so, fetches the next token.
    // If not, reports a syntactic error.

    void match(int tokenExpected) throws SyntaxError {
        if (currentToken.kind == tokenExpected) {
            previousTokenPosition = currentToken.position;
            currentToken = scanner.getToken();
        } else {
            syntacticError("\"%\" expected here", Token.spell(tokenExpected));
        }
    }

    void accept() {
        previousTokenPosition = currentToken.position;
        currentToken = scanner.getToken();
    }

    void syntacticError(String messageTemplate, String tokenQuoted) throws SyntaxError {
        SourcePosition pos = currentToken.position;
        errorReporter.reportError(messageTemplate, tokenQuoted, pos);
        throw(new SyntaxError());
    }

    // start records the position of the start of a phrase.
    // This is defined to be the position of the first
    // character of the first token of the phrase.

    void start(SourcePosition var1) {
        var1.lineStart = currentToken.position.lineStart;
        var1.charStart = currentToken.position.charStart;
    }

    void finish(SourcePosition var1) {
        var1.lineFinish = previousTokenPosition.lineFinish;
        var1.charFinish = previousTokenPosition.charFinish;
    }

    void copyStart(SourcePosition var1, SourcePosition var2) {
        var2.lineStart = var1.lineStart;
        var2.charStart = var1.charStart;
    }

    Type copyType(Type tAST) {
        SourcePosition tPos = tAST.position;
        if (tAST instanceof IntType) {
            return new IntType(tPos);
        } else if (tAST instanceof FloatType) {
            return new FloatType(tPos);
        } else if (tAST instanceof BooleanType) {
            return new BooleanType(tPos);
        } else {
            return new VoidType(tPos);
        }
    }

    // ========================== PROGRAMS ========================

    public Program parseProgram() {

        Program programAST = null;

        SourcePosition programPos = new SourcePosition();
        start(programPos);

        try {
            List dlAST = parseFuncDeclList();
            finish(programPos);
            programAST = new Program(dlAST, programPos);
            if (currentToken.kind != Token.EOF) {
                syntacticError("\"%\" unknown type", currentToken.spelling);
            }
        }
        catch (SyntaxError s) { return null; }
        return programAST;
    }

    // ========================== DECLARATIONS ========================

    List parseFuncDeclList() throws SyntaxError {
        Decl dAST = null;
        List d2AST = null;
        List dlAST = null;
        SourcePosition funPos = new SourcePosition();
        start(funPos);
        if (currentToken.kind == Token.VOID || currentToken.kind == Token.BOOLEAN ||
            currentToken.kind == Token.INT || currentToken.kind == Token.FLOAT) {
            Type tAST = parseType();
            Ident idAST = parseIdent();
            if (currentToken.kind == Token.LPAREN) {
                dAST = parseFuncDeclStart(tAST, idAST);
            } else {
                d2AST = parseVarDeclStart(tAST, idAST, true);
            }
        }

        if (currentToken.kind != Token.VOID && currentToken.kind != Token.BOOLEAN &&
            currentToken.kind != Token.INT && currentToken.kind != Token.FLOAT) {
            dlAST = new EmptyDeclList(dummyPos);
        } else {
            dlAST = parseFuncDeclList();
        }

        if (dAST != null) {
            finish(funPos);
            d2AST = new DeclList(dAST, (List)dlAST, funPos);
        } else if (d2AST != null) {
            DeclList d3AST = (DeclList)d2AST;
            while (!(d3AST.DL instanceof EmptyDeclList))
                d3AST = (DeclList)d3AST.DL;

            if (!(dlAST instanceof EmptyDeclList))
                d3AST.DL = (DeclList)dlAST;
        } else {
            d2AST = dlAST;
        }

        return (List)d2AST;
    }

    Decl parseFuncDeclStart(Type tAST, Ident idAST) throws SyntaxError {
        SourcePosition fdPos = tAST.position;
        List lAST = parseParaList();
        Stmt sAST = parseCompoundStmt();
        finish(fdPos);
        return new FuncDecl(tAST, idAST, lAST, sAST, fdPos);
    }



    List parseVarDecl() throws SyntaxError {
        List vdAST = null;
        Type tAST = parseType();
        vdAST = parseInitDeclaratorList(tAST, false);
        match(Token.SEMICOLON);
        return vdAST;
    }

    List parseVarDeclStart(Type tAST, Ident idAST, boolean isArray) throws SyntaxError {
        List lAST = null;
        Decl dAST = null;
        SourcePosition vdsPos = new SourcePosition();
        copyStart(tAST.position, vdsPos);
        Expr East;
        if (currentToken.kind == Token.LBRACKET) {
            accept();
            if (currentToken.kind == Token.INTLITERAL) {
                East = parseExpr();
            } else {
                East = new EmptyExpr(dummyPos);
            }

            match(Token.RBRACKET);
            finish(vdsPos);
            tAST = new ArrayType(tAST, (Expr)East, vdsPos);
        }

        if (currentToken.kind == Token.EQ) {
            accept();
            East = parseInitialiser();
        } else {
            East = new EmptyExpr(dummyPos);
        }

        SourcePosition temp1Pos = new SourcePosition();
        copyStart(idAST.position, temp1Pos);
        finish(temp1Pos);
        if (isArray) {
            dAST = new GlobalVarDecl(tAST, idAST, (Expr)East, temp1Pos);
        } else {
            dAST = new LocalVarDecl(tAST, idAST, (Expr)East, temp1Pos);
        }

        SourcePosition temp2Pos = new SourcePosition();
        copyStart(idAST.position, temp2Pos);
        DeclList dllAST;
        if (currentToken.kind == Token.COMMA) {
            accept();
            if (tAST instanceof ArrayType) {
                tAST = ((ArrayType)tAST).T;
            }

            lAST = parseInitDeclaratorList(tAST, isArray);
            finish(temp2Pos);
            dllAST = new DeclList((Decl)dAST, lAST, temp2Pos);
        } else {
            finish(temp2Pos);
            dllAST = new DeclList((Decl)dAST, new EmptyDeclList(dummyPos), temp2Pos);
        }

        match(Token.SEMICOLON);
        return dllAST;
    }

    List parseInitDeclaratorList(Type tAST, boolean isArray) throws SyntaxError {
        List idlAST = null;
        SourcePosition idlPos = new SourcePosition();
        start(idlPos);
        tAST = copyType(tAST);
        Decl dAST = parseInitDeclarator(tAST, isArray);
        DeclList dlAST;
        if (currentToken.kind == Token.COMMA) {
            accept();
            idlAST = parseInitDeclaratorList(tAST, isArray);
            finish(idlPos);
            dlAST = new DeclList(dAST, idlAST, idlPos);
        } else {
            finish(idlPos);
            dlAST = new DeclList(dAST, new EmptyDeclList(dummyPos), idlPos);
        }

        return dlAST;
    }

    Decl parseInitDeclarator(Type tAST, boolean isArray) throws SyntaxError {
        Decl idAST = null;
        SourcePosition idPos = new SourcePosition();
        start(idPos);
        VC.Parser.Parser.innerClass temp = parseDeclarator(tAST);
        Expr eAST = null;
        if (currentToken.kind == Token.EQ) {
            accept();
            eAST = parseInitialiser();
        } else {
            eAST = new EmptyExpr(dummyPos);
        }

        finish(idPos);
        if (isArray) {
            idAST = new GlobalVarDecl(temp.tAST, temp.iAST, eAST, idPos);
        } else {
            idAST = new LocalVarDecl(temp.tAST, temp.iAST, eAST, idPos);
        }

        return (Decl)idAST;
    }

    innerClass parseDeclarator(Type tAST) throws SyntaxError {
        Expr eAST = null;
        SourcePosition dPos = new SourcePosition();
        copyStart(tAST.position, dPos);
        Ident iAST = parseIdent();
        if (currentToken.kind == Token.LBRACKET) {
            accept();
            if (currentToken.kind == Token.INTLITERAL) {
                SourcePosition tempPos = new SourcePosition();
                start(tempPos);
                IntLiteral intl = parseIntLiteral();
                finish(tempPos);
                eAST = new IntExpr(intl, tempPos);
            } else {
                eAST = new EmptyExpr(dummyPos);
            }

            match(Token.RBRACKET);
            finish(dPos);
            tAST = new ArrayType(tAST, eAST, dPos);
        }

        return new innerClass(tAST, iAST);
    }

    List parseInitExpr() throws SyntaxError {
        SourcePosition iePos = new SourcePosition();
        start(iePos);
        List lAST = null;
        Expr eAST = parseExpr();
        ExprList elAST;
        if (currentToken.kind == Token.SEMICOLON) {
            accept();
            lAST = parseInitExpr();
            finish(iePos);
            elAST = new ExprList(eAST, lAST, iePos);
        } else {
            finish(iePos);
            elAST = new ExprList(eAST, new EmptyExprList(dummyPos), iePos);
        }

        return elAST;
    }

    Expr parseInitialiser() throws SyntaxError {
        Expr iiAST = null;
        SourcePosition iiPos = new SourcePosition();
        start(iiPos);
        if (currentToken.kind == Token.LCURLY) {
            accept();
            List lAST = parseInitExpr();
            match(Token.RCURLY);
            finish(iiPos);
            iiAST = new InitExpr(lAST, iiPos);
        } else {
            iiAST = parseExpr();
        }

        return iiAST;
    }

    //  ======================== TYPES ==========================

    Type parseType() throws SyntaxError {
        Type typeAST = null;
        SourcePosition typePos = new SourcePosition();
        start(typePos);
        if (currentToken.kind == Token.VOID) {
            accept();
            finish(typePos);
            typeAST = new VoidType(typePos);
        } else if (currentToken.kind == Token.BOOLEAN) {
            accept();
            finish(typePos);
            typeAST = new BooleanType(typePos);
        } else if (currentToken.kind == Token.INT) {
            accept();
            finish(typePos);
            typeAST = new IntType(typePos);
        } else if (currentToken.kind == Token.FLOAT) {
            accept();
            finish(typePos);
            typeAST = new FloatType(typePos);
        } else {
            syntacticError("\"%\" type Wrong", currentToken.spelling);
        }

        return typeAST;
    }

    // ======================= STATEMENTS ==============================

    Stmt parseCompoundStmt() throws SyntaxError {
        Stmt cAST = null;
        SourcePosition stmtPos = new SourcePosition();
        start(stmtPos);

        match(Token.LCURLY);
        List l1AST = parseDeclStmtList();
        List l2AST = parseStmtList();
        match(Token.RCURLY);
        finish(stmtPos);

        /* In the subset of the VC grammar, no variable declarations are
        * allowed. Therefore, a block is empty iff it has no statements.
        */
        if (l1AST instanceof EmptyDeclList && l2AST instanceof EmptyStmtList) {
            cAST = new EmptyCompStmt(stmtPos);
        } else {
            finish(stmtPos);
            cAST = new CompoundStmt(l1AST, l2AST, stmtPos);
        }

        return cAST;
    }

    List parseDeclStmtList() throws SyntaxError {
        List dslAST = null;
        SourcePosition dslPos = new SourcePosition();
        start(dslPos);
        if (currentToken.kind == Token.INT || currentToken.kind == Token.FLOAT ||
            currentToken.kind == Token.BOOLEAN || currentToken.kind == Token.VOID) {
            dslAST = parseVarDecl();
        }

        while(currentToken.kind == Token.INT || currentToken.kind == Token.FLOAT ||
            currentToken.kind == Token.BOOLEAN || currentToken.kind == Token.VOID) {
            List lAST = parseVarDecl();

            DeclList dlAST = (DeclList)dslAST;
            while (!(dlAST.DL instanceof EmptyDeclList))
                dlAST = (DeclList)dlAST.DL;

            dlAST.DL = (DeclList)lAST;
        }

        if (dslAST == null) {
            dslAST = new EmptyDeclList(dummyPos);
        }

        return dslAST;
    }

    List parseStmtList() throws SyntaxError {
        List slAST = null;

        SourcePosition stmtPos = new SourcePosition();
        start(stmtPos);

        if (currentToken.kind != Token.RCURLY) {
            Stmt sAST = parseStmt();
            {
                if (currentToken.kind != Token.RCURLY) {
                    slAST = parseStmtList();
                    finish(stmtPos);
                    slAST = new StmtList(sAST, slAST, stmtPos);
                } else {
                    finish(stmtPos);
                    slAST = new StmtList(sAST, new EmptyStmtList(dummyPos), stmtPos);
                }
            }
        }
        else
        slAST = new EmptyStmtList(dummyPos);

        return slAST;
    }

    Stmt parseStmt() throws SyntaxError {
        Stmt sAST = null;

        switch (currentToken.kind) {
            case Token.IF:
                sAST = parseIfStmt();
                break;

            case Token.FOR:
                sAST = parseForStmt();
                break;

            case Token.WHILE:
                sAST = parseWhileStmt();
                break;

            case Token.BREAK:
                sAST = parseBreakStmt();
                break;

            case Token.CONTINUE:
                sAST = parseContinueStmt();
                break;

            case Token.RETURN:
                sAST = parseReturnStmt();
                break;

            case Token.LCURLY:
                sAST = parseCompoundStmt();
                break;

            default:
                sAST = parseExprStmt();
                break;
        }

        return sAST;
    }

    Stmt parseIfStmt() throws SyntaxError {
        SourcePosition ifPos = new SourcePosition();
        start(ifPos);

        match(Token.IF);
        match(Token.LPAREN);
        Expr eAST = parseExpr();
        match(Token.RPAREN);
        Stmt s1AST = parseStmt();
        if (currentToken.kind == Token.ELSE) {
            accept();
            Stmt s2AST = parseStmt();
            finish(ifPos);
            return new IfStmt(eAST, s1AST, s2AST, ifPos);
        } else {
            finish(ifPos);
            return new IfStmt(eAST, s1AST, ifPos);
        }
    }


    Stmt parseForStmt() throws SyntaxError {
        SourcePosition fsPos = new SourcePosition();
        start(fsPos);

        match(Token.FOR);
        match(Token.LPAREN);
        Expr e1AST = null;
        Expr e2AST = null;
        Expr e3AST = null;

        if (currentToken.kind != Token.SEMICOLON) {
            e1AST = parseExpr();
        } else {
            e1AST = new EmptyExpr(fsPos);
        }

        match(Token.SEMICOLON);
        if (currentToken.kind != Token.SEMICOLON) {
            e2AST = parseExpr();
        } else {
            e2AST = new EmptyExpr(fsPos);
        }

        match(Token.SEMICOLON);
        if (currentToken.kind != Token.RPAREN) {
            e3AST = parseExpr();
        } else {
            e3AST = new EmptyExpr(fsPos);
        }
        match(Token.RPAREN);

        Stmt sAST = parseStmt();
        finish(fsPos);
        return new ForStmt(e1AST, e2AST, e3AST, sAST, fsPos);
    }

    Stmt parseWhileStmt() throws SyntaxError {
        SourcePosition wsPos = new SourcePosition();
        start(wsPos);

        match(Token.WHILE);
        match(Token.LPAREN);
        Expr eAST = parseExpr();
        match(Token.RPAREN);
        Stmt sAST = parseStmt();
        finish(wsPos);
        return new WhileStmt(eAST, sAST, wsPos);
    }

    Stmt parseBreakStmt() throws SyntaxError {
        SourcePosition bsPos = new SourcePosition();
        start(bsPos);

        match(Token.BREAK);
        match(Token.SEMICOLON);
        finish(bsPos);
        return new BreakStmt(bsPos);
    }

    Stmt parseContinueStmt() throws SyntaxError {
        SourcePosition csPos = new SourcePosition();
        start(csPos);

        match(Token.CONTINUE);
        match(Token.SEMICOLON);
        finish(csPos);
        return new ContinueStmt(csPos);
    }

    Stmt parseReturnStmt() throws SyntaxError {
        SourcePosition rsPos = new SourcePosition();
        start(rsPos);

        match(Token.RETURN);
        Expr eAST = null;
        if (currentToken.kind == Token.SEMICOLON) {
            accept();
            finish(rsPos);
            eAST = new EmptyExpr(rsPos);
        } else {
            eAST = parseExpr();
            finish(rsPos);
        }
        return new ReturnStmt(eAST, rsPos);
    }

    Stmt parseExprStmt() throws SyntaxError {
        ExprStmt sAST = null;
        SourcePosition stmtPos = new SourcePosition();
        start(stmtPos);
        if (currentToken.kind != Token.ID && currentToken.kind != Token.NOT &&
            currentToken.kind != Token.PLUS && currentToken.kind != Token.MINUS &&
            currentToken.kind != Token.INTLITERAL && currentToken.kind != Token.FLOATLITERAL &&
            currentToken.kind != Token.BOOLEANLITERAL && currentToken.kind != Token.STRINGLITERAL &&
            currentToken.kind != Token.LPAREN) {
            match(Token.SEMICOLON);
            finish(stmtPos);
            sAST = new ExprStmt(new EmptyExpr(dummyPos), stmtPos);
        } else {
            Expr eAST = parseExpr();
            match(Token.SEMICOLON);
            finish(stmtPos);
            sAST = new ExprStmt(eAST, stmtPos);
        }

        return sAST;
    }

    // ======================= PARAMETERS =======================

    List parseParaList() throws SyntaxError {
        List formalsAST = null;

        SourcePosition formalsPos = new SourcePosition();
        start(formalsPos);

        match(Token.LPAREN);
        if (currentToken.kind == Token.RPAREN) {
            accept();
            finish(formalsPos);
            formalsAST = new EmptyParaList(formalsPos);
        } else
            formalsAST = parseProperParaList();
        return formalsAST;
    }

    List parseProperParaList() throws SyntaxError {
        List pplAST = null;
        SourcePosition pplPos = new SourcePosition();
        start(pplPos);

        ParaDecl dAST = parseParaDecl();
        List dlAST = null;
        if (currentToken.kind == Token.COMMA) {
            accept();
            dlAST = parseProperParaList();
            finish(pplPos);
            pplAST = new ParaList(dAST, pplAST, pplPos);
        } else {
            finish(pplPos);
            pplAST = new DeclList(dAST, new EmptyDeclList(pplPos), pplPos);
        }
        return pplAST;
    }

    ParaDecl parseParaDecl() throws SyntaxError {
        ParaDecl pdAST = null;
        Type tAST = parseType();
        SourcePosition pdPos = new SourcePosition();
        start(pdPos);
        innerClass arrayType = parseDeclarator(tAST);
        finish(pdPos);
        pdAST = new ParaDecl(arrayType.tAST, arrayType.iAST, pdPos);
        return pdAST;
    }

    List parseArgList() throws SyntaxError {
        List argAST = null;

        SourcePosition argPos = new SourcePosition();
        start(argPos);

        match(Token.LPAREN);
        if (currentToken.kind == Token.RPAREN) {
            accept();
            finish(argPos);
            argAST = new EmptyArgList(argPos);
        } else {
            argAST = parseProperArgList();
        }
        return argAST;
    }

    List parseProperArgList() throws SyntaxError {
        List paAST = null;
        SourcePosition palPos = new SourcePosition();
        start(palPos);
        Arg arg = parseArg();
        ArgList dlAST;
        if (currentToken.kind == Token.COMMA) {
            accept();
            paAST = parseProperArgList();
            finish(palPos);
            dlAST = new ArgList(arg, paAST, palPos);
        } else {
            finish(palPos);
            dlAST = new ArgList(arg, new EmptyArgList(palPos), palPos);
        }

        return dlAST;
    }

    Arg parseArg() throws SyntaxError {
        SourcePosition aPos = new SourcePosition();
        start(aPos);
        Expr a = parseExpr();
        finish(aPos);
        return new Arg(a, aPos);
    }

    // ======================= EXPRESSIONS ======================

    Expr parseExpr() throws SyntaxError {
        Expr exprAST = null;
        exprAST = parseAssignmentExpr();
        return exprAST;
    }

    Expr parseAssignmentExpr () throws SyntaxError {
        Expr exprAST = null;

        SourcePosition asStartPos = new SourcePosition();
        start(asStartPos);

        exprAST = parseCondOrExpr();
        while (currentToken.kind == Token.EQ) {

            Operator opAST = acceptOperator();
            Expr e2AST = parseAdditiveExpr();

            SourcePosition asPos = new SourcePosition();
            copyStart(asStartPos, asPos);
            finish(asPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, asPos);
        }
        return exprAST;
    }

    Expr parseCondOrExpr() throws SyntaxError {
        Expr exprAST = null;

        SourcePosition coStartPos = new SourcePosition();
        start(coStartPos);

        exprAST = parseCondAndExpr();
        while (currentToken.kind == Token.OROR) {

            Operator opAST = acceptOperator();
            Expr e2AST = parseAdditiveExpr();

            SourcePosition coPos = new SourcePosition();
            copyStart(coStartPos, coPos);
            finish(coPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, coPos);
        }
        return exprAST;
    }

    Expr parseCondAndExpr() throws SyntaxError {
        Expr exprAST = null;

        SourcePosition caStartPos = new SourcePosition();
        start(caStartPos);

        exprAST = parseEqualityExpr();
        while (currentToken.kind == Token.ANDAND) {

            Operator opAST = acceptOperator();
            Expr e2AST = parseAdditiveExpr();

            SourcePosition caPos = new SourcePosition();
            copyStart(caStartPos, caPos);
            finish(caPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, caPos);
        }
        return exprAST;
    }

    Expr parseEqualityExpr() throws SyntaxError {
        Expr exprAST = null;

        SourcePosition eqStartPos = new SourcePosition();
        start(eqStartPos);

        exprAST = parseRelExpr();
        while (currentToken.kind == Token.NOTEQ || currentToken.kind == Token.EQEQ) {

            Operator opAST = acceptOperator();
            Expr e2AST = parseAdditiveExpr();

            SourcePosition eqPos = new SourcePosition();
            copyStart(eqStartPos, eqPos);
            finish(eqPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, eqPos);
        }
        return exprAST;
    }

    Expr parseRelExpr() throws SyntaxError {
        Expr exprAST = null;

        SourcePosition relStartPos = new SourcePosition();
        start(relStartPos);

        exprAST = parseAdditiveExpr();
        while (currentToken.kind == Token.LTEQ || currentToken.kind == Token.LT ||
               currentToken.kind == Token.GTEQ || currentToken.kind == Token.GT) {

            Operator opAST = acceptOperator();
            Expr e2AST = parseAdditiveExpr();

            SourcePosition relPos = new SourcePosition();
            copyStart(relStartPos, relPos);
            finish(relPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, relPos);
        }
        return exprAST;
    }

    Expr parseAdditiveExpr() throws SyntaxError {
        Expr exprAST = null;

        SourcePosition addStartPos = new SourcePosition();
        start(addStartPos);

        exprAST = parseMultiplicativeExpr();
        while (currentToken.kind == Token.PLUS || currentToken.kind == Token.MINUS) {
            Operator opAST = acceptOperator();
            Expr e2AST = parseMultiplicativeExpr();

            SourcePosition addPos = new SourcePosition();
            copyStart(addStartPos, addPos);
            finish(addPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, addPos);
        }
        return exprAST;
    }

    Expr parseMultiplicativeExpr() throws SyntaxError {

        Expr exprAST = null;

        SourcePosition multStartPos = new SourcePosition();
        start(multStartPos);

        exprAST = parseUnaryExpr();
        while (currentToken.kind == Token.MULT || currentToken.kind == Token.DIV) {
            Operator opAST = acceptOperator();
            Expr e2AST = parseUnaryExpr();
            SourcePosition multPos = new SourcePosition();
            copyStart(multStartPos, multPos);
            finish(multPos);
            exprAST = new BinaryExpr(exprAST, opAST, e2AST, multPos);
        }
        return exprAST;
    }

    Expr parseUnaryExpr() throws SyntaxError {

        Expr exprAST = null;

        SourcePosition unaryPos = new SourcePosition();
        start(unaryPos);

        switch (currentToken.kind) {
            case Token.MINUS :case Token.PLUS: case Token.NOT:
                Operator opAST = acceptOperator();
                Expr e2AST = parseUnaryExpr();
                finish(unaryPos);
                exprAST = new UnaryExpr(opAST, e2AST, unaryPos);
                break;

            default:
                exprAST = parsePrimaryExpr();
                break;

        }
        return exprAST;
    }

    Expr parsePrimaryExpr() throws SyntaxError {
        Expr exprAST = null;
        SourcePosition primPos = new SourcePosition();
        start(primPos);
        switch(currentToken.kind) {
            case Token.ID:
                Ident iAST = parseIdent();
                if (currentToken.kind == Token.LPAREN) {
                    List e2AST = parseArgList();
                    finish(primPos);
                    exprAST = new CallExpr(iAST, e2AST, primPos);
                } else {
                    SimpleVar sAST;
                    if (currentToken.kind == Token.LBRACKET) {
                        finish(primPos);
                        sAST = new SimpleVar(iAST, primPos);
                        accept();
                        Expr e3AST = parseExpr();
                        finish(primPos);
                        exprAST = new ArrayExpr(sAST, e3AST, primPos);
                        match(Token.RBRACKET);
                    } else {
                        finish(primPos);
                        sAST = new SimpleVar(iAST, primPos);
                        exprAST = new VarExpr(sAST, primPos);
                    }
                }
                break;

            case Token.LPAREN:
                accept();
                exprAST = parseExpr();
                match(Token.RPAREN);
                break;

            case Token.INTLITERAL:
                IntLiteral ilAST = parseIntLiteral();
                finish(primPos);
                exprAST = new IntExpr(ilAST, primPos);
                break;

            case Token.FLOATLITERAL:
                FloatLiteral flAST = parseFloatLiteral();
                finish(primPos);
                exprAST = new FloatExpr(flAST, primPos);
                break;

            case Token.BOOLEANLITERAL:
                BooleanLiteral blAST = parseBooleanLiteral();
                finish(primPos);
                exprAST = new BooleanExpr(blAST, primPos);
                break;

            case Token.STRINGLITERAL:
                StringLiteral slAST = parseStringLiteral();
                finish(primPos);
                exprAST = new StringExpr(slAST, primPos);
                break;

            default:
                syntacticError("illegal primary expression", currentToken.spelling);

        }
        return (Expr)exprAST;
    }

    // ========================== ID, OPERATOR and LITERALS ========================

    Ident parseIdent() throws SyntaxError {

        Ident I = null;

        if (currentToken.kind == Token.ID) {
            previousTokenPosition = currentToken.position;
            String spelling = currentToken.spelling;
            I = new Ident(spelling, previousTokenPosition);
            currentToken = scanner.getToken();
        } else
            syntacticError("identifier expected here", "");
        return I;
    }

    // acceptOperator parses an operator, and constructs a leaf AST for it

    Operator acceptOperator() throws SyntaxError {
        Operator O = null;

        previousTokenPosition = currentToken.position;
        String spelling = currentToken.spelling;
        O = new Operator(spelling, previousTokenPosition);
        currentToken = scanner.getToken();
        return O;
    }

    IntLiteral parseIntLiteral() throws SyntaxError {
        IntLiteral IL = null;

        if (currentToken.kind == Token.INTLITERAL) {
            String spelling = currentToken.spelling;
            accept();
            IL = new IntLiteral(spelling, previousTokenPosition);
        } else
            syntacticError("integer literal expected here", "");
        return IL;
    }

    FloatLiteral parseFloatLiteral() throws SyntaxError {
        FloatLiteral FL = null;

        if (currentToken.kind == Token.FLOATLITERAL) {
            String spelling = currentToken.spelling;
            accept();
            FL = new FloatLiteral(spelling, previousTokenPosition);
        } else
            syntacticError("float literal expected here", "");
        return FL;
    }

    BooleanLiteral parseBooleanLiteral() throws SyntaxError {
        BooleanLiteral BL = null;

        if (currentToken.kind == Token.BOOLEANLITERAL) {
            String spelling = currentToken.spelling;
            accept();
            BL = new BooleanLiteral(spelling, previousTokenPosition);
        } else
            syntacticError("boolean literal expected here", "");
        return BL;
    }

    StringLiteral parseStringLiteral() throws SyntaxError {
        StringLiteral SL = null;
        if (currentToken.kind == Token.STRINGLITERAL) {
            previousTokenPosition = currentToken.position;
            String spelling = currentToken.spelling;
            SL = new StringLiteral(spelling, previousTokenPosition);
            currentToken = scanner.getToken();
        } else {
            syntacticError("string literal expected here", "");
        }

        return SL;
    }
}