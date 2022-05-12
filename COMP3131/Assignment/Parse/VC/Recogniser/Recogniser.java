/***
 *|*
*+* Recogniser.java            
*|*
***/

/* At this stage, this parser accepts a subset of VC defined	by
* the following grammar. 
*
* You need to modify the supplied parsing methods (if necessary) and 
* add the missing ones to obtain a parser for the VC language.
*
* 19-Feb-2022

program       -> func-decl

// declaration

func-decl     -> void identifier "(" ")" compound-stmt

identifier    -> ID

// statements 
compound-stmt -> "{" stmt* "}" 
stmt          -> continue-stmt
            |  expr-stmt
continue-stmt -> continue ";"
expr-stmt     -> expr? ";"

// expressions 
expr                -> assignment-expr
assignment-expr     -> additive-expr
additive-expr       -> multiplicative-expr
                    |  additive-expr "+" multiplicative-expr
multiplicative-expr -> unary-expr
                |  multiplicative-expr "*" unary-expr
unary-expr          -> "-" unary-expr
            |  primary-expr

primary-expr        -> identifier
            |  INTLITERAL
            | "(" expr ")"
*/

package VC.Recogniser;


import javax.sql.rowset.spi.SyncFactoryException;

import VC.ErrorReporter;
import VC.Scanner.Scanner;
import VC.Scanner.SourcePosition;
import VC.Scanner.Token;

public class Recogniser {

    private Scanner scanner;
    private ErrorReporter errorReporter;
    private Token currentToken;

    public Recogniser (Scanner lexer, ErrorReporter reporter) {
        scanner = lexer;
        errorReporter = reporter;

        currentToken = scanner.getToken();
    }

    // match checks to see f the current token matches tokenExpected.
    // If so, fetches the next token.
    // If not, reports a syntactic error.

    void match(int tokenExpected) throws SyntaxError {
        if (currentToken.kind == tokenExpected) {
            currentToken = scanner.getToken();
        } else {
            syntacticError("\"%\" expected here", Token.spell(tokenExpected));
        }
    }

    // accepts the current token and fetches the next
    void accept() {
        currentToken = scanner.getToken();
    }

    void syntacticError(String messageTemplate, String tokenQuoted) throws SyntaxError {
        SourcePosition pos = currentToken.position;
        errorReporter.reportError(messageTemplate, tokenQuoted, pos);
        throw(new SyntaxError());
    }


    // ========================== PROGRAMS ========================

    public void parseProgram() {

        try {
            while (currentToken.kind != Token.EOF) {
                parseCheckFunOrVar();
            }
            if (currentToken.kind != Token.EOF) {
                syntacticError("\"%\" wrong result type for a function", currentToken.spelling);
            }
        }
        catch (SyntaxError s) {  }
    }

    // ========================== DECLARATIONS ========================

    void parseCheckFunOrVar() throws SyntaxError {
        parseType();
        parseInitDeclaratorList();
        if (currentToken.kind == Token.LPAREN) {
            parseParaList();
            parseCompoundStmt();
        } else {
            match(Token.SEMICOLON);
        }
    }

    void parseFuncDecl() throws SyntaxError {

        parseType();
        parseIdent();
        parseParaList();
        parseCompoundStmt();
    }

    void parseVarDecl() throws SyntaxError {

        parseType();
        parseInitDeclaratorList();
        match(Token.SEMICOLON);
    }

    void parseInitDeclaratorList() throws SyntaxError {

        parseInitDeclarator();
        while (currentToken.kind == Token.COMMA) { 
            accept();
            parseInitDeclarator();
        }
    }

    void parseInitDeclarator() throws SyntaxError {
        
        parseDeclarator();
        if (currentToken.kind == Token.EQ) {
            accept();
            parseInitialiser();
        }
    }

    void parseDeclarator() throws SyntaxError {

        parseIdent();
        if (currentToken.kind == Token.LBRACKET) {
            accept();
            if (currentToken.kind != Token.RBRACKET) {
                parseIntLiteral();
            }
            match(Token.RBRACKET);
        }
    }

    void parseInitialiser() throws SyntaxError {

        if (currentToken.kind == Token.LCURLY) {
            accept();
            parseExpr();
            while (currentToken.kind == Token.COMMA) {
                accept();
                parseExpr();
            }
            match(Token.RCURLY);
        } else 
            parseExpr();
    }


    // ========================== PRIMIYIVE TYES ========================


    void parseType() throws SyntaxError {
        
        if (currentToken.kind == Token.VOID ||
            currentToken.kind == Token.BOOLEAN ||
            currentToken.kind == Token.INT || 
            currentToken.kind == Token.FLOAT) {
            accept();
        } else {
            syntacticError("\"%\" wrong result type for a function", currentToken.spelling);
        }
    }

    
    // ======================= STATEMENTS ==============================


    void parseCompoundStmt() throws SyntaxError {

        match(Token.LCURLY);
        while (currentToken.kind == Token.VOID || 
               currentToken.kind == Token.BOOLEAN ||
               currentToken.kind == Token.INT || 
               currentToken.kind == Token.FLOAT) {
            parseVarDecl();
        }

        while (currentToken.kind == Token.BREAK || 
               currentToken.kind == Token.CONTINUE ||
               currentToken.kind == Token.FOR || 
               currentToken.kind == Token.IF ||
               currentToken.kind == Token.RETURN ||
               currentToken.kind == Token.WHILE ||
               currentToken.kind == Token.BOOLEANLITERAL ||
               currentToken.kind == Token.ID ||
               currentToken.kind == Token.INTLITERAL ||
               currentToken.kind == Token.MINUS || 
               currentToken.kind == Token.LPAREN 
               || currentToken.kind == Token.PLUS
               || currentToken.kind == Token.NOT
               || currentToken.kind == Token.STRINGLITERAL
               || currentToken.kind == Token.FLOATLITERAL) {
            parseStmt();
        }
        
        match(Token.RCURLY);
    }

    // Here, a new nontermial has been introduced to define { stmt } *
    void parseStmtList() throws SyntaxError {

        while (currentToken.kind != Token.RCURLY) 
            parseStmt();
    }

    void parseStmt() throws SyntaxError {

        switch (currentToken.kind) {

            case Token.IF:
                parseIfStmt();
                break;

            case Token.FOR:
                parseForStmt();
                break;

            case Token.WHILE:
                parseWhileStmt();
                break;

            case Token.BREAK:
                parseBreakStmt();
                break;

            case Token.CONTINUE:
                parseContinueStmt();
                break;

            case Token.RETURN:
                parseReturnStmt();
                break;

            default:
                parseExprStmt();
                break;

        }
    }

    void parseIfStmt() throws SyntaxError {

        match(Token.IF);
        match(Token.LPAREN);
        parseExpr();
        match(Token.RPAREN);

        if (currentToken.kind == Token.LCURLY)
            parseCompoundStmt();
        else 
            parseStmt();

        if (currentToken.kind == Token.ELSE) {
            accept();
            if (currentToken.kind == Token.LCURLY)
                parseCompoundStmt();
            else 
                parseStmt();
        }
    }

    void parseForStmt() throws SyntaxError {

        match(Token.FOR);
        match(Token.LPAREN);
        parseExprStmt();
        parseExprStmt();
        if (currentToken.kind == Token.ID
        || currentToken.kind == Token.PLUS
        || currentToken.kind == Token.MINUS
        || currentToken.kind == Token.NOT
        || currentToken.kind == Token.LPAREN
        || currentToken.kind == Token.BOOLEANLITERAL
        || currentToken.kind == Token.STRINGLITERAL
        || currentToken.kind == Token.INTLITERAL
        || currentToken.kind == Token.FLOATLITERAL) {
            parseExpr();
        }
        match(Token.RPAREN);
        parseCompoundStmt();
    }

    void parseWhileStmt() throws SyntaxError {

        match(Token.WHILE);
        match(Token.LPAREN);
        parseExpr();
        match(Token.RPAREN);
        parseCompoundStmt();
    }

    void parseBreakStmt() throws SyntaxError {
        match(Token.BREAK);
        match(Token.SEMICOLON);
    }

    void parseContinueStmt() throws SyntaxError {

        match(Token.CONTINUE);
        match(Token.SEMICOLON);

    }

    void parseReturnStmt() throws SyntaxError {

        match(Token.RETURN);
        parseExprStmt();
    }

    void parseExprStmt() throws SyntaxError {

        if (currentToken.kind == Token.ID
        || currentToken.kind == Token.PLUS
        || currentToken.kind == Token.MINUS
        || currentToken.kind == Token.NOT
        || currentToken.kind == Token.LPAREN
        || currentToken.kind == Token.BOOLEANLITERAL
        || currentToken.kind == Token.STRINGLITERAL
        || currentToken.kind == Token.INTLITERAL
        || currentToken.kind == Token.FLOATLITERAL) {
            parseExpr();
            match(Token.SEMICOLON);
        } else {
            match(Token.SEMICOLON);
        }

    }


    // ======================= IDENTIFIERS ======================

    // Call parseIdent rather than match(Token.ID). 
    // In Assignment 3, an Identifier node will be constructed in here.


    void parseIdent() throws SyntaxError {

        if (currentToken.kind == Token.ID) {
            accept();
        } else 
            syntacticError("identifier expected here", "");
    }

    // ======================= OPERATORS ======================

    // Call acceptOperator rather than accept(). 
    // In Assignment 3, an Operator Node will be constructed in here.

    void acceptOperator() throws SyntaxError {

        currentToken = scanner.getToken();
    }


    // ======================= EXPRESSIONS ======================

    void parseExpr() throws SyntaxError {

        parseAssignExpr();
    }

    void parseAssignExpr() throws SyntaxError {

        parseCondOrExpr();
        while (currentToken.kind == Token.EQ) {
            acceptOperator();
            parseCondOrExpr();
        }

    }

    void parseCondOrExpr() throws SyntaxError {

        parseCondAndExpr();
        while (currentToken.kind == Token.OROR) {
            acceptOperator();
            parseCondAndExpr();
        }
    }

    void parseCondAndExpr() throws SyntaxError {

        parseEqualityExpr();
        while (currentToken.kind == Token.ANDAND) {
            acceptOperator();
            parseEqualityExpr();
        }
    }

    void parseEqualityExpr() throws SyntaxError {

        parseRelExpr();
        while (currentToken.kind == Token.EQEQ || 
               currentToken.kind == Token.NOTEQ) {
            acceptOperator();
            parseRelExpr();
        }
    }

    void parseRelExpr () throws SyntaxError {

        parseAdditiveExpr();
        while (currentToken.kind == Token.LT || 
               currentToken.kind == Token.LTEQ || 
               currentToken.kind == Token.GT || 
               currentToken.kind == Token.GTEQ) {
            acceptOperator();
            parseAdditiveExpr();
        }
    }

    void parseAdditiveExpr() throws SyntaxError {

        parseMultiplicativeExpr();
        while (currentToken.kind == Token.PLUS || 
               currentToken.kind == Token.MINUS) {
            acceptOperator();
            parseMultiplicativeExpr();
        }
    }

    void parseMultiplicativeExpr() throws SyntaxError {

        parseUnaryExpr();
        while (currentToken.kind == Token.MULT || 
               currentToken.kind == Token.DIV) {
            acceptOperator();
            parseUnaryExpr();
        }
    }

    void parseUnaryExpr() throws SyntaxError {

        switch (currentToken.kind) {
            case Token.MINUS:
                {
                    acceptOperator();
                    parseUnaryExpr();
                }
                break;

            case Token.PLUS:
                {
                    acceptOperator();
                    parseUnaryExpr();
                }
                break;

            case Token.NOT:
                {
                    acceptOperator();
                    parseUnaryExpr();
                }
                break;

            default:
                parsePrimaryExpr();
                break;
        }
    }

    void parsePrimaryExpr() throws SyntaxError {

        switch (currentToken.kind) {

            case Token.ID:
                {
                    parseIdent();
                    if (currentToken.kind == Token.LPAREN) {
                        parseArgList();
                    } else if (currentToken.kind == Token.LBRACKET) {
                        accept();
                        parseExpr();
                        match(Token.RBRACKET);
                    }
                }
                break;

            case Token.LPAREN:
                {
                    accept();
                    parseExpr();
                    match(Token.RPAREN);
                }
                break;

            case Token.INTLITERAL:
                parseIntLiteral();
                break;

            case Token.FLOATLITERAL:
                parseFloatLiteral();
                break;
            
            case Token.BOOLEANLITERAL:
                parseBooleanLiteral();
                break;

            case Token.STRINGLITERAL:
                accept();
                break;

            default:
                syntacticError("illegal parimary expression", currentToken.spelling);
            
        }
    }


    // ========================== PARAMETERS ========================


    void parseParaList() throws SyntaxError {

        match(Token.LPAREN);
        if (currentToken.kind != Token.RPAREN) 
            parseProperParaList();
        match(Token.RPAREN);
    }

    void parseProperParaList() throws SyntaxError {

        parseParaDecl();
        while (currentToken.kind == Token.COMMA) {
            accept();
            parseParaDecl();
        }
    }

    void parseParaDecl() throws SyntaxError {

        parseType();
        parseDeclarator();
    }

    void parseArgList() throws SyntaxError {

        match(Token.LPAREN);
        if (currentToken.kind != Token.RPAREN) 
            parseProperArgList();
        match(Token.RPAREN);
    }

    void parseProperArgList() throws SyntaxError {

        parseArg();
        while (currentToken.kind == Token.COMMA) {
            accept();
            parseArg();
        }
    }

    void parseArg() throws SyntaxError {

        parseExpr();
    }


    // ========================== LITERALS ========================

    // Call these methods rather than accept().  In Assignment 3, 
    // literal AST nodes will be constructed inside these methods. 

    void parseIntLiteral() throws SyntaxError {

        if (currentToken.kind == Token.INTLITERAL) {
            accept();  
        } else 
            syntacticError("integer literal expected here", "");
    }

    void parseFloatLiteral() throws SyntaxError {

        if (currentToken.kind == Token.FLOATLITERAL) {
            accept();
        } else 
            syntacticError("float literal expected here", "");
    }

    void parseBooleanLiteral() throws SyntaxError {

        if (currentToken.kind == Token.BOOLEANLITERAL) {
            accept();
        } else 
            syntacticError("boolean literal expected here", "");
    }

}
