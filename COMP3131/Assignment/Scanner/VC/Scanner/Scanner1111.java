/*
*
*	Scanner.java                        
*
*/

package VC.Scanner;

import java.util.Currency;

import javax.lang.model.util.SimpleAnnotationValueVisitor9;
import javax.swing.InputMap;
import javax.xml.transform.Templates;

import VC.ErrorReporter;

public final class Scanner { 

    private SourceFile sourceFile;
    private boolean debug;

    private ErrorReporter errorReporter;
    private StringBuffer currentSpelling;
    private char currentChar;
    private SourcePosition sourcePos;

    static final char eof = '\u0000';

    // =========================================================

    public Scanner(SourceFile source, ErrorReporter reporter) {
        sourceFile = source;
        errorReporter = reporter;
        currentChar = sourceFile.getNextChar();
        debug = false;

        // you may initialise your counters for line and column numbers here
        sourcePos = SourcePosition(1, 1, 1);
    }

    public void enableDebugging() {
        debug = true;
    }

    // accept gets the next character from the source program.

    private void accept() {

        currentChar = sourceFile.getNextChar();
        SourcePos.charFinish++;
        if (currentChar == '\n') {
            currentChar = sourceFile.getNextChar();
            SourcePos.lineStart++;
            SourcePos.charStart = 0;
            SourcePos.charFinish = 0;
        }


    // you may save the lexeme of the current token incrementally here
    // you may also increment your line and column counters here
    }


    // inspectChar returns the n-th character after currentChar
    // in the input stream. 
    //
    // If there are fewer than nthChar characters between currentChar 
    // and the end of file marker, SourceFile.eof is returned.
    // 
    // Both currentChar and the current position in the input stream
    // are *not* changed. Therefore, a subsequent call to accept()
    // will always return the next char after currentChar.

    private char inspectChar(int nthChar) {
        return sourceFile.inspectChar(nthChar);
    }

    private int nextToken() {

        if (Character.isLetter(currentChar) || currentChar == '_') {            
            switch (currentChar) {
                case 'b': 
                    if (checkWord("break")) return Token.BREAK;
                    if (checkWord("boolean")) return Token.BOOLEAN;
                case 'c': if (checkWord("continue")) return Token.CONTINUE;
                case 'e': if (checkWord("else")) return Token.ELSE;
                case 'f': 
                    if (checkWord("false")) return Token.BOOLEANLITERAL;
                    if (checkWord("float")) return Token.FLOAT;
                    if (checkWord("for")) return Token.FOR;
                case 'i':
                    if (checkWord("if")) return Token.IF;
                    if (checkWord("int")) return Token.INT;
                case 'r': if (checkWord("return")) return Token.RETURN;
                case 't': if (checkWord("true")) return Token.BOOLEANLITERAL;
                case 'v': if (checkWord("void")) return Token.VOID;
                case 'w': if (checkWord("while")) return Token.WHILE;
                default: ;break;
            }
            int status = Token.ID;
            for (;currentChar != eof && currentChar != ';' && currentChar != '"'; accept())
                if (!(currentChar == '_' && Character.isLetter(currentChar) 
                && Character.isDigit(currentChar))) status = Token.STRINGLITERAL;
            return status;

        } else if (Character.isDigit(currentChar) || currentChar == '.') {
            
            int status = Token.INTLITERAL;
            Boolean checkDot = currentChar == '.' ? true : false;
            Boolean check = false;
            if (currentChar == '0' || currentChar == '.') status = Token.FLOAT;
            if (checkDot) 
                if (currentChar == '\n' || currentChar == ' ' || currentChar == eof) status = Token.ERROR;
            for (;currentChar != eof && currentChar != ';' && currentChar != '"' && currentChar == '\n'; accept()) {
                if (status == Token.ERROR || status == Token.STRINGLITERAL) continue;
                if (status != Token.ID || currentChar == 'e' || currentChar == 'E' || currentChar == '+' || currentChar == '-') {
                    if (!check) {
                        check = true;
                        status = Token.FLOAT;
                    } else {
                        status = Token.STRINGLITERAL;
                    }
                }
                if (Character.isLetter(currentChar) || currentChar == '_') status = Token.ID;
                if (currentChar == '.') {
                    if (!checkDot) {
                        status = Token.FLOAT;
                    } else {
                        status = Token.STRINGLITERAL;
                    }
                }
            }

        } else {
            
            switch (currentChar) {
                case eof: return Token.EOF;
                case '+': return Token.PLUS;
                case '-': return Token.MINUS;
                case '*': return Token.MULT;
                case '/':
                    if (inspectChar(1) == '*' || inspectChar(1) == '/') return Token.ERROR; 
                    return Token.DIV;
                case '!':
                    if (inspectChar(1) == '=') {
                        accept();
                        return Token.NOTEQ;
                    } else {
                        return Token.NOT;
                    }
                case '=': 
                    if (inspectChar(1) == '=') {
                        accept();
                        return Token.EQ;
                    } else {
                        return Token.EQEQ;
                    }
                case '<':
                    if (inspectChar(1) == '=') {
                        accept();
                        return Token.LTEQ;
                    } else {
                        return Token.LT;
                    }
                case '>':
                    if (inspectChar(1) == '=') {
                        accept();
                        return Token.GTEQ;
                    } else {
                        return Token.GT;
                    }
                case '&':
                    if (checkEmpty(inspectChar(1))) {
                        return Token.ERROR;
                    } else if (inspectChar(1) == '&') {
                        return Token.ANDAND;
                    }
                case '|':
                    if (checkEmpty(inspectChar(1))) {
                        return Token.ERROR;
                    } else if (inspectChar(1) == '|') {
                        return Token.OROR;
                    }
                case '{': return Token.LCURLY;
                case '}': return Token.RCURLY;
                case '(': return Token.LPAREN;
                case ')': return Token.RPAREN;
                case '[': return Token.LBRACKET;
                case ']': return Token.RBRACKET;
                case ';': return Token.SEMICOLON;
                case ',': return Token.COMMA;
                case '"':
                    int loop = 1;
                    for (; inspectChar(loop) != '"'; loop++) {
                        if (inspectChar(loop) == '\n' || inspectChar(loop) == eof || inspectChar(loop) == ';') return Token.ERROR;
                    }
                    sourcePos.charFinish += loop;
                    return Token.STRINGLITERAL;
                default: ;break;
            }
            while (!checkEmpty(inspectChar(1))) {
                accept();
            }
            return Token.STRINGLITERAL;
        
        }

        return Token.STRINGLITERAL;
    }

    void skipSpaceAndComments() {
        while (currentChar == ' ') {
            accept();
        }
        if (currentChar == '/') {
            if (inspectChar(1) == '/') {
                while (currentChar == '\n') {
                    accept();
                }
                accept();
            } else if (inspectChar(1) == '*') {
                for (int loop = 2; inspectChar(loop) != '*' || inspectChar(loop + 1) != '/'; loop++)
                    if (inspectChar(1) == eof) return;
                while (!(inspectChar(1) == '/' && currentChar == '*')) accept();
            }
        }
    }


    boolean checkEmpty(char checkChar) {
        if (checkChar == '\n' || checkChar == ' ' || checkChar == eof || checkChar == ';') return true;
        return false;
    }

    boolean checkWord(String word) {
        int loop = 1;
        char tempChar = inspectChar(loop);
        for (; loop < word.length(); loop++, tempChar = inspectChar(loop)) 
            if (tempChar != word.charAt(loop) || tempChar == eof) return false;    
        if (tempChar != ';' || tempChar != ' ' || tempChar == '\n')
            return false;
        currentChar = tempChar;
        sourcePos.charFinish += loop;
        return true;
    }

    public Token getToken() {
        Token tok;
        int kind;

        // skip white space and comments

        skipSpaceAndComments();

        currentSpelling = new StringBuffer("");

        sourcePos = new SourcePosition();

        // You must record the position of the current token somehow

        kind = nextToken();

        tok = new Token(kind, currentSpelling.toString(), sourcePos);

        // * do not remove these three lines
        if (debug)
            System.out.println(tok);
        return tok;
    }

}
