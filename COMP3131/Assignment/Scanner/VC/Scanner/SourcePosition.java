/*
 * SourcePosition.java    
 */

// ====== PLEASE DO NOT MODIFY THIS FILE =====

// This class is used to store the positions of tokens and phrases

package VC.Scanner;

public class SourcePosition {

  public int lineStart, lineFinish;
  public int charStart, charFinish;

  public SourcePosition () {
    lineStart = lineFinish = charStart = charFinish = 0;
  }

  // can be called by the parser to store the position of a phrase
  public SourcePosition (int theLineStart, int theLineFinish) {
    lineStart = theLineStart;
    lineFinish = theLineFinish;
    charStart = 0;  
    charFinish = 0; 
  }

  // can be called by the scanner to store the position of a token
  public SourcePosition (int theLineNum, int theCharStart, int theCharFinish) {
    lineStart = lineFinish = theLineNum; 
    charStart = theCharStart;
    charFinish = theCharFinish ;
  }

  public String toString() {
    return lineStart + "(" + charStart + ").." + lineFinish + "(" + charFinish + ")";
  }
}
