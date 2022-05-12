/*
 * SyntaxError.java 
 *
 * Presently, the parser uses the so-called panic-mode
 * recovery. On encountering the first syntax error, the 
 * parser prints a message with a line number indicating
 * where the error has occurred, and then stops.
 */

package VC.Parser;

class SyntaxError extends Exception {

  SyntaxError() {
    super();
  };

  SyntaxError (String s) {
    super(s);
  }

}
