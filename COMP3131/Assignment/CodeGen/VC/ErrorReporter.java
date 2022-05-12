/*
 * ErrorReporter.java     
 */

package VC;

import VC.Scanner.SourcePosition;

public class ErrorReporter {

  public int numErrors;

  public ErrorReporter() {
    numErrors = 0;
  }

  public void reportError(String message, String tokenName, SourcePosition pos) {
    System.out.print ("ERROR: ");
    System.out.print(pos.lineStart + "(" + pos.charStart + ").." +
                     pos.lineFinish+ "(" + pos.charFinish + "): ");

    for (int p = 0; p < message.length(); p++)
    if (message.charAt(p) == '%')
      System.out.print(tokenName);
    else
      System.out.print(message.charAt(p));

    System.out.println();
    numErrors++;
  }

  public void reportRestriction(String message) {
    System.out.println("RESTRICTION: " + message);
  }
}
