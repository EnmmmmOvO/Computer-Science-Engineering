/*-*
 *^*
 *** vc.java           30/1/2022
 *^* 
 *-*/

package VC;

import VC.Scanner.Scanner;
import VC.Scanner.SourceFile;
import VC.Scanner.Token;

public class vc {

    private static Scanner scanner;
    private static ErrorReporter reporter;
    private static Token currentToken;
    private static String inputFilename; 

 
    public static void main(String[] args) {
        inputFilename = args[0];

        System.out.println("======= The VC compiler =======");

        SourceFile source = new SourceFile(inputFilename);

        reporter = new ErrorReporter();
        scanner  = new Scanner(source, reporter);
        scanner.enableDebugging();

        do 
	  currentToken = scanner.getToken();
        while (currentToken.kind != Token.EOF);
    }
}
