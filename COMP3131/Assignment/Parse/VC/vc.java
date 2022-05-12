/*
 * 
 */

package VC;

import VC.Scanner.Scanner;
import VC.Scanner.SourceFile;
import VC.Parser.Parser;
import VC.TreeDrawer.Drawer;
import VC.TreePrinter.Printer;
import VC.UnParser.UnParser;
import VC.ASTs.AST;

public class vc {

    private static Scanner scanner;
    private static ErrorReporter reporter;
    private static Parser parser;
    private static Drawer drawer;
    private static Printer printer;
    private static UnParser unparser;

    private static int drawingAST = 0;
    private static String inputFilename; 
    private static String VCFilename = null;
    private static String ASTFilename = null; 

    private static AST theAST;

    private static void cmdLineOptions() {
      System.out.println("Usage: java VC.vc [-options] filename");
      System.out.println();
      System.out.println("where options include:");
      System.out.println("	-ast 		    display the AST (without SourcePosition)");
      System.out.println("	-astp 		    display the AST (with SourcePosition)");
      System.out.println("	-t file             print the AST into <file>"); 
      System.out.println("	-u file  	    unparse the AST into <file>"); 
      System.exit(1);
    }

    public static void main(String[] args) {
        int i = 0;
        String arg;

        while (i < args.length && args[i].startsWith("-")) {
          arg = args[i++];
          
          if (arg.equals("-ast"))
            drawingAST = 1;
          else if (arg.equals("-astp"))
            drawingAST = 2;
          else if (arg.equals("-u")) {
            if (i < args.length)
              VCFilename = args[i++];
            else {
              System.out.println("[# vc #]: invalid option " + arg);
              cmdLineOptions();
            }
          } else if (arg.equals("-t")) {
            if (i < args.length)
              ASTFilename = args[i++];
            else {
              System.out.println("[# vc #]: invalid option " + arg);
              cmdLineOptions();
            }
          }
        }
        if (i == args.length)
           cmdLineOptions();
        else
           inputFilename = args[i];

        System.out.println("======= The VC compiler =======");

        SourceFile source = new SourceFile(inputFilename);

        reporter = new ErrorReporter();
        scanner  = new Scanner(source, reporter);
        parser   = new Parser(scanner, reporter);

        if (ASTFilename == null)
          ASTFilename = inputFilename + "t";
        printer = new Printer(ASTFilename);

        if (VCFilename == null)
          VCFilename = inputFilename + "u";
        unparser = new UnParser(VCFilename);

        try {
        theAST = parser.parseProgram();
        }
        catch (Exception e) { 
          System.out.println("PANIC:");
	  e.printStackTrace(); 
          System.exit(1);
        }

        if (reporter.numErrors == 0) {
           System.out.println ("Compilation was successful.");
 	   drawer   = new Drawer();
           if (drawingAST == 2)
             drawer.enableDebugging(); // show SourcePosition
           if (drawingAST != 0)
             drawer.draw(theAST); // draw the AST

           printer.print(theAST);

           unparser.unparse(theAST);
        } else
           System.out.println ("Compilation was unsuccessful.");
    }
}

