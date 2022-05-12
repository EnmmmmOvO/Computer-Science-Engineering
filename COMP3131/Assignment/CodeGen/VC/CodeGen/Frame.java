/*
 * Frame.java
 */

package VC.CodeGen;

import java.util.Stack;

 public class Frame {

    // true if the function being compiled is main and false otherwise
    private final boolean _main;

   // The index for the next new label to be allocated in this frame
   private int label;

   // The local variables of a function (known as method in Java)
   // are assigned indices starting from 0.
   //
   // The indices for an instance method with n parameters are:
   //  variable                           index
   // ===================-=======================
   //  this                                 0 
   //  para 1                               1 
   //                    ...
   //  para n                               n 
   //  (lexically) first local variable   n + 1
   //  (lexically) second local variable  n + 2
   // 
   // The indices for a class method with n parameters are:
   //  variable                           index
   // ===================-=======================
   //  para 1                               0 
   //                    ...
   //  para n                             n - 1 
   //  (lexically) first local variable   n 
   //  (lexically) second local variable  n + 1
   // 
   // See page 73, T Lindholm and F Yellin, The JVM spec, 2nd ed.

   private int localVarIndex;

   // Simulate the execution of byte code to determine at compile-time
   // the maximum depth of the operand stack for a method. 
   // See page 73, T Lindholm and F Yellin, The JVM spec, 2nd ed.

   private int currentStackSize;
   private int maximumStackSize;

   // Stacks for storing labels used for translating continue and break in while
   // These labels are inherited attributes

   public Stack<String> conStack; 
   public Stack<String> brkStack; 

   // Stacks for storing labels marking the beginning and end of a scope. 
   // These labels are inherited attributes and used in generating 
   // .VAR directive

   public Stack<String> scopeStart;
   public Stack<String> scopeEnd; 

   public Frame(boolean _main) {
     this._main = _main;
     label = 0;
     localVarIndex = 0;
     currentStackSize = 0;
     maximumStackSize = 0;
     conStack = new Stack<String>();
     brkStack = new Stack<String>();
     scopeStart = new Stack<String>();
     scopeEnd = new Stack<String>();
   }

   public boolean isMain() { 
     return _main;
   }

  // returns the next new local variable index for this frame

   public int getNewIndex() { 
     if (localVarIndex >= JVM.MAX_LOCALVARINDEX) {
       System.out.println("The maximum local variable index (" + JVM.MAX_LOCALVARINDEX + ") reached.");
       System.exit(1);
     }
     return localVarIndex++;
   }

  // returns the next new label for this frame

   public String getNewLabel() { 
     return "L" + label++;
   }

   // All the following functions are used in calculating the maximum
   // operand stack size at compile time

   public void push() {
     push(1);
   }

   public void push(int i) {
   //System.out.println("\t push called "  + i );
     currentStackSize += i;
     if (currentStackSize < 0 || currentStackSize > JVM.MAX_OPSTACK) {
       System.out.println("Invalid operand stack size.");
       System.out.println("Current operand stack size is " + currentStackSize + ".");
       System.out.println("You wanted to push " + i + ((i == 1) ? " operand" : " operands") + " to the stack.");
       System.out.println("The size of the operand stack is limited to the range 0 .. " + JVM.MAX_OPSTACK + ".");
       System.out.println("Good luck with debugging your code generator."); 
       System.exit(1);
     }

     if (currentStackSize > maximumStackSize)
        maximumStackSize = currentStackSize;
   }
  
   public void pop() {
     pop(1);
   }

   public void pop(int i) {
	 //System.out.println("\t pop called "  + i );
     currentStackSize -= i;
     
     if (currentStackSize < 0) {
       System.out.println("Invalid operand stack size.");
       System.out.println("Current operand stack size is " + currentStackSize + ".");
       System.out.println("You wanted to pop " + i + ((i == 1) ? " operand" : " operands") + " to the stack.");
       System.out.println("The size of the operand stack is limited to the range 0 .. " + JVM.MAX_OPSTACK + ".");
       System.out.println("Good luck with debugging your code generator."); 
       System.exit(1);
     }
   }
  
   public int getMaximumStackSize() {
     return maximumStackSize;
   }
  public int getCurStackSize() {
     return currentStackSize;
   }
 }
