/**
 * Demo file, it may not be correct and/or complete.  
 * Please watch the corresponding lecture(s) for more explanations.
 * 
 * @author ashesh
 */

package pizza;

/**
 * A Law of Demeter example in Java.
 * Based on the example by Alvin Alexander, http://alvinalexander.com.
 * This is an adaptation of the source code example from the book
 * The Pragmatic Programmer.
 */
public class LawOfDemeterInJava
{
  private  Foo foo = new Foo();
  /**
   * Good examples of following the Law of Demeter.
   */
  public void goodExamples(Pizza pizza) {
    //Foo foo = new Foo();
    
    // (1) it's okay to call our own methods
    doSomething();
    
    // (2) it's okay to call methods on objects passed in to our method
    int price = pizza.getPrice();
    
    // (3) it's okay to call methods on any objects we create
    Topping cheeseTopping = new CheeseTopping();
    float weight = cheeseTopping.getWeightUsed();
    
    // (4) any directly held component objects
    foo.doBar();
  }
  
  private void doSomething()  {
    // do something here ...
  }
}