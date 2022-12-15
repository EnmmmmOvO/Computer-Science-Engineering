/* Types

  Q: What are the types in this program?
    -- things I unambigously agree are types
    String, String[], Shape, Rectangle, Triangle

    --- arguable (let's not get too hung up on whether  they fit)
      public -- access control specification
      class
      void   -- denotes the absence of a type
  Q: what is a type?
   - a set of object of the same kind
     ^^^^ probably closest to what we're doing in this course
   - a structure to store the data
   - an interface standard to access the data
   - an architecture-specific amount of memory, e.g. x number of bytes
   - can’t types also define functionality? 

   my suggestion: a type is a set of data items
                  Int = {0,1,2,3,-1,-2,...}

  Q: what are types for?
  - abstraction (related to providing an interface)
  - static analysis
  - analysis the logic of the program without actually running it
  - Layman: for grouping and simple understandability of nature of object 
  - the avoidance of paradoxes
    (inability to distinguish between things of the same type)
  - Type errors exists only when concept of types is introduced :D 

  - types let you avoid type errors
    - how do you *know* that your type system avoid type errors?

 */
class Shape {}

class Rectangle extends Shape {}

class Triangle extends Shape {}

public class Hello {

    public static Triangle Rectangle2Triangle(Rectangle rect) {
        Triangle[] triangles = new Triangle[1]; // make a new triangle array of length 1
        Shape[] shapes = triangles; // shapes is a shape array, that aliases "triangles"
        shapes[0] = rect; // whichever array shapes is a pointer to, put the rectangle first
        return triangles[0]; // return the first triangle (which is a square)
    }

    public static void main(String[] args) {
        /* Two possibilities:
           1 the program just keeps going
           2 we get some kind of runtime error

           Whichever one happens, we get a violation
            of a mathematical property of type systems.
           1 subject reduction (if I have a well-typed program,
                                that doesn't do type casts,
                                and I do some computation, 
                                it stays well-typed)
           2 progress (the behaviour of every well-typed program
                       is well-defined)
         */
        Rectangle2Triangle(new Rectangle());
        //(Triangle)(new Rectangle());
        System.out.println("Hello World!\n");
    }

}