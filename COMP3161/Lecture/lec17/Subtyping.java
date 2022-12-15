class Animal { }

// Declare Pig to be a *subtype* of Animal
// Anywhere that an Animal is expected, you can supply a pig
class Pig extends Animal {}

class Cow extends Animal {}

class Sheep extends Animal {}

class BlackSheep extends Sheep {}

public class Subtyping {
    public static void main(String[] args) {
        /* This is something that only typechecks when you have
           something like the subtyping rule on the slides
         */
        Animal my_animal = ((Animal)new BlackSheep());
    }
}


/* The subtyping relationship <= must be partial order:
    BlackSheep <= Sheep <= Animal

    Reflexive:  forall a,    a <= a
    Transitive:
                forall a b c,   a <= b   and  b <= c   then a <= c
    Antisymmetric:
                forall a b,   if a <= b   and b <= a    then a = b
                "no cycles"


    Int <= Float

       3 + 2.2

       Real.fromInt 3 + 2.2


       3 + "hello"  |-> "3hello"

       ^ Coerce 3 directly from Int to String

       3 + "hello"  |-> 3.0 + "hello"  |-> "3.0hello"

       ^ Coerce 3 from Int to Float to String
 */

/*
  This subtype relationship, this violates the LSP:
     Rectangle <= Square

  All squares satisfy: A=s^2, where s is any side
  Rectangles don't :(

  (Square <= Rectangle may or may not work
   depending on what methods they have)

  How about:

    Int <= Float

  Here's a property of floats:
   For any Float, if you keep adding 1 to it, eventually you hit a fixed point
   Not true for Ints


  So far, we've been walking into the same honey trap that many OO language designers have:

  - It looks like subtyping should always distribute like this over type constructors
    (On first inspection, it looks like type constructors should be *covariant*)


  Suppose I need a function f from Float to Int

  Presumably, I have a Float x that I'm going to call my function with

    f(x)

  But if subtyping was always covariant, f *could* be of type Int to Float

    if f really expects an Int, it might be undefined on my Float

  Get-put-principle:
    A type constructor T(a) should be:
    - *covariant* over a if we only ever *get* a:s from T
    - *contravariant* if we only ever *put* a:s in T
    - if we need to both get and put things of type a in T,
       T should be *invariant*

            a = b
          __________
          T a <= T b
 */