{-  unit type     ()
    sum type      Either
    product type  ,
    empty type    ????

  let's make an empty type:
 -}

data Void -- This is a algebraic datatype with no constructors
          -- thus we can't construct a value that inhabits Void


{- de Morgan

     !(A /\ B) = !A \/ !B

     !(A \/ B) = !A /\ !B

   These two inequalities comprise four inequalities

   All four hold in *classical* logic,
   but only three of them hold in intuitionistic (constructive) logic.


   !A  =   A => False   becomes   A -> Void

   Let's do:

     !(A /\ B) ==> !A \/ !B

   Translate from logic to types

     ((a,b) -> Void) -> Either (a -> Void) (b -> Void)
 -}

{- Either, this is the one that doesn't hold constructively,
     or we're not clever enough right now.
 proof_dm1 :: ((a,b) -> Void) -> Either (a -> Void) (b -> Void)
 proof_dm1 f = ---
 -}

proof_dm2 :: Either (a -> Void) (b -> Void) -> ((a,b) -> Void)
proof_dm2 (Left fa) (a,b) = fa a
proof_dm2 (Right fb) (a,b) = fb b

proof_dm3 :: Either (a -> Void) (b -> Void) -> ((a,b) -> Void)
proof_dm3 (Left fa) = \x -> fa (fst x)
proof_dm3 (Right fb) = \x -> fb (snd x)

{- Function arrow is right associative

    a -> (b -> c)     =         a -> b -> c
 -}

{-
  The simplest example of something that doesn't hold constructively
  (and therefore, has an uninhabited (empty) type on the other side
   of the isomorphism) is:

    the law of the excluded middle   A \/ !A (classical tautology)


   Applying the CH isomorphism, a proof of A \/ !A
   would be a value of the following type:

     Either a (a -> Void)
 -}
{- We can't write this function, because the law of excluded middle
   doesn't hold constructively
  exm :: Either a (a -> Void)
  exm = Right (\x -> ????)
 -}
{- However, the law of the excluded middle doesn't not hold constructively

   In constructive logic, !!A is different from A

   It's possible to prove !!(A \/ !A)
 -}
dn_lem :: (Either a (a -> Void) -> Void) -> Void
dn_lem f = f (Right (\a -> f (Left a)))

{- This is an example of the *double negation translation*

     P   is a classical tautology iff
     !!P is a constructive tautology
 -}



swap :: (a,b) -> (b,a) -- Here, the universal quantifiers are in invisible ink
swap (a,b) = (b,a)

{- Three (distinct) kinds of polymorphism are often called just "polymorphism"
   - parametric polymorphism -- functions defined uniformly over all types,
                                these can be applied to any specific type
   - subtype polymorphism    -- whenever a Shape is excepted, we can supply
                                a Triangle instead
   - ad-hoc polymorphism     -- a + b    + denotes both float addition and
                                           int addition,
                                 different definitions of + for different types,
                                 which definition gets applied depends on the
                                 type of the arguments.
 -}

--(swap::(Int,Int) -> (Int,Int)) (1,2)

foo :: [a] -> [a]
foo [] = []
foo (x:xs) = xs

{-  map f (foo xs) = foo(map f xs)

 Every function that has the same
 type signature as foo above
 satisfies this equation!
 -}

{-
   filter p (map f xs) =
   map f (filter (p . f) xs)
 -}

{-
  In this lecture, circle is function
  compositions

  In Haskell, function composition is .
 -}