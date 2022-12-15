import Control.Monad.State

{- We could start with the abstract nonsense,
    or with examples

   A monad is a type constructor m,
   equipped with two functions:

    return  "return"    a -> m a
    >>=     "bind"      m a -> (a -> m b) -> m b

   a,b are type variables (implicitly universally quantified)

   >>= is usually written in infix.

   ...that satisfy three algebraic laws:

   return is the left and right identity of >>=:

     m >>= return      =      m
     return x >>= m    =      m x

   bind should be associative:

     m >>= (\x -> m' >>= m'')    =   (m >>= m') >>= m''
 -}
bind_assoc :: Monad m => (m a) -> (a -> m b) -> (b -> m c) -> m c
bind_assoc m m' m'' =
  m >>= (\x -> m' x >>= m'')

bind_assoc' m m' m'' =
  (m >>= m') >>= m''


{- A calculator (aka a big-step semantics of arith exprs):-}
data Arith = Num Int | Plus Arith Arith | Div Arith Arith

calc :: Arith -> Maybe Int
calc (Num n) = Just n
calc (Plus e1 e2) =
  case calc e1 of
    Nothing -> Nothing
    Just n ->
      case calc e2 of
        Nothing -> Nothing
        Just m -> Just $ n + m
calc (Div e1 e2) =
  case calc e1 of
    Nothing -> Nothing
    Just n ->
      case calc e2 of
        Nothing -> Nothing
        Just m ->
          if m==0 then
            Nothing
          else
            Just $ n `div` m
{- Every time we make a recursive call, we do the exact same thing:
   - return Nothing of the recursive call gave us Nothing,
   - otherwise, use the result to continue the computation

   This is exactly the sort of pattern that bind >>= is meant to
   abstract.
 -}
{-
 data Maybe a = Nothing
              | Just a

 data List a = Nil
              | Cons a [a]

  The maybe monad:
 -}
myReturn :: a -> Maybe a
myReturn x = Just x

myBind :: Maybe a -> (a -> Maybe b) -> Maybe b
myBind Nothing f  = Nothing
myBind (Just a) f = f a

myAssert :: Bool -> Maybe ()
myAssert False = Nothing
myAssert True = Just ()

myAssert' :: Bool -> String -> Either String ()
myAssert' False s = Left s
myAssert' True s = Right ()

{- Step 1:
   reformulate our calculator using return and bind

   `f`  means  "I want to use f in infix position"

   x `f` y     parses to    f x y
 -}
calc' :: Arith -> Maybe Int
calc' (Num n) = myReturn n
calc' (Plus e1 e2) =
  calc' e1 `myBind` (\n -> calc' e2 `myBind` (\m -> myReturn $ n + m)) 
calc' (Div e1 e2) =
  calc' e1 `myBind` (\n -> calc' e2 `myBind` (\m -> myAssert (m/=0) `myBind` (\x -> myReturn $ n `div` m)))
{- That's arguably nicer? We're not juggling case expressions all day.

   Step 2:
   - use the built-in >>= and return for the Maybe monad
     (identical to the ones we defined above)
   - use Haskell's built-in do notation

     m >>= (\x -> f)

     Sugar ("do" notation)

     do
       x <- m
       f
 -}
calc'' :: Arith -> Maybe Int
calc'' (Num n) = return n
calc'' (Plus e1 e2) =
  do
    n <- calc'' e1
    m <- calc'' e2
    return $ n + m
calc'' (Div e1 e2) =
  do
    n <- calc'' e1
    m <- calc'' e2
    myAssert $ m /= 0
    return $ n `div` m

calc''' :: Arith -> Either String Int
calc''' (Num n) = return n
calc''' (Plus e1 e2) =
  do
    n <- calc''' e1
    m <- calc''' e2
    return $ n + m
calc''' (Div e1 e2) =
  do
    n <- calc''' e1
    m <- calc''' e2
    myAssert' (m /= 0) "bruh you divided by 0"
    return $ n `div` m

{- A pretty-printer for lambda-calculus in HOAS
 -}
data Lam = Var String -- just for pretty-printing
         | App Lam Lam
         | Abs (Lam -> Lam)

{-  pp s names
    if names is an infinite list of distinct names,
    you'll get a tuple (names',s) where:

     names' are the names we didn't need
     s is the pretty-printed term
 -}
pp :: Lam -> [String] -> ([String],String)
pp (Var x) names = (names,x)
pp (App s t) names =
  let (names',s') = pp s names
      (names'',t') = pp t names'
  in (names'',
      "(" ++ s' ++ " " ++ t' ++ ")"
      )
pp (Abs f) (name:names) =
  let (names',s) = pp (f (Var name)) names
  in (names',
      "(" ++ name ++ ". " ++ s ++ ")")

nats :: [Int]
nats = 0:map (\x -> x + 1) nats

names :: [String]
names = map (\x -> "x" ++ show x) nats

{- State monad bind
 -}
myStateReturn :: a -> (s -> (s,a))
myStateReturn a s = (s,a)
myStateBind :: (s -> (s,a)) -> (a -> (s -> (s,b))) -> (s -> (s,b))
myStateBind m m' s =
  let (s',a) = m s
      (s'',b) = m' a s'
  in (s'',b)

fresh :: State [String] String
fresh =
  do xs <- gets id -- grab all the names from the state
     put (tail xs) -- put back all but the first name
     return (head xs) -- return the first name


pp' :: Lam -> State [String] String
pp' (Var x) = return x
pp' (App s t) =
  do
    s' <- pp' s
    t' <- pp' t
    return $ "(" ++ s' ++ " " ++ t' ++ ")"
pp' (Abs f) =
  do
    name <- fresh
    s <- pp' (f (Var name))
    return $ "(" ++ name ++ ". " ++ s ++ ")"

{- Q: So … what is the advantage of monad? I think it makes the code shorter but also makes code harder to understand.

   A: - makes code shorter
      - makes code more abstract (hides irrelevant bookkeeping)
      - makes it easy to change the code by swapping out the underlying monad
 -}