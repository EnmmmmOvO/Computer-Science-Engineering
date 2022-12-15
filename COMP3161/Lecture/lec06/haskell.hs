data Arith =
    Num Int
  | Let Arith (Arith -> Arith)
  | Plus Arith Arith
  | Times Arith Arith
  | Var  String -- Only for pretty-printing
  -- deriving Show doesn't work because we have functions

{- free e1 s returns true iff s is free in e1 -}
free :: Arith -> String -> Bool
free (Num n) s       = True
free (Let s1 e2) s   = free s1 s && free(e2 (Num 0)) s
free (Plus s1 e2) s  = free s1 s && free e2 s
free (Times s1 e2) s = free s1 s && free e2 s
free (Var s') s      = s' /= s

{- Returns a name that is free in e -}
mkfree :: Arith -> String -> String
mkfree e s = if free e s then s else mkfree e (s++"'")

{- We need to write and install our own pretty-printer for Arith,
   because Haskell doesn't have a default way of pretty-printing
   functions (used here in the HOAS-style Let clause).

   This is just here for testing.  Don't worry if you're not sure
   what's going on here---this will be covered later in the course.
 -}
instance Show Arith where
  show (Num n) = "(Num "++show n++")"
  show (Let e1 e2) =
    "(Let "++show e1++" (\\x -> "++show(e2 (Var x))++"))"
    where x = mkfree (Let e1 e2) "x"
  show (Times e1 e2) = "(Times "++show e1++" "++show e2++")"
  show (Plus e1 e2) = "(Plus "++show e1++" "++show e2++")"
  show (Var s) = s


{- Fortunately, the big-step semantics is
   unambiguous, so we don't need to make any
   implementation decisions.
 -}
eval :: Arith -> Int
eval (Num n) = n
eval (Plus e1 e2) =
  eval e1 + eval e2
  {-
  let v1 = eval e1
      v2 = eval e2
  in
    v1 + v2
  -}  
eval (Times e1 e2) =
  eval e1 * eval e2  
eval (Let e1 e2) =
  let v1 = eval e1
  in
    eval (e2 (Num v1))
{-
  data Maybe a = Nothing | Just a
 -}

step :: Arith -> Maybe Arith
step (Num n) = Nothing
step (Plus (Num n) (Num m)) = Just $ Num (n + m)
step (Plus (Num n) e) =
  case step e of
    Nothing -> Nothing
    Just e' -> Just(Plus (Num n) e')
step (Plus e1 e2) =
  case step e1 of
    Nothing -> Nothing
    Just e1' -> Just(Plus e1' e2)
step (Times (Num n) (Num m)) = Just $ Num (n * m)
step (Times (Num n) e) =
  case step e of
    Nothing -> Nothing
    Just e' -> Just(Times (Num n) e')
step (Times e1 e2) =
  case step e1 of
    Nothing -> Nothing
    Just e1' -> Just(Times e1' e2)
step (Let (Num n) e2) =
  Just(e2 (Num n))
step (Let e1 e2) =
  case step e1 of
    Nothing -> Nothing
    Just e1' -> Just(Let e1' e2)