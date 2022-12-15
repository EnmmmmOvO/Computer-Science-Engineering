import Data.List(elemIndex)
import Data.Char(isSpace,isDigit)

{-
  The inference rules go directly from strings to parse trees.
  We'll instead go from token lists to parse trees.

  To go all the way, we just have to: parser . lexer
   (. is Haskell function composition)
 -}

data ArithT =
  LParenT
  | RParenT
  | NumT Int
  | TimesT
  | PlusT
  deriving (Eq,Show)
{- deriving Show: "make ArithT pretty-printable"
   deriving Eq:   "make ArithT comparable with the == (equality) operator"
 -}

lexer :: String -> [ArithT]
lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isDigit c =
    let (digits,rest) = span isDigit (c:cs)
    in NumT(read digits):lexer cs
  | otherwise =
    (case c of
       '(' -> LParenT
       ')' -> RParenT
       '*' -> TimesT
       '+' -> PlusT
       _ -> error "Unrecognised character"
    ):lexer cs

data Arith =
  NumE Int
  | TimesE Arith Arith
  | PlusE Arith Arith
  deriving (Eq,Show)

{- parse ts will:
    - parse an arithmetic expression from a *prefix* of ts
    - also return the leftovers
 -}
parseAtom :: [ArithT] -> (Arith,[ArithT])
parsePExp :: [ArithT] -> (Arith,[ArithT])
parseSExp :: [ArithT] -> (Arith,[ArithT])
{- The following clause implements the inference rule
           i Int
    ______________________
   i Atom <--> (Num i) AST
 -}
parseAtom (NumT n:ts) = (NumE n,ts)
parseAtom (LParenT:ts) =
  case parseSExp ts of
    (e, RParenT:ts) -> (e, ts)
parseAtom (t:ts) = error("Unrecognised token: " ++ show t)
{- Observation: both inference rules for PExp require us to find
   an Atom at the left.
 -}
parsePExp ts =
  case parseAtom ts of
    -- If the first pattern matches, we're in the inference rule for times
    (e1,TimesT:ts2) ->
      let (e2, ts3) = parsePExp ts2
      in (TimesE e1 e2, ts3)
    -- If not, we're in the inference rule for atoms, and nothing more to do
    (e1,ts2) -> (e1, ts2)
parseSExp ts =
  case parsePExp ts of
    (e1,PlusT:ts2) ->
      let (e2, ts3) = parseSExp ts2
      in (PlusE e1 e2, ts3)
    (e1,ts2) -> (e1, ts2)

-- A top-level parser function that complains if there are leftovers.
parse :: [ArithT] -> Arith
parse ts =
  case parseSExp ts of
    (e,[]) -> e
    (_,c:_) -> error ("Unexpected token: " ++ show c)

{- This unparser will produce more parentheses than strictly necessary.
   It's a fun exercise to make one that produces minimal parentheses.
 -}
unparse :: Arith -> String
unparse(NumE i) = show i
unparse(TimesE e e') = "(" ++ unparse e ++ "*" ++ unparse e' ++ ")"
unparse(PlusE e e') = "(" ++ unparse e ++ "+" ++ unparse e' ++ ")"

{- "just raw strings" representation -}
data ArithL =
  NumL Int
  | TimesL ArithL ArithL
  | PlusL ArithL ArithL
  | VarL String
  | LetL String ArithL ArithL
  deriving (Eq,Show)

{- de Bruijn represenation -}
data ArithDB =
  NumDB Int
  | TimesDB ArithDB ArithDB
  | PlusDB ArithDB ArithDB
  | VarDB Int
  | LetDB ArithDB ArithDB -- No need for var names on binding occurences
  deriving (Eq,Show)

data ArithHOAS =
  NumHOAS Int
  | TimesHOAS ArithHOAS ArithHOAS
  | PlusHOAS ArithHOAS ArithHOAS
  | LetHOAS ArithHOAS (ArithHOAS -> ArithHOAS)
  | FreeHOAS String -- only used for convenience when converting from HOAS.
{-  deriving (Eq,Show)  doesn't work
    - Functions aren't considered comparable using == in Haskell.
    - Functions aren't considered pretty-printable either
 -}


example = LetHOAS (NumHOAS 3) (\x -> PlusHOAS x (NumHOAS 2))

{- Generic substitution problem:
    Whenever we change our syntax, we need to redefine substitution

   In the HOAS setting. Substitution is just function application.
 -}

-- The variable name at the i:th position
-- is the name of the i:th binder
deBruijnify :: [String] -> ArithL -> ArithDB
deBruijnify env (NumL i) = NumDB i
deBruijnify env (VarL s) =
  case elemIndex s env of
    Nothing -> error ("Out of scope variable: " ++ s)
    Just n -> VarDB n
deBruijnify env (TimesL e e') =
  TimesDB (deBruijnify env e) (deBruijnify env e')
deBruijnify env (PlusL e e') =
  PlusDB (deBruijnify env e) (deBruijnify env e')
deBruijnify env (LetL x e e') =
  LetDB (deBruijnify env e) (deBruijnify (x:env) e')

-- When we deconvert from de Bruijn notation,
-- we need to somehow invent variable names.
-- Here we say that the variable name at the
-- (n-i-1):th position is xi.
dedeBruijnify :: Int -> ArithDB -> ArithL
dedeBruijnify n (NumDB i) = NumL i
dedeBruijnify n (VarDB i) =
  if i <= n then
    VarL("x" ++ show(n-i-1))
  else
    error $ "Index out of scope: x" ++ show i
dedeBruijnify n (TimesDB e e') =
  TimesL (dedeBruijnify n e) (dedeBruijnify n e')
dedeBruijnify n (PlusDB e e') =
  PlusL (dedeBruijnify n e) (dedeBruijnify n e')
dedeBruijnify n (LetDB e e') =
  LetL ("x" ++ show n) (dedeBruijnify n e) (dedeBruijnify (n+1) e')

{-
   The following exp corresponds to
     let x = 5 in
       5 +
       (let y = 4 in
          x
        end)
     end
 -}
-- deBruijnify [] (LetL "x" (NumL 5) (PlusL (VarL "x") (LetL "y" (NumL 4) (VarL "x"))))

toHOAS :: [(String,ArithHOAS)] -> ArithL -> ArithHOAS
toHOAS env (NumL i) = NumHOAS i
toHOAS env (VarL s) =
  case lookup s env of
    Nothing -> error ("Out of scope variable: " ++ s)
    Just e -> e
toHOAS env (TimesL e e') =
  TimesHOAS (toHOAS env e) (toHOAS env e')
toHOAS env (PlusL e e') =
  PlusHOAS (toHOAS env e) (toHOAS env e')
toHOAS env (LetL x e e') =
  LetHOAS (toHOAS env e) (\e'' -> toHOAS ((x,e''):env) e')
  {-
     The (\x -> ...) notation defines functions without giving them
     names.  These are called lambda expression.  For example,
       (\x -> x + 1)
     is a function that adds 1 to an element, and can be called thus:
       (\x -> x + 1) 2

     Here, the body of the Let expression needs to be a function,
     which given a HOAS expression inserts that expression
     at all occurrences of x in the current scope.
     We achieve that by binding it to x in the current env,
     shadowing any pre-existing binders.
 -}

{-
   Just like the deBruijn case, we need to invent variable names.
   This time around, we'll just use a number n to keep track of how
   many variable names have already been used.
 -}
fromHOAS :: Int -> ArithHOAS -> ArithL
fromHOAS n (NumHOAS i) = NumL i
fromHOAS n (FreeHOAS s) = VarL s
fromHOAS n (TimesHOAS e e') =
  TimesL (fromHOAS n e) (fromHOAS n e')
fromHOAS n (PlusHOAS e e') =
  PlusL (fromHOAS n e) (fromHOAS n e')
fromHOAS n (LetHOAS e e') =
  let x = "x" ++ show n in
    LetL ("x" ++ show n) (fromHOAS n e) (fromHOAS (n+1) (e' (FreeHOAS x)))