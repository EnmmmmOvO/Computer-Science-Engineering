data Ty =
  BoolTy
  | IntTy
  | FunTy Ty Ty -- (FunTy t1 t2) is t1 -> t2
  deriving (Show, Eq)

data Op = Times | Add | Eq
  deriving (Show, Eq)

data Exp =
  Var String -- only used for pretty-printing
  | Num Int
  | Lit Bool
  | If Exp Exp Exp
  | App Exp Exp
  | Binop Op Exp Exp
  | Recfun Ty Ty (Exp -> Exp -> Exp) -- HOAS
  | Tag Ty -- only used internally in type-checking
           -- a placeholder for an expression of type ty

-- First, a simple pretty printer
free :: Exp -> String -> Bool
free (Num n) s       = True
free (Lit b) s       = True
free (If e1 e2 e3) s  = free e1 s && free e2 s && free e3 s
free (App e1 e2) s  = free e1 s && free e2 s
free (Binop _ e1 e2) s  = free e1 s && free e2 s
free (Recfun _ _ e) s  = free (e (Num 0) (Num 0)) s
free (Tag _) s = True
free (Var s') s      = s' /= s

mkfree :: Exp -> String -> String
mkfree e s = if free e s then s else mkfree e (s++"'")

instance Show Exp where
  show (Num n) = "(Num "++show n++")"
  show (Lit b) = "(Lit "++show b++")"
  show (Recfun ty1 ty2 fn) =
    "(Recfun "++ show ty1 ++ " " ++ show ty2 ++ " (\\"++f++" -> \\"++x++" -> " ++show(fn (Var f) (Var x))++"))"
    where x = mkfree (Recfun ty1 ty2 fn) "x"
          f = mkfree (Recfun ty1 ty2 fn) "f"
  show (If e1 e2 e3) = "(If "++show e1++" "++show e2++" "++show e3++")"
  show (App e1 e2) = "(App "++show e1++" "++show e2++")"
  show (Binop op e1 e2) = "(Binop "++show op++" "++show e1++" "++show e2++")"
  show (Tag ty) = "(Tag "++show ty++")"
  show (Var s) = s

triangle =
  Recfun IntTy IntTy
    (\triang -> \n ->
      (If (Binop Eq n (Num 0))
          (Num 0)
          (Binop Add n (App triang (Binop Add n (Num (-1)))))))

-- Stack frames

{-
 data Either a b = Left a
                 | Right b
 -}

data Frame =
    IfF Exp Exp -- this represents the frame (If [] e1 e2)
  | AppR (Exp -> Exp -> Exp) -- this represents (App v [])
  | AppL Exp -- this represents (App [] e)
  | BinopL Op Exp
  | BinopR Op (Either Bool Int)
              -- think of Either as the disjoint union of (in this case) Bool and Integer

-- Stacks

type Stack = [Frame]

-- States

data State = Eval Stack Exp
           | Return Stack Exp

oneStep :: State -> State
oneStep (Eval st (Binop op e1 e2)) = Eval ((BinopL op e2):st) e1
oneStep (Return (BinopL op e2:st) (Num n)) = Eval ((BinopR op (Right n)):st) e2
oneStep (Return (BinopL op e2:st) (Lit b)) = Eval ((BinopR op (Left b)):st) e2
oneStep (Return (BinopR Add (Right n):st) (Num m)) = Return st (Num $ n + m)
oneStep (Return (BinopR Times (Right n):st) (Num m)) = Return st (Num $ n * m)
oneStep (Return (BinopR Eq (Right n):st) (Num m)) = Return st (Lit $ n == m)
oneStep (Return (BinopR Eq (Left b1):st) (Lit b2)) = Return st (Lit $ b1 == b2)

oneStep (Eval st (Num n)) = Return st (Num n)
oneStep (Eval st (Lit b)) = Return st (Lit b)
oneStep (Eval st (Recfun ty1 ty2 f)) = Return st (Recfun ty1 ty2 f)

oneStep (Eval st (If e1 e2 e3)) = Eval (IfF e2 e3:st) e1
oneStep (Return (IfF e2 e3:st) (Lit b))
  | b == True = Eval st e2
  | otherwise = Eval st e3

oneStep (Eval st (App e1 e2)) = Eval (AppL e2:st) e1
oneStep (Return (AppL e2:st) (Recfun _ _ f)) = Eval (AppR f:st) e2
oneStep (Return (AppR f:st) v) = Eval st (f (Recfun undefined undefined f) v)

eval (Return [] (Num n)) = Num n
eval (Return [] (Recfun ty1 ty2 f)) = Recfun ty1 ty2 f
eval (Return [] (Lit b)) = Lit b
eval state = eval(oneStep state)