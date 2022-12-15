{- Polymorphism is the reason why you don't need separate length functions
   for [Int] [()]

 -}

mylength :: [a] -> Int
mylength [] = 0
mylength (x : xs) = 1 + mylength xs

{- Type inference is what (often) allows you to leave out type signatures -}

myotherlength [] = 0
myotherlength (x : xs) = 1 + myotherlength xs


triang :: Int -> Int
triang 0 = 0
triang n = n + triang(n-1)


{- In MinHS

   recfun triang :: (Int -> Int) n =
     if n == 0 then
       0
     else
       n + triang(n-1)

  e1 e2  denotes function application

   (recfun triang :: (Int -> Int) n =
      if n == 0 then
        0
      else
        n + triang(n-1)) 5
 -}

{- In Haskell:   
 -}
--average x y = (x + y) / 2

data Ty =
  BoolTy
  | IntTy
  | FunTy Ty Ty -- (FunTy t1 t2) is t1 -> t2
  deriving (Show, Eq)

data Op = Times | Add | Eq

data Exp =
  Var String -- only used for pretty-printing
  | Num Int
  | Lit Bool
  | If Exp Exp Exp
  | App Exp Exp
  | Binop Op Exp Exp
  | Recfun Ty Ty (Exp -> Exp -> Exp)
  | Tag Ty -- only used internally in type-checking
           -- a placeholder for an expression of type ty

{- This pretty-printer is defined in two layers to avoid printing redundant parentheses.
   - ppAtom is for pretty-printing things as they should appear on the left of function arrows
     (with added parentheses for disambiguation)
   - ppType is for pretty-printing things as they should appear on the top level, or the right
     of a function arrow.

   Note the similarities between this and the disambiguated syntaxes we've seen earlier in the course.
   This is not an accident.
 -}
ppAtom BoolTy = "Bool"
ppAtom IntTy  = "Int"
ppAtom x = "(" ++ ppType x ++ ")"
ppType (FunTy argty retty) = ppAtom argty ++ " -> " ++ ppType retty
ppType x = ppAtom x

ppOp Times = "*"
ppOp Add   = "+"
ppOp Eq    = "=="

{- We won't be as bothered with redundant parens here,
    but a similar technique could be used.
   This would be a decent Haskell exercise if you're keen.

  We need to generate fresh variable names for Recfun.
  We adopt the simple solution of having an incrementing
  counter n, and letting all names xn, fn etc.
 -}
ppExp n (Var s) = s
ppExp n (Num i) = show i
ppExp n (Lit b) = show b
ppExp n (Binop op e1 e2) =
  concat ["(",ppExp n e1," ",ppOp op," ",ppExp n e1,")"]
ppExp n (If e1 e2 e3) =
  concat ["(if ",ppExp n e1," then ",ppExp n e2," else ",ppExp n e3,")"]
ppExp n (App e1 e2) =
  concat ["(",ppExp n e1," ",ppExp n e2,")"]
ppExp n (Recfun argty retty fun) =
  let f = "f"++show n
      x = "x"++show n
  in
    concat ["(recfun ",f," :: (",ppType (FunTy argty retty),") ",x," = ",ppExp (n+1) (fun (Var f) (Var x)),")"]

pp e = ppExp 0 e

{-
  data Maybe a = Nothing | Just a
 -}

typecheck :: Exp -> Maybe Ty
typecheck (Num n) = Just IntTy
typecheck (Lit b) = Just BoolTy
typecheck (Binop Add e1 e2) =
  case (typecheck e1, typecheck e2) of
    (Just IntTy, Just IntTy) -> Just IntTy
    _ -> Nothing
typecheck (Binop Times e1 e2) =
  case (typecheck e1, typecheck e2) of
    (Just IntTy, Just IntTy) -> Just IntTy
    _ -> Nothing
typecheck (Binop Eq e1 e2) =
  case (typecheck e1, typecheck e2) of
    (Just IntTy, Just IntTy) -> Just BoolTy
    (Just BoolTy, Just BoolTy) -> Just BoolTy    
    _ -> Nothing
typecheck (If e1 e2 e3) =
  case (typecheck e1, typecheck e2, typecheck e3) of
    (Just BoolTy, Just ty1, Just ty2)
      | ty1 == ty2 -> Just ty2
    _ -> Nothing
typecheck (App e1 e2) =
  case (typecheck e1, typecheck e2) of
    (Just (FunTy ty1 ty2), Just ty3)
      | ty1 == ty3 -> Just ty2
    _ -> Nothing
typecheck (Tag ty) = Just ty
typecheck (Recfun argty retty f) = -- f : Exp -> Exp -> Exp
  case typecheck (f (Tag (FunTy argty retty)) (Tag argty)) of
    Just ty
      | ty == retty -> Just (FunTy argty retty)
    _ -> Nothing

{-
   (recfun triang :: (Int -> Int) n =
      if n == 0 then
        0
      else
        n + triang(n-1)) 5
 -}

triangle =
  Recfun IntTy IntTy
    (\triang -> \n ->
      (If (Binop Eq n (Num 0))
          (Num 0)
          (Binop Add n (App triang (Binop Add n (Num (-1)))))))

{-
   (recfun triang :: (Int -> Int) n =
      if n == 0 then
        0
      else
        n + triang(n-1)) 5
   |->

   (if n == 0 then
        0
      else
        n + triang(n-1))[n:=5, triang := (recfun triang :: (Int -> Int) n =
                                            if n == 0 then
                                              0
                                            else
                                              n + triang(n-1))]
   =
   if 5 == 0 then
        0
      else
        5 + (recfun triang :: (Int -> Int) n =
             if n == 0 then
               0
             else
               n + triang(n-1))(5-1)

 -}