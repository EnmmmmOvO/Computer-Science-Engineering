module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Exception

type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           | Func VEnv [Char] [[Char]] Exp
           deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined -- should not ever be used

evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE E.empty e
evaluate bs = evalE E.empty (Let bs (Var "main"))

evalE :: VEnv -> Exp -> Value
evalE evl (Num n) = I n
evalE evl (Con "True") = B True
evalE evl (Con "False") = B False
evalE evl (Con "Nil") = Nil

evalE evl (If b e1 e2) = 
  case evalE evl b of 
    B True -> evalE evl e1
    B False -> evalE evl e2

evalE evl (App (Prim Neg) (Num n)) = I (-n)

evalE evl (App (App (Prim sy) e1) e2) =
  case (evalE evl e1, evalE evl e2) of 
    (Nil, _) -> Nil
    (_, Nil) -> Nil
    (I n1, I n2) -> case sy of 
      Add -> I (n1 + n2)
      Sub -> I (n1 - n2)
      Mul -> I (n1 * n2)
      Quot -> I (quot n1 n2)
      Eq -> B (n1 == n2)
      Ne -> B (n1 /= n2)
      Lt -> B (n1 < n2)
      Le -> B (n1 <= n2)
      Gt -> B (n1 > n2)
      Ge -> B (n1 >= n2)

evalE evl (App (App (Con "Cons") (Num e1)) e2) = Cons e1 (evalE evl e2)
evalE evl (App (Prim Null) (Con "Nil")) = B True
evalE evl (App (Prim Null) e) = B False

evalE evl (App (Prim Head) (App (Con "Cons") (Num n)))  = I n 
evalE evl (App (Prim Head) (App e1 e2)) = evalE evl (App (Prim Head) e1)
evalE evl (App (Prim Head) (Con "Nil"))  = error ("List is empty")

evalE evl (App (Prim Tail)(App (App (Con "Cons") (Num n)) (Con "Nil"))) = Cons n Nil
evalE evl (App (Prim Tail) (App (App (Con "Cons") (Num n)) e2)) = evalE evl (App (Prim Tail) e2)
evalE evl (App (Prim Tail) (Con "Nil"))  = error ("List is empty")

evalE evl (Let [] e) = evalE evl e
evalE evl (Let ((Bind s _ [] e1):xs) e2) = 
  let temp = E.add evl (s, (evalE evl e1)) in evalE temp (Let xs e2)
evalE evl (Let ((Bind f _ v e1):xs) e2) = 
  let temp = E.add evl (f, (Func evl f v e1)) in evalE temp (Let xs e2)

evalE evl (Var v) = 
  case E.lookup evl v of 
    Just (Func evl _ [] e) -> evalE evl e
    Just e -> e
    Nothing -> Nil

evalE evl e = error("Else situation")