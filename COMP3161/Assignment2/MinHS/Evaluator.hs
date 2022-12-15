module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type VEnv = E.Env Value

data Value = I Integer
           | F VEnv [Id] Exp
           | P Op [Value]
           | C Id [Value]
           deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (P o []) | o `elem` [Fst , Snd ] = PP.pretty o
                  | otherwise             = PP.parens (PP.pretty o)
  pretty (P Fst vs) = PP.parens (primop "fst" PP.<+> PP.hsep (map PP.pretty vs))
  pretty (P Snd vs) = PP.parens (primop "snd" PP.<+> PP.hsep (map PP.pretty vs))
  pretty (P o vs) = PP.parens (PP.parens (PP.pretty o) PP.<+> PP.hsep (map PP.pretty vs))
  pretty (C c []) = datacon c
  pretty (C c vs) = PP.parens (datacon c PP.<+> PP.hsep (map PP.pretty vs))
  pretty (F g ps x) = PP.red (PP.string "<<") PP.<> PP.hsep (map PP.string ps) PP.<> PP.string "."
                             PP.<+> PP.pretty x PP.<+> PP.red (PP.string ">>")

evaluate :: Program -> Value
evaluate bs = evalE E.empty (Let bs (Var "main"))

evalB :: VEnv -> Bind -> Value
evalB e (Bind n t ps x) = evalF (F e ps x)

bindName (Bind n _ _ _) = n

evalF :: Value -> Value
evalF (F e [] x) = evalE e x
evalF x          = x

evalE :: VEnv -> Exp -> Value
evalE e (Var i) | Just v <- E.lookup e i = v
evalE e (Num i)        = I i
evalE e (Con x)        = C x []
evalE e (Prim o)       = P o []
evalE e (If c t f)     = case evalE e c of
                           C "True"  [] -> evalE e t
                           C "False" [] -> evalE e f
evalE e (Let (b:bs) x) = evalE (e `E.add` (bindName b, evalB e b)) (Let bs x)
evalE e (Let [] x)     = evalE e x
evalE e (Case x alts)  = tryAlts (evalE e x) alts
   where tryAlts (C c as) (Alt t ps y :_) | c == t = evalE (E.addAll e (zip ps as)) y
         tryAlts v (x:xs) = tryAlts v xs
         tryAlts v [] = error "Pattern match failure"

evalE e (Recfun b)     = let v = evalB (e `E.add` (bindName b, v)) b
                          in v
evalE e (Letrec bs x)  = let g = e `E.addAll` map (\x -> (bindName x, evalB g x)) bs
                          in evalE g x
evalE e (App a b)      = case evalE e a of
                           P o v    -> evalOp o (v ++ [evalE e b])
                           C c v    -> C c (v ++ [evalE e b])
                           v@(F {}) -> applyF v (evalE e b)
  where applyF :: Value -> Value -> Value
        applyF (F g (x:xs) e) v = evalF $ F (g `E.add` (x,v)) xs e


evalOp :: Op -> [Value] -> Value
evalOp Neg  [I x    ] = I $ (-x)
evalOp Add  [I x,I y] = I $ x + y
evalOp Sub  [I x,I y] = I $ x - y
evalOp Mul  [I x,I y] = I $ x * y
evalOp Quot [I x,I 0] = error "divide by zero"
evalOp Rem  [I x,I 0] = error "divide by zero"
evalOp Quot [I x,I y] = I $ x `div` y
evalOp Rem  [I x,I y] = I $ x `rem` y
evalOp Gt   [I x,I y] = flip C [] . show $ x >  y
evalOp Ge   [I x,I y] = flip C [] . show $ x >= y
evalOp Lt   [I x,I y] = flip C [] . show $ x <  y
evalOp Le   [I x,I y] = flip C [] . show $ x <= y
evalOp Eq   [I x,I y] = flip C [] . show $ x == y
evalOp Ne   [I x,I y] = flip C [] . show $ x /= y
evalOp Fst  [C "Pair" [a,b]] = a
evalOp Snd  [C "Pair" [a,b]] = b
evalOp s x = P s x
