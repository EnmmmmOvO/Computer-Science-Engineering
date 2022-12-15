module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)

unify :: Type -> Type -> TC Subst
unify (TypeVar x) (TypeVar y) =  return (if x == y then emptySubst else x =: TypeVar y)
   
unify (Base x) (Base y) = if x == y then return emptySubst else typeError (TypeMismatch (Base x) (Base y))

unify (Prod l1 r1) (Prod l2 r2) = do 
  _T1 <- unify l1 l2
  _T2 <- unify (substitute _T1 r1) (substitute _T1 r2)
  return (_T1 <> _T2)
  
unify (Sum l1 r1) (Sum l2 r2) = do 
  _T1 <- unify l1 l2
  _T2 <- unify (substitute _T1 r1) (substitute _T1 r2)
  return (_T1 <> _T2)
  
unify (Arrow l1 r1) (Arrow l2 r2) = do 
  _T1 <- unify l1 l2
  _T2 <- unify (substitute _T1 r1) (substitute _T1 r2)
  return (_T1 <> _T2)

unify (TypeVar x) y = 
    if x `notElem` tv y then
        return (x =: y)
    else
        typeError (OccursCheckFailed x y)
unify y (TypeVar x) = unify (TypeVar x) y
unify x y = typeError (TypeMismatch x y)

generalise :: Gamma -> Type -> QType
generalise g t = foldr f init lst
    where f a b = Forall a b
          init  = Ty t
          lst   = tv t \\ tvGamma g

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = do
    let Bind name _ _ body = head bs 
    (exp, tau, subst) <- inferExp env body
    let retype = substitute subst tau
    let refill = allTypes (substQType subst) exp
    let tt = generalise (substGamma subst env) retype
    return ([Bind name (Just tt) [] refill], retype, subst)

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives
inferExp g (Num x) = return (Num x, Base Int, emptySubst)
inferExp g (Prim x) = unquantify (primOpType x) >>= \v -> return (Prim x, v, emptySubst)
inferExp g (Con x) = 
    case constType x of
        Nothing -> typeError (NoSuchConstructor x)
        Just tt -> unquantify tt >>= \v -> return (Con x, v, emptySubst)
inferExp g (Var x) = 
    case E.lookup g x of
        Nothing -> typeError (NoSuchVariable x)
        Just tt -> unquantify tt >>= \v -> return (Var x, v, emptySubst)


inferExp g (App e1 e2) = do
      alpha  <- fresh
      (_, tau1, t) <- inferExp g e1
      (_, tau2, t') <- inferExp (substGamma t g) e2
      u <- unify (substitute t' tau1) (Arrow tau2 alpha)
      return (App e1 e2, 
             substitute u alpha,  
             u <> t' <> t)
    
inferExp g (If e e1 e2) = do
      (_, tau, t) <- inferExp g e
      u <- unify tau (Base Bool)
      let w = substitute (u <> t) tau
      if w /= Base Bool then
         typeError (TypeMismatch (Base Bool) w)
      else do
          (_, tau1, t1) <- inferExp (substGamma (u <> t) g) e1
          (_, tau2, t2) <- inferExp (substGamma (t1 <> u <> t) g) e2
          u' <- unify (substitute t2 tau1) tau2
          return (If e e1 e2, substitute u' tau2, u' <> t2 <> t1 <> u <> t)
          
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
      (_, tau, t) <- inferExp g e
      alfl <- fresh
      alfr <- fresh
      (_, taul, t1) <- inferExp (substGamma t $ E.add g (x, Ty alfl)) e1
      (_, taur, t2) <- inferExp (substGamma (t1 <> t) $ E.add g (y, Ty alfr)) e2  
      u <- unify (substitute (t2 <> t1 <> t) $ Sum alfl alfr)
                  (substitute (t2 <> t1) tau)
      u' <- unify (substitute (u <> t2) taul)
                  (substitute (u) taur)
      return (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2], 
               substitute (u' <> u) $ taur,
               u' <> u <> t2 <> t1 <> t)
    
inferExp g (Case e _) = typeError MalformedAlternatives
  
inferExp g (Recfun (Bind f a [x] e)) = do
  alf1 <- fresh
  alf2 <- fresh
  let gg = E.add g (x, Ty alf1)
  let ggg = E.add gg (f, Ty alf2)
  (_, tau, t) <- inferExp ggg e
  u <- unify (substitute t alf2) (Arrow (substitute t alf1) tau)
  return (Recfun (Bind f a [x] e), 
      substitute u (Arrow (substitute t alf1) tau),
      u <> t)

inferExp g (Let [Bind x a [] e1] e2) = do
  (_, tau, t) <- inferExp g e1
  let gg = substGamma t g
  let ggg = E.add gg (x, generalise gg tau)
  (_, tau', t') <- inferExp ggg e2
  return (Let [Bind x a [] e1] e2,
          tau',
          t' <> t)
  
  
          