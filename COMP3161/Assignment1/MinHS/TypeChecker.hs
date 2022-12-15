{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}
module MinHS.TypeChecker where

import qualified MinHS.Env as E
import MinHS.Syntax

import Control.Applicative
import Control.Monad (void, unless)
import Control.Monad.Fail

type Gamma = E.Env Type

primOpType :: Op -> Type
primOpType Head = TypeApp (TypeCon List) (TypeCon Int) `Arrow` TypeCon Int
primOpType Null = TypeApp (TypeCon List) (TypeCon Int) `Arrow` TypeCon Bool
primOpType Tail = TypeApp (TypeCon List) (TypeCon Int) `Arrow` TypeApp (TypeCon List) (TypeCon Int)
primOpType Gt   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Ge   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Lt   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Le   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Eq   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Ne   = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Bool)
primOpType Neg  = TypeCon Int `Arrow` TypeCon Int
primOpType _    = TypeCon Int `Arrow` (TypeCon Int `Arrow` TypeCon Int)

constructorType :: Id -> Maybe Type
constructorType "Cons"
   = Just $ TypeCon Int
    `Arrow` (TypeApp (TypeCon List) (TypeCon Int)
    `Arrow` TypeApp (TypeCon List) (TypeCon Int))
constructorType "Nil"   = Just $ TypeApp (TypeCon List) (TypeCon Int)
constructorType "True"  = Just $ TypeCon Bool
constructorType "False" = Just $ TypeCon Bool
constructorType _       = Nothing

tyConKind :: TyCon -> Kind
tyConKind List = Star :=> Star
tyConKind _    = Star

initialGamma :: Gamma
initialGamma = E.empty

data TypeError = TypeMismatch Type Type Exp
               | TypeShouldBeFunction Type Bind
               | FunctionTypeExpected Exp Type
               | NoSuchVariable Id
               | NoSuchConstructor Id
               | TypeConstructorSaturated Type Kind
               | KindMismatch Kind Kind Type
               deriving (Show)

newtype TC a = TC (Either TypeError a) deriving (Monad, Functor, Applicative)

instance MonadFail TC where
   fail = error 
 
data Kind = Star
          | (:=>) Kind Kind
          deriving (Show, Eq)

runTC :: TC () -> Maybe TypeError
runTC (TC (Left err)) = Just err
runTC (TC (Right ())) = Nothing

typeError :: TypeError -> TC a
typeError = TC . Left

typecheck :: Program -> Maybe TypeError
typecheck = runTC . void . checkBinds initialGamma

checkBinds :: Gamma -> Program -> TC Gamma
checkBinds g (b:bs) = (E.add g <$> checkBind g b) >>= flip checkBinds bs
checkBinds g []     = return g

checkBinds' :: Gamma -> Program -> TC ()
checkBinds' g (b:bs) = checkBind g b >> checkBinds' g bs
checkBinds' g []     = return ()

checkBind :: Gamma -> Bind -> TC (Id, Type)
checkBind g b@(Bind n ty args exp) = do ty `ofKind` Star
                                        checkAbs g b
                                        return (n,ty)

checkAbs :: Gamma -> Bind -> TC ()
checkAbs g   (Bind n (Arrow a b) (x:xs) exp) = checkAbs (g `E.add` (x,a)) (Bind n b xs exp)
checkAbs g b@(Bind n ty          (x:xs) _  ) = typeError $ TypeShouldBeFunction ty b
checkAbs g   (Bind n ty          []     exp) = shouldCheck g exp ty

shouldCheck :: Gamma -> Exp -> Type -> TC ()
shouldCheck g exp t
  = do t' <- checkExp g exp
       unless (t' == t) $ typeError $ TypeMismatch t t' exp

typeWellformed :: Type -> TC Kind
typeWellformed (TypeCon c) = return $ tyConKind c
typeWellformed (Arrow a b) = (a `ofKind` Star) >> (b `ofKind` Star) >> return Star
typeWellformed (TypeApp a b)
  = do kb :=> kr <- expectArrowKind typeWellformed a
       b `ofKind` kb
       return kr
  where expectArrowKind a t
          = do x <- a t
               case x of
                 a :=> b -> return x
                 _       -> typeError $ TypeConstructorSaturated t x
ofKind t k = do k' <- typeWellformed t
                unless (k == k') $ typeError $ KindMismatch k k' t


checkExp :: Gamma -> Exp -> TC Type
checkExp g (Var i)  | Just t <- E.lookup g i = return t
                    | otherwise              = typeError $ NoSuchVariable i
checkExp g (Con c)  | Just t <- constructorType c = return t
                    | otherwise                   = typeError $ NoSuchConstructor c
checkExp g (Prim c) | t <- primOpType c = return t
checkExp g (Num _) = return $ TypeCon Int
checkExp g (App e1 e2)
  = do a `Arrow` b <- expectFunctionType (checkExp g) e1
       shouldCheck g e2 a
       return b
  where expectFunctionType :: (Exp -> TC Type) -> (Exp -> TC Type)
        expectFunctionType a e
          = do x <- a e
               case x of
                 a `Arrow` b -> return x
                 _           -> typeError $ FunctionTypeExpected e x
checkExp g (If c t e)
  = do shouldCheck g c (TypeCon Bool)
       t1 <- checkExp g t
       shouldCheck g e t1
       return t1
checkExp g (Let bs e) = checkBinds g bs >>= flip checkExp e
checkExp g (Recfun b@(Bind n ty ps e))
  = do typeWellformed ty
       checkAbs (g `E.add` (n, ty)) b
       return ty
checkExp g (Letrec bs e)
  = do bs' <- mapM (\(Bind n ty _ _) -> typeWellformed ty >> return (n,ty)) bs
       let g' = g `E.addAll` bs'
       checkBinds' g' bs
       checkExp g' e


