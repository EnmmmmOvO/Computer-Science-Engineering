module MinHS.Subst ( Subst
                   , substitute
                   , substQType
                   , substGamma
                   , emptySubst
                   , (=:)
                   ) where

import MinHS.Syntax
import Data.Monoid hiding (Sum, (<>))
import MinHS.Env hiding (lookup)
import Data.Semigroup (Semigroup ((<>)))
newtype Subst = Subst [(Id, Type)]

instance Semigroup Subst where 
  Subst a <> Subst b = Subst $ map (fmap $ substitute $ Subst b) a
                            ++ map (fmap $ substitute $ Subst a) b
  
instance Monoid Subst where
  mempty = Subst []
  mappend = (<>)

substitute :: Subst -> Type -> Type
substitute s (Base c   ) = Base  c
substitute s (Sum a b  ) = Sum   (substitute s a) (substitute s b)
substitute s (Prod a b ) = Prod  (substitute s a) (substitute s b)
substitute s (Arrow a b) = Arrow (substitute s a) (substitute s b)
substitute (Subst s) (TypeVar x) | Just t <- lookup x s = t
                                 | otherwise            = TypeVar x

substQType :: Subst -> QType -> QType
substQType s (Ty t) = Ty (substitute s t)
substQType s (Forall x t) = Forall x (substQType (remove x s) t)
  where remove x (Subst s) = Subst $ filter ((/= x) . fst) s

substGamma :: Subst -> Env QType -> Env QType
substGamma = fmap . substQType

emptySubst :: Subst
emptySubst = mempty

(=:) :: Id -> Type -> Subst
a =: b = Subst [(a,b)]
