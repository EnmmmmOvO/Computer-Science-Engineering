{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module MinHS.Env ( Env(..)
                 , empty
                 , lookup
                 , add
                 , addAll
                 ) where

import qualified Data.Map as M
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid
import Prelude hiding (lookup)
import Data.Semigroup

newtype Env e = Env (M.Map String e) deriving (Functor, Foldable, Traversable, Show, Eq, Monoid, Semigroup)

empty :: Env e
empty = Env M.empty

lookup :: Env e -> String -> Maybe e
lookup (Env env) var = M.lookup var env

add :: Env e -> (String, e) -> Env e
add (Env env) (key,elt) = Env (M.insert key elt env)

addAll :: Env e -> [(String,e)] -> Env e
addAll (Env env) pairs = Env $ foldr (\(k,e) g -> M.insert k e g) env pairs


