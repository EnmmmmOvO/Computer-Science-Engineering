module MinHS.TCMonad ( TypeError (..)
                     , TC
                     , freshNames
                     , runTC
                     , typeError
                     , fresh
                     ) where

import MinHS.Syntax
import Control.Applicative
import Control.Monad

data TypeError = TypeMismatch Type Type
               | OccursCheckFailed Id Type
               | NoSuchVariable Id
               | NoSuchConstructor Id
               | MalformedAlternatives
               | ForallInRecfun
               deriving (Show)

newtype TC a = TC ([Id] -> Either TypeError ([Id], a))

instance Monad TC where
  return x = TC (\s -> Right (s,x))
  (TC a) >>= f  = TC (\s -> case a s of Left x -> Left x
                                        Right (s',v) -> let TC b = f v
                                                         in b s')

instance Applicative TC where
  pure = return
  (<*>) = ap

instance Functor TC where
  fmap = ap . pure

freshNames :: [Id]
freshNames = map pure ['a'..'z'] ++ map ((++) "a" . show) [1..]

runTC :: TC a -> Either TypeError a
runTC (TC f) = fmap snd (f freshNames)

typeError :: TypeError -> TC a
typeError = TC . const . Left

fresh :: TC Type
fresh = TC $ \(x:xs) -> Right (xs,TypeVar x)
