-- Induction: for defining data types
-- Recursion: for defining functions

import Data.Char
-- Algebraic (aka inductive) datatype spec
data Token =
  -- IdentT is a *data constructor*
  IdentT String
  | LitT Int
  | LParenT 
  | RParenT
  | LBraceT
  | RBraceT
  | SemiT
  | GreaterT
  | MinusT
  | IfT
  | ReturnT
  | AssignT
  deriving Show

-- ["hello","hi"]
-- is syntactic sugar for
---"hello":"hi":[]
-- Lists is also an algebraic
-- datatype
-- [] :: [a]
-- (:) :: a -> [a] -> [a]

-- String is a type synonym
-- for [Char]

-- the type of lexer is
-- String -> [Token]
lexer :: String -> [Token]
lexer "" = []
lexer ('>':cs) = GreaterT:lexer cs
lexer ('=':cs) = AssignT:lexer cs
lexer ('-':cs) = MinusT:lexer cs
lexer ('(':cs) = LParenT:lexer cs
lexer (')':cs) = RParenT:lexer cs
lexer ('{':cs) = LBraceT:lexer cs
lexer ('}':cs) = RBraceT:lexer cs
lexer (';':cs) = SemiT:lexer cs
lexer (c:cs) =
  if isAlpha c then
    let (name,rest) = span isAlphaNum (c:cs)
    in
        if name == "return" then
          ReturnT:lexer rest
        else if name == "if" then
          IfT:lexer rest
        else
          IdentT name:lexer rest
  else if isSpace c then
    lexer cs
  else if isDigit c then
    let (number,rest) = span isDigit (c:cs)
    in
      LitT(read number):lexer rest
  else
    error "haven't written yet"


sumTo :: Int -> Int
sumTo 0 = 0
sumTo n = n + sumTo(n-1)

-- Q: Where did we mention n should not be 0?
-- A: Nowhere. Haskell process clauses of a definition
--    top-down.


data Nat = Z | S Nat
         deriving Show

add :: Nat -> Nat -> Nat
add Z n = n
add (S n) m = S(add n m)


mylength :: [a] -> Int
mylength [] = 0
mylength (x:xs) = 1 + mylength xs

mytake :: Int -> [a] -> [a]
mytake 0 xs = []
mytake n [] = []
mytake n (x:xs) = x:mytake (n-1) xs

mydrop :: Int -> [a] -> [a]
mydrop 0 xs = xs
mydrop n [] = []
mydrop n (x:xs) = mydrop (n-1) xs

myappend :: [a] -> [a] -> [a]
myappend [] ys = ys
myappend (x:xs) ys = x : myappend xs ys


data Tree a =
  Leaf
  | Branch a (Tree a) (Tree a)

leaves :: Tree a -> Int
leaves Leaf = 1
leaves (Branch x l r) = leaves l + leaves r

height :: Tree a -> Int
height Leaf = 0
height (Branch x l r) = 1 + max (height l) (height r)


data Forest a = Empty | Cons (Rose a) (Forest a)

data Rose a = Node a (Forest a)

size :: Rose a -> Int
size (Node x f) = 1 + size_f f

size_f :: Forest a -> Int
size_f Empty = 0
size_f (Cons r f) = size r + size_f f