import Data.Char
-- Algebraic datatype spec
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