{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module MinHS.Parse where

import MinHS.Syntax

import Text.Parsec
import qualified Text.Parsec.Token as T
import qualified Text.Parsec.Language as L
import Text.Parsec.Expr
import Data.List (foldl1')
import Control.Applicative hiding ( (<|>), many )
import Data.List (sortBy)
import Data.Ord (comparing)

parseProgram = parse program

language = L.haskellStyle { T.reservedOpNames = [ "+","-","/","*","%"
                                                , "==","<=",">=","<",">","/="
                                                ,"::","->","\\","=>","="
                                                ]
                          , T.reservedNames   = [ "case","of","let","in","if","then","else"
                                                , "recfun","Int","Bool"
                                                , "letrec", "forall", "fst","snd"
                                                ]
                          , T.identStart      = letter <|> oneOf "_"
                          }

T.TokenParser {..} = T.makeTokenParser language

program = do whiteSpace; v <- many1 (bind <* semi); eof; return v

bind = Bind <$> varName
            <*> ((Just <$ reservedOp "::" <*> qtyp) <|> pure Nothing)
            <*> many varName <* reservedOp "=" <*> expr
            <?> "binding"

conName = constructor identifier <|> parens (constructor operator) <?> "constructor"
varName = variable identifier <|> parens (variable operator) <?> "variable"
constructor f =  lookAhead isConstructor *> f
variable    f =  isConstructor *> unexpected "Constructor tag where variable expected!"
             <|> f
isConstructor = pure <$> upper <|> string ":"

expr = buildExpressionParser [ [Prefix (reservedOp "-" >> return (App (Prim Neg))) ]
                             , [Infix (binApply <$> multDivRem) AssocLeft]
                             , [Infix (binApply <$> plusMinus)  AssocLeft]
                             , [Infix (binApply <$> comparison) AssocNone]
                             , [Infix (binApply <$> customOp) AssocNone]
                             ] (foldl1' App <$> many1 term) <?> "expression"
 where op s p = reservedOp s *> pure (Prim p)
       plusMinus  =  op "+" Add
                 <|> op "-" Sub
       multDivRem =  op "*" Mul
                 <|> op "/" Quot
                 <|> op "%" Rem
       comparison =  op ">=" Ge
                 <|> op "<=" Le
                 <|> op "<" Lt
                 <|> op ">" Gt
                 <|> op "==" Eq
                 <|> op "/=" Ne
       customOp = id <$ char '`' <*> conOrVar identifier <* char '`' <* whiteSpace
       conOrVar f =  Con         <$> constructor f
                 <|> Var         <$> f
       term =  If <$ reserved "if" <*> expr <* reserved "then" <*> expr <* reserved "else" <*> expr
           <|> Let    <$ reserved "let"    <*> many1 (bind <* semi) <* reserved "in" <*> expr
           <|> Recfun <$ reserved "recfun" <*> bind
           <|> Letrec <$ reserved "letrec" <*> many1 (bind <* semi) <* reserved "in" <*> expr
           <|> Case   <$ reserved "case" <*> expr <* reserved "of"
                      <*> (sortBy (comparing altTag) <$> many1 (alt <* semi))
           <|> try (parens (plusMinus
                        <|> multDivRem
                        <|> comparison
                        <|> conOrVar operator))
           <|> parens (tuples <$> expr `sepBy` comma)
           <|> Num <$> natural
           <|> Prim Fst <$ reserved "fst"
           <|> Prim Snd <$ reserved "snd"
           <|> conOrVar identifier
           <?> "term"
        where tuples [] = Con "()"
              tuples [a] = a
              tuples (x:xs) = binApply (Con "Pair") x (tuples xs)
              altTag (Alt t _ _) = t

alt = Alt <$> constructor identifier
          <*> manyTill identifier (reserved "->")
          <*> expr
          <?> "alternative"

qtyp =  Forall <$ reserved "forall" <*> identifier <* char '.' <* whiteSpace <*> qtyp
    <|> Ty <$> typ

typ = buildExpressionParser [ [Infix (reservedOp "+" *> pure Sum) AssocRight]
                            , [Infix (reservedOp "*" *> pure Prod) AssocRight]
                            , [Infix (reservedOp "->" *> pure Arrow) AssocRight]
                            ] term <?> "type"
  where term = parens (typ
                   <|> pure (Base Unit))
           <|> reserved "Bool" *> pure (Base Bool)
           <|> reserved "Int"  *> pure (Base Int)
           <|> (TypeVar <$> variable identifier)
