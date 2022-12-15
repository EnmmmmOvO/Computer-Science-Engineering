{-# LANGUAGE FlexibleContexts #-}
module MinHS.Pretty where
import MinHS.Syntax
import MinHS.TCMonad

import Text.PrettyPrint.ANSI.Leijen as P

primop = dullyellow . string
keyword = bold . string
datacon = dullgreen . string
typecon = blue . string
numeric = dullcyan . integer
symbol = magenta . string
err = red . string

instance Pretty Bind where
  pretty (Bind n ty ps exp) = string n <+> symbol "::" <+> pretty ty
                                       <+> params (symbol "=" <+> pretty exp)
      where params = if null ps then id else (hsep (map string ps) <+>)
  prettyList = vcat . map (<> semi) . map pretty


instance Pretty Type where
  pretty = prettyType'
    where
      prettyType (a `Arrow` b) = prettyType' a <+> symbol "->" <+> prettyType b
      prettyType (a `Prod` b) = prettyType' a <+> symbol "*" <+> prettyType b
      prettyType (a `Sum` b) = prettyType' a <+> symbol "+" <+> prettyType b
      prettyType (Base Unit) = typecon "()"
      prettyType (Base x)    = typecon $ show x
      prettyType (TypeVar x) = string x
      prettyType' t@(a `Arrow` b) = parens (prettyType t)
      prettyType' t@(a `Prod` b) = parens (prettyType t)
      prettyType' t@(a `Sum` b) = parens (prettyType t)
      prettyType' t = prettyType t

instance Pretty Op where
  pretty Add  = primop "+"
  pretty Sub  = primop "-"
  pretty Mul  = primop "*"
  pretty Quot = primop "/"
  pretty Rem  = primop "%"
  pretty Neg  = primop "-"
  pretty Gt   = primop ">"
  pretty Ge   = primop ">="
  pretty Lt   = primop "<"
  pretty Le   = primop "<="
  pretty Eq   = primop "=="
  pretty Ne   = primop "/="
  pretty Fst = primop "fst"
  pretty Snd = primop "snd"

instance Pretty QType where
  pretty (Ty t) = pretty t
  pretty (Forall x t) = keyword "forall" <+> string x <> char '.' <+> pretty t

instance Pretty Exp where
  pretty (Var i) = string i
  pretty (App (App (Con "Pair") e1) e2) = parens (pretty e1 <> string "," <+> pretty e2)
  pretty (App (Prim Neg) e2) = parens (string "-" <+> pretty' e2)
  pretty (Prim Fst) = string "fst"
  pretty (Prim Snd) = string "snd"
  pretty (Prim o) = parens (pretty o)
  pretty (Con i) = datacon i
  pretty (Num i) = numeric i
  pretty (App e1 e2) = pretty e1 <+> pretty' e2
  pretty (If c t e) =  keyword "if"
                   <+> align (pretty c
                            P.<$> keyword "then" <+> pretty t
                            P.<$> keyword "else" <+> pretty e)
  pretty (Let bs e)  = align (keyword "let" <+> align (pretty bs) P.<$> keyword "in" <+> pretty e)
  pretty (Recfun b)  = parens (keyword "recfun" <+> pretty b)
  pretty (Letrec bs e) = align (keyword "letrec" <+> align (pretty bs) P.<$> keyword "in" <+> pretty e)
  pretty (Case s alts) = parens (keyword "case" <+> pretty s <+> keyword "of" <+> (align $ vcat $ map pretty alts))

instance Pretty Alt where
  pretty (Alt t xs e) = datacon t <+> (hsep (map string xs)) <+> symbol "->" <+> pretty e <> semi

pretty' t@(App _ _) = parens (pretty t)
pretty' t           = pretty t

instance Pretty TypeError where
   pretty (TypeMismatch t1 t2) =  err "Type mismatch:"
                              P.<$> indent 3 (pretty t1)
                              P.<$> err "is not"
                              P.<$> indent 3 (pretty t2)
   pretty (NoSuchVariable x) =  err "Variable"
                            <+> string x
                            <+> err "not in scope."
   pretty (NoSuchConstructor x) =  err "Constructor"
                               <+> string x
                               <+> err "not in scope."
   pretty (OccursCheckFailed x t) = err "Variable" <+> string x <+> err "cannot occur in the type" <+> pretty t <+> err "(occurs check)"
   pretty (MalformedAlternatives) = err "Alternatives must be for sum types, and include cases for both Inl and Inr"
   pretty (ForallInRecfun)        = err "Quantified type cannot occur in Recfun"
