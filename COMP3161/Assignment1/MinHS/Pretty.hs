module MinHS.Pretty where
import MinHS.Syntax
import MinHS.TypeChecker

import Text.PrettyPrint.ANSI.Leijen as L

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
      prettyType (TypeApp (TypeCon List) b) = blue (brackets (prettyType b))
      prettyType (TypeApp a b) = prettyType a <+> prettyType'' b
      prettyType (TypeCon Unit) = typecon "()"
      prettyType (TypeCon x)    = typecon $ show x
      prettyType' t@(a `Arrow` b) = parens (prettyType t)
      prettyType' t = prettyType t
      prettyType'' t@(TypeApp a b) = parens (prettyType' t)
      prettyType'' t = prettyType' t

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
  pretty Head = primop "head"
  pretty Null = primop "null"
  pretty Tail = primop "tail"

instance Pretty Exp where
  pretty (Var i) = string i
  pretty (App (Prim Neg) e2) = parens (string "-" <+> pretty' e2)
  pretty (Prim Head) = string "head"
  pretty (Prim Tail) = string "tail"
  pretty (Prim o) = parens (pretty o)
  pretty (Con i) = datacon i
  pretty (Num i) = numeric i
  pretty (App e1 e2) = pretty e1 <+> pretty' e2
  pretty (If c t e) =  keyword "if"
                   <+> align (pretty c
                            L.<$> keyword "then" <+> pretty t
                            L.<$> keyword "else" <+> pretty e)
  pretty (Let bs e)  = align (keyword "let" <+> align (pretty bs) L.<$> keyword "in" <+> pretty e)
  pretty (Recfun b)  = parens (keyword "recfun" <+> pretty b)
  pretty (Letrec bs e) = align (keyword "letrec" <+> align (pretty bs) L.<$> keyword "in" <+> pretty e)

pretty' t@(App _ _) = parens (pretty t)
pretty' t           = pretty t

instance Pretty TypeError where
   pretty (TypeMismatch t1 t2 e) =  err "Type mismatch:"
                                L.<$> indent 3 (pretty t1)
                                L.<$> err "is not"
                                L.<$> indent 3 (pretty t2)
                                L.<$> err "in expression"
                                L.<$> indent 3 (pretty e)
   pretty (TypeShouldBeFunction ty b) =  err "Parameter list suggests this atomic type"
                                     L.<$> indent 3 (pretty ty)
                                     L.<$> err "to be a function, in binding:"
                                     L.<$> indent 3 (pretty b)
   pretty (FunctionTypeExpected e t) =  err "Function application must be performed on a function, but this:"
                                    L.<$> indent 3 (pretty e)
                                    L.<$> err "is of type"
                                    <+> pretty t
   pretty (NoSuchVariable x) =  err "Variable"
                            <+> string x
                            <+> err "not in scope."
   pretty (NoSuchConstructor x) =  err "Constructor"
                               <+> string x
                               <+> err "not in scope."
   pretty (TypeConstructorSaturated t k) =  err "Expected"
                                        <+> pretty t
                                        <+> err "to be a type constructor, but it is an atomic type."
   pretty (KindMismatch k1 k2 t) =  err "Type term"
                                <+> pretty t
                                <+> err "is not valid."
