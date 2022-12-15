<div id="content">
<h1 class="title">Tute (Week 5)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orge3e01e7">1. If</a></li>
<li><a href="#orgb41da1e">2. MinHS</a></li>
<li><a href="#org6290488">3. Abstract Machines</a></li>
</ul>
  </div></div></div>
<div id="outline-container-orge3e01e7" class="outline-2">
<h2 id="orge3e01e7"><span class="section-number-2">1</span> If</h2>
  <div class="outline-text-2" id="text-1"></div></div>

1. Most imperative programming languages do not make the $\mathbf{else}$ clause of an $\mathbf{if}$ statement mandatory. TinyImp only has the $\mathbf{if\ then\ else}$ form. How can a stand-alone $\mathbf{if}$ be encoded in TinyImp?

> > $$
> > [\![\mathbf{if}\;b\;\mathbf{then}\;e\;\mathbf{fi}]\!]\equiv\mathbf{if}\;b\;\mathbf{then}\;e\;\mathbf{else}\;\mathbf{skip}\;\mathbf{fi}
> > $$

2. Conversely, how can $\mathbf{if\ then\ else}$ be encoded using only stand-alone $\mathbf{if}$ in TinyImp?

> > In the following, we assume $x$ is a fresh variable, i.e.,one that doesn't occur free anywhere in $e_1, e_2$ or $b$. To see why we bother with $x$, consider what happens if the truth value of $b$ changes as a result of executing $e_1$.
> > $$
> > \begin{array}{l}   [\![ \mathbf{if}\;b\; \mathbf{then}\;e_1\;\mathbf{else}\;e_2\;\mathbf{fi} ]\!] \\   \equiv \\   \mathbf{var}\;x\;\cdot \\   x:=b; \\   \mathbf{if}\;x\;\mathbf{then}\\   \quad e_1\\   \mathbf{fi};\\   \mathbf{if}\;\neg\;x\;\mathbf{then}\\   \quad e_2 \\   \mathbf{fi}  \end{array}
> > $$
> > The negation operator here could simply be added to the expression language, or encoded with some extra juggling.

3. MinHS doesn't have stand-alone $\mathbf{if}$, a design decision shared by most functional rogramming languages. Unlike TinyImp, there's no sensible way of encoding it. Why is it difficult to encode, and why do you think the language has been designed this way?

> > The $\mathbf{if}$ in TinyImp is a statement and therefore has no value, only side-effects.  Hence there's a clear choice of what to do when the guard is false: nothing.  In MinHS, $\mathbf{if\ then\ else}$ is an expression, and wea would like expressions to have values. In the absence of an $\mathbf{else}$ branch, it's not clear what value we should assign to an expression whose guard is false.  
> >
> > If we really want to go ahead with this, we might consider the following choices.  First, we could say that $\mathbf{if}$ expressions whose guard are false have no value, and cause the program to diverge or abort.  Second, we could associate a "default" value to every type, and use this value as a fallback. There's nothing inherently wrong with either choice, but both seem to run against the programmer's intution that nothing should happen.

<div id="outline-container-orgb41da1e" class="outline-2">
<h2 id="orgb41da1e"><span class="section-number-2">2</span> MinHS</h2>
  <div class="outline-text-2" id="text-2"></div></div>
Consider the following Haskell implementation of an abstract syntax for MinHS.

```haskell
data type = 
  Bool
  | Int
  | FunTy Type Type -- Type -> Type
  deriving (Show,Eq)

data Expr =
  Num Int
  | Lit Bool
  | If Expr Expr Expr
  | Apply Expr Expr
  | Plus Expr Expr
  | Eq Expr Expr
  | Recfun Type Type (Expr -> Expr -> Expr)
  | Var String
```
Implement a <code>Value</code> type and an evaluator function for this language.

> ```haskell 
> data Val = IntV Int | BoolV Bool | FunV (Expr -> Expr -> Expr)
> eval :: Expr -> Val
> eval (Num n) = IntV n
> eval (Lit b) = BoolV b
> eval (Eq  a b) = let
>     IntV x = eval a
>     IntV y = eval b
>  in BoolV (x == y)
> eval (Plus a b) = let
>     IntV x = eval a
>     IntV y = eval b
>  in IntV (x + y)
> -- Similar for other cases..
> eval (If c t e) = let
>     BoolV b = eval c
>  in if b then eval t else eval e
> eval (Recfun _ _ f) = FunV f
> eval (Apply a b) = let
>     FunV f = eval a
>     arg    = eval b
>  in eval (f (uneval (FunV f)) (uneval>  arg))
> uneval :: Val -> Expr
> uneval (IntV v) = Num v
> uneval (BoolV b) = Lit b
> uneval (FunV f) = Recfun undefined undefined f
> -- Use of undefined above is safe, as this is only used while
> -- evaluating, where types are ignored anyway.
> ```

<div id="outline-container-org6290488" class="outline-2">
<h2 id="org6290488"><span class="section-number-2">3</span> Abstract Machines</h2>
  <div class="outline-text-2" id="text-3"></div></div>


Here is a big step semantics for a simple expression language, consisting of atomic terms $\mathbf{P}$, $\mathbf{A}$, $\mathbf{PP}$, $\mathbf{AP}$, $\mathbf{PPAP}$, and a single operator $+$.

The big step semantics are as follows:
$$
\dfrac{a \Downarrow \mathbf{AP} \quad b \Downarrow \mathbf{PP}}{a + b \Downarrow \mathbf{PPAP} }{\mathrm{Uh}_3}
$$
Translate this language to an equivalent small-step semantics where <i>all rules are axioms</i>. Use a stack, similarly to the C-Machine, in order to keep track of the current expression under evaluation.


> Assuming a stack much like the C-Machine and similar evaluation states, we have the following rules:
> 1. $s \succ \mathbf{P} \mapsto s \prec \mathbf{P}$
> 2. $s \succ \mathbf{A} \mapsto s \prec \mathbf{A}$
> 3. $s \succ (a + b) \mapsto (\square + b) \triangleright s \succ a$
> 4. $(\square + b) \triangleright s \prec \mathbf{P} \mapsto (\mathbf{P} + \square) \triangleright s \succ b$
> 5. $(\square + b) \triangleright s \prec \mathbf{AP} \mapsto (\mathbf{AP} + \square) \triangleright s \succ b$
> 5. $(\mathbf{P} + \square) \triangleright s \prec \mathbf{A} \mapsto s \prec \mathbf{AP}$
> 6. $(\mathbf{P} + \square) \triangleright s \prec \mathbf{P} \mapsto s \prec \mathbf{PP}$
> 7. $(\mathbf{AP} + \square) \triangleright s \prec \mathbf{PP} \mapsto s \prec \mathbf{PPAP}$

