<div id="content">
<h1 class="title">Tute (Week 2)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orgd0cbd45">1. Inductive Types</a></li>
<li><a href="#org5794677">2. Red Black Trees</a></li>
<li><a href="#org0b808f4">3. Ambiguity and Syntax</a></li>
<li><a href="#org9dd87ec">4. Simultaneous Induction</a></li>
</ul>
</div>
  </div>
</div>
<div id="outline-container-orgd0cbd45" class="outline-2">
<h2 id="orgd0cbd45"><span class="section-number-2">1</span> Inductive Types</h2>
<div class="outline-text-2" id="text-1">
  </div></div>


Consider the <code>(++)</code> operator in Haskell.


```haskell
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
```

1. State the formal properties of <i>left identity</i>, <i>right identity</i> and <i>associativity</i> for <code>(++)</code>.
> > ```haskell
> > [] ++ ys == ys -- left identity
> > xs ++ [] == xs -- right identity
> > (xs ++ (ys ++ zs)) == ((xs ++ ys) ++ zs) -- associativity
> > ```
2. Try to prove these properties. In some cases, you may need to perform induction on the structure of lists. The <b>base case</b> of the induction will be for the empty list, and the <b>inductive case</b> will be to show your property for a list <code>(x:xs)</code>, assuming the property for the list <code>xs</code> (this assumption is called the <i>inductive hypothesis</i>).

> > Proving left identity is a trivial consequence of the first defining equation of <code>(++)</code>.  
> >
> > For right identity, we want to prove <code>xs ++ [] == xs</code> for all <code>xs</code>.  
> >
> > <b>Base case</b>: <code>xs == []</code>, we must show <code>[] ++ [] == []</code>, which follows from the first defining equation.
> >
> > <b>Inductive case</b>: <code>xs == (x:xs')</code>, assuming the inductive hypothesis that:
> >
> > ```haskell
> > xs' ++ [] == xs'
> > ```
> > We must show that:
> > ```haskell
> > (x:xs') ++ [] == (x:xs')
> > ```
> > By equational reasoning:
> > ```haskell
> > LHS == (x:xs') ++ [] 
> >  == x:(xs' ++ []) -- Equation 2
> >  == (x:xs')       -- Inductive Hypothesis
> >  == RHS
> > ```
> > Thus right identity is proven by induction on lists.
> >
> > For associativity, we want to prove <code>(xs ++ ys) ++ zs == xs ++ (ys ++ zs)</code> for all <code>xs</code>, <code>ys</code> and <code>zs</code>. By induction on <code>xs</code>: 
> >
> > <b>Base case</b>: <code>xs == []</code>, we must show <code>([] ++ ys) ++ zs == [] ++ (ys ++ zs)</code>. Simplifying with the first defining equation, both sides become <code>ys ++ zs</code>.  
> >
> > <b>Inductive case</b>: <code>xs == (x:xs')</code>. Assuming the inductive hypothesis that:
> >
> > ```haskell
> > (xs' ++ ys) ++ zs == xs' ++ (ys ++ zs)
> > ```
> >
> > We must show that:
> >
> > ```haskell
> > ((x:xs') ++ ys) ++ zs == (x:xs') ++ (ys ++ zs)
> > ```
> >
> > By equational reasoning:
> >
> > ```haskell
> > LHS == ((x:xs') ++ ys) ++ zs 
> >     == (x:(xs' ++ ys)) ++ zs -- Equation 2
> >     == x:((xs' ++ ys) ++ zs) -- Equation 2
> >     == x:(xs' ++ (ys ++ zs)) -- Inductive Hypothesis
> >     == (x:xs') ++ (ys ++ zs) -- Equation 2 (symmetrically)
> >     == RHS
> > ```
> >
> > Thus associativity is proven by induction on lists.

<div id="outline-container-org5794677" class="outline-2">
<h2 id="org5794677"><span class="section-number-2">2</span> Red Black Trees</h2>
<div class="outline-text-2" id="text-2">
  </div></div>
Red-black trees are binary search trees where each node in the tree is coloured either red or black. In C, red-black trees could, for example, be encoded with the following user-defined data type:

```haskell
typedef struct redBlackNode* link;

struct redBlackNode { 
  Item item; // Item type defined elsewhere
  link left, right; 
  int  isRed; // 1 if node is red, 0 if black
};
```

and in Haskell (again, we assume the `Item` type is defined elsewhere)

```haskell
data RBColour
  = Red
  | Black

data RBTree
  = RBLeaf
  | RBNode RBColour Item RBTree RBTree 
```

1. The user defined Haskell data type characterises a set of terms as `RBTree`. List the inference rules to define the same set. Assume there already exists a judgement $x\ \mathbf{Item}$ which is derivable for all $x$ in the `Item` type.

> > $$
> > \dfrac{ }{\mathit{Red}\ \mathbf{RBColour}} \quad \dfrac{ }{\mathit{Black}\ \mathbf{RBColour}}
> > $$
> >
> > $$
> > \dfrac{ }{\mathit{RBLeaf}\ \mathbf{RBTree}} \quad \dfrac{c\ \mathbf{RBColour}\quad x\ \mathbf{Item}\quad t_1\ \mathbf{RBTree}\quad t_2\ \mathbf{RBTree}}{(\mathit{RBNode}\ c\ x\ t_1\ t_2)\ \mathbf{RBTree}}
> > $$

2. In a proper red-black tree, we can never have a red parent node with a red child, although it is possible to have black nodes with black children. Moreover, the root node cannot be red. Therefore, not all terms of type `RBTree` are real red-black trees. Define inference rules for a property $t\ \mathbf{OK}$, such that $\mathbf{OK}$ is derivable if the term $t$ represents a proper red-black tree.

> > We define this using an additional property $\mathbf{OK}^R$. $\mathbf{OK}$ is a red-black tree with a black root node or a leaf, whereas , $\mathbf{OK}^R$ trees can also have red root nodes. If a node has a red root node, both children have to have black root nodes. 
> > $$
> > \dfrac{ }{\mathit{RBLeaf}\ \mathbf{OK}}\quad\dfrac{t_1\ \mathbf{OK}^R\quad t_2\ \mathbf{OK}^R }{ (\mathit{RBNode}\ \mathit{Black}\ x\ t_1\ t_2)\ \mathbf{OK}}
> > $$
> >
> > $$
> > \dfrac{t_1\ \mathbf{OK}\quad t_2\ \mathbf{OK} }{ (\mathit{RBNode}\ \mathit{Red}\ x\ t_1\ t_2)\ \mathbf{OK}^R}\quad
> > \dfrac{n\ \mathbf{OK}}{n\ \mathbf{OK}^R}
> > $$

<div id="outline-container-org0b808f4" class="outline-2">
<h2 id="org0b808f4"><span class="section-number-2">3</span> Ambiguity and Syntax</h2>
<div class="outline-text-2" id="text-3">
  </div></div>

Consider the language of *boolean expressions* (with operators: $\land$ (and), $\lor$ (or), $\neg$ (not), constant values $\mathit{True}$ and $\mathit{False}$, and parentheses).


1. Give a simple (non-simultaneous) inductive definition for this language using only judgements of the form $e\  \mathbf{Bool}$.

> > $$
> > \dfrac{e_1\ \mathbf{Bool}\quad e_2\ \mathbf{Bool}}{e_1 \lor e_2\ \mathbf{Bool}}
> > \quad
> > \dfrac{e_1\ \mathbf{Bool}\quad e_2\ \mathbf{Bool}}{e_1 \land e_2\ \mathbf{Bool}}
> > $$

2. Identify how this language is *ambiguous*: That is, find an expression that can be parsed in multiple ways.

> > $\bot \land \top \lor \bot$ can be interpreted in multiple ways with different semantic results.

3. Now, give a second definition for the same language which is not ambiguous. (to disambiguate: $\neg$ has the highest precedence; $\land$ has a higher precedence than $\lor$, both are left associative).

> > Separate the judgment $\textbf{Bool}$ into the 3 simultaneous judgments $\mathbf{AndEx,\ OrEx\ \text{and}\ Atom}$ such that $\textbf{Atom} \subset \textbf{AndEx} \subset \textbf{OrEx}$ This makes terms of highest precedence (constants, parenthesised or negated expressions) the tightest class of boolean expressions, followed by those additionally involving $\land$ on the outer level, and finally those additionally involving $\lor$​ on the outer level (which is just the entire expression set) the loosest. The subset relations directly give some rules that allow us to "convert" between judgments as appropriate:
> > $$
> > \dfrac{e\ \mathbf{Atom}}{e\ \mathbf{AndEx}} \quad \quad\dfrac{e\ \mathbf{AndEx}}{e\ \mathbf{OrEx}}
> > $$
> > The rules for the connectives are as follows: note the careful choice of judgments in the assumptions to preserve left-associativity as well as precedence.
> > $$
> > \dfrac{e_1\ \mathbf{OrEx}\quad e_2\ \mathbf{AndEx}}{e_1 \lor e_2\ \mathbf{OrEx}} \quad \dfrac{e_1\ \mathbf{AndEx}\quad e_2\ \mathbf{Atom}}{e_1 \land e_2\ \mathbf{AndEx}}
> > $$
> > Defining $\mathbf{Atom}$ is straightforward: note again the choice of judgment to assert in the parenthesised expression rule.
> > $$
> > \dfrac{c \in \{\top, \bot\}}{c\ \mathbf{Atom}}
> > \quad
> > \dfrac{e\ \mathbf{OrEx}}{\texttt{(}e\texttt{)}\ \mathbf{Atom}}
> > \quad
> > \dfrac{e\ \mathbf{Atom} }{\neg e\ \mathbf{Atom}}
> > $$

4. Assume you want to prove a property $P$ for all boolean expressions using rule induction over the rules of the first version. Which cases do you have to consider? What is the induction hypothesis for each case?

> > There would be five cases:
> >
> > 1. Prove $P(c)$ where $c\in \{ \top, \bot\}$.
> > 2. Prove $P(\neg e)$ where $e\ \mathbf{Bool}$ with inductive hypothesis $P(e)$.
> > 3. Prove $P((e))$where  $e\ \mathbf{Bool}$ with inductive hypothesis $P(e)$.
> > 4. Prove $P(e1 \lor e2)$ where  $e_1\ \mathbf{Bool}$ and  $e_2\ \mathbf{Bool}$ with inductive hypotheses $P(e1)$ and $P(e2)$.
> > 5. Prove $P(e1 \land e2)$ where  $e_1\ \mathbf{Bool}$ and  $e_2\ \mathbf{Bool}$ with inductive hypotheses $P(e1)$ and $P(e2)$.

<div id="outline-container-org9dd87ec" class="outline-2">
<h2 id="org9dd87ec"><span class="section-number-2">4</span> Simultaneous Induction</h2>
<div class="outline-text-2" id="text-4">
  </div></div>
  
In the lecture, we discussed two alternative definitions of a language of parenthesised expressions:
$$
\dfrac{}{\varepsilon\ \mathbf{M}}{M_E}\quad
\dfrac{s\ \mathbf{M}}{\texttt{(}s\texttt{)}\ \mathbf{M}}{M_N}\quad
\dfrac{s_1\ \mathbf{M}\quad s_2\ \mathbf{M}}{s_1s_2\ \mathbf{M}}{M_J}
$$


$$
\dfrac{}{\varepsilon\ \mathbf{L}}{L_E}\quad
\dfrac{s\ \mathbf{L}}{\texttt{(}s\texttt{)}\ \mathbf{N}}{N_N}\quad
\dfrac{s_1\ \mathbf{N}\quad s_2\ \mathbf{L}}{s_1s_2\ \mathbf{L}}{L_J}
$$

In the lecture, we showed that if $s\ \mathbf{M}$, then $s\ \mathbf{L}$ Show that the reverse direction of the implication is also true, and therefore $\mathbf{M}$ defines the same language as $\mathbf{L}$.

<i>Hint</i>: similar to the proof discussed in the lecture, it is not possible to prove it using straight forward rule induction. However, first try induction and to see what is missing, then adjust your proof accordingly.

> If $s\ \mathbf{L}$, then either:
>
> <b>Base Case</b>: $s = \varepsilon$ in this case, we can directly infer $s\ \mathbf{M}$ as
> $$
> \dfrac{ }{\varepsilon\ \mathbf{M}}{M_E}
> $$
> <b>Inductive Case</b>: $s = s_1 s_2$, for
>
> ​	$\bullet\ (A_1)\ s_1\ \mathbf{N}$
>
> ​	$\bullet\ (A_2)\ s_2\ \mathbf{L}$
>
> As only one of these assumptions $(A_2)$ mentions $\mathbf{L}$, we only get one inductive hypothesis, that $s_2\ \mathbf{M}$:
> $$
> \dfrac{\dfrac{???}{s_1\ \mathbf{M}} \quad \dfrac{ }{s_2\ \mathbf{M}}{I.H} }{s_1s_2\ \mathbf{M}}{M_J}
> $$
> The problem with this approach is that our proof goal is too specific, which makes our induction hypothesis too weak.
>
> Instead we will prove that if <i>either</i> $s\ \mathbf{L}$ or $s\ \mathbf{N}$, then $s\ \mathbf{M}$. This will mean we have to deal with the cases arising from rule $N_N$ as well as $L_E$ and $L_J$, but it also means that we get the second inductive hypothesis we need in the $L_J$ case.
>
> <b>Inductive Case</b>: $s = s_1 s_2$, for
>
> ​	$\bullet\ s_1\ \mathbf{N}$
>
> ​	$\bullet\ s_2\ \mathbf{L}$
>
> We now get inductive hypotheses $s_1\ \mathbf{M}$ and $s_2\ \mathbf{M}$.
> $$
> \dfrac{\dfrac{ }{s_1\ \mathbf{M}}{I.H}_1 \quad \dfrac{ }{s_2\ \mathbf{M}}{I.H}_2 }{s_1s_2\ \mathbf{M}}{M_J}
> $$
> <b>Inductive Case</b>: $s=(s1)$, for $s_1\ \mathbf{L}$. We get the inductive hypothesis that $s_1\ \mathbf{M}$.
> $$
> \dfrac{\dfrac{}{s_1\ \mathbf{M}}{I.H}}{\texttt{(}s_1\texttt{)}\ \mathbf{M}}{M_N}
> $$

