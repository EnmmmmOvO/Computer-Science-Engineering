<div id="content">
<h1 class="title">Tute (Week 8)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orga4c175a">1. Data Types</a>
<ul>
<li><a href="#orgf8eb5cd">1.1. Converting from Haskell</a></li>
<li><a href="#orgdf78e4f">1.2. Recursive Types</a></li>
<li><a href="#org5458545">1.3. Type Isomorphisms</a></li>
<li><a href="#org8b8b164">1.4. Typing Terms</a></li>
<li><a href="#org7f9c409">1.5. Curry-Howard</a>
<ul>
<li><a href="#orgb229f7f">1.5.1. Proof Witnesses</a></li>
<li><a href="#org78c1147">1.5.2. Proving a proposition</a></li>
<li><a href="#org77ebc27">1.5.3. Constructivity</a></li>
</ul>
</li>
</ul>
</li>
<li><a href="#org277d150">2. Polymorphism</a>
<ul>
<li><a href="#orge49b04e">2.1. Quantifier Positions</a></li>
<li><a href="#orgd4fac2a">2.2. Parametricity</a></li>
</ul>
</li>
</ul>
</div>
  </div></div>
<div id="outline-container-orga4c175a" class="outline-2">
<h2 id="orga4c175a"><span class="section-number-2">1</span> Data Types</h2>
<div class="outline-text-2" id="text-1">
</div>
<div id="outline-container-orgf8eb5cd" class="outline-3">
<h3 id="orgf8eb5cd"><span class="section-number-3">1.1</span> Converting from Haskell</h3>
  <div class="outline-text-3" id="text-1-1"></div></div></div>
Use MinHS type constructors $+$ , $\times$  and $\mathbf{rec}$ to describe types isomorphic to each of the following Haskell types. Give example terms for each type.

```haskell
data Direction = East | West | North | South
data Foo = Foo Int Bool Int
data Tree = Node Tree Tree | Leaf
```


> $$
> \begin{array}{lcllcl}\texttt{Direction} & \simeq & \mathbf{1} + (\mathbf{1} + (\mathbf{1} + \mathbf{1})) & \texttt{West} & \simeq & (\mathsf{InR}\ (\mathsf{InL}\ \texttt{()}))\\ 
> \texttt{Foo} & \simeq & \mathtt{Int}\times(\mathtt{Bool}\times\mathtt{Int})
> &\texttt{Foo}\ 3\ \texttt{True}\ 2 & \simeq & (3, (\mathsf{True}, 2))\\
> \texttt{Tree} & \simeq & \mathbf{rec}\ t. (t \times t) + \mathbf{1}\\
> \end{array}
> $$

<div id="outline-container-orgdf78e4f" class="outline-3">
<h3 id="orgdf78e4f"><span class="section-number-3">1.2</span> Recursive Types</h3>
  <div class="outline-text-3" id="text-1-2"></div></div>
Give an example MinHS term for each of the following types (if such a term exists), and derive the typing judgement for that term.


1. $\mathbf{rec}\ t.\ (\mathtt{Int} + t)$

> > $$
> > \dfrac{
> > \dfrac
> > {
> > \dfrac
> > {
> > \dfrac{ \dfrac{}{3 : \mathtt{Int} }}
> > {\mathsf{InL}\ 3 : (\mathtt{Int} + (\mathbf{rec}\ t.\ (\mathtt{Int} + t)) )}
> > }
> > {\mathsf{roll}\ (\mathsf{InL}\ 3) :  (\mathbf{rec}\ t.\ (\mathtt{Int} + t)) }
> > }
> > {\mathsf{InR}\ (\mathsf{roll}\ (\mathsf{InL}\ 3)) : (\mathtt{Int} + (\mathbf{rec}\ t.\ (\mathtt{Int} + t)) )}
> > }
> > {\mathsf{roll}\ (\mathsf{InR}\ (\mathsf{roll}\ (\mathsf{InL}\ 3))) : \mathbf{rec}\ t.\ (\mathtt{Int} + t)}
> > $$

2. $\mathbf{rec}\ t.\ (\mathtt{Int} \times \mathtt{Bool})$

> > $$
> > \dfrac{ 
> > \dfrac{ \dfrac{}{3 : \mathtt{Int}}  \quad \dfrac{}{\mathsf{True} : \mathtt{Bool}} }
> > {(3, \mathsf{True}) : (\mathtt{Int} \times \mathtt{Bool})}}
> > {\mathsf{roll}\ (3, \mathsf{True}) : \mathbf{rec}\ t.\ (\mathtt{Int} \times \mathtt{Bool})}
> > $$
> >

3. $\mathbf{rec}\ t.\ (\mathtt{Int} \times t)$

> > There is no finite term of this type, but we can make one with recfun:
> > $$
> > \mathbf{recfun}\ f\ x = \mathsf{roll}\ (x, f\ x)
> > $$

<div id="outline-container-org5458545" class="outline-3">
<h3 id="org5458545"><span class="section-number-3">1.3</span> Type Isomorphisms</h3>
  <div class="outline-text-3" id="text-1-3"></div></div>

Which of the following types are isomorphic to each other (assuming a strict semantics)?
1. $\textbf{rec}\ t.\ t \times t$
2. $\textbf{0}$
3. $\textbf{1}$
4. $\textbf{1} \times \textbf{0}$
5. $\textbf{rec}\ t.\ t \times \textbf{1}$
6. $\textbf{rec}\ t.\ t + \textbf{1}$

> > 1, 2, 4, 5 are all isomorphic. 3 and 6 are in their own isomorphism equivalence classes.

<div id="outline-container-org8b8b164" class="outline-3">
<h3 id="org8b8b164"><span class="section-number-3">1.4</span> Typing Terms</h3>
  <div class="outline-text-3" id="text-1-4"></div></div> 
  
For each of the following terms, give a possible type for the term (there may be more than one type).
1. $(\mathsf{InL}\ \mathsf{True})$

> > In these answers, I've opted for the smallest possible type.
> >
> > $\texttt{Bool} + \mathbf{0}$

2. $(\mathsf{InR}\ \mathsf{True})$

> > $\texttt{Bool} + \mathbf{0}$

3. $(\mathsf{InL}\ (\mathsf{InL}\ \mathsf{True}))$

> > $(\texttt{Bool} + \mathbf{0})+\mathbf{0}$

3. $(\mathsf{roll}\ (\mathsf{InR}\ \mathsf{True}))$

> > $\mathbf{rec}\ t.\ (\mathbf{0} + \texttt{Bool})$

4. $(\texttt{()}, (\mathsf{InL}\ \texttt{()}))$

> >$\mathbf{1} \times (\mathbf{1} + \mathbf{0})$

<div id="outline-container-org7f9c409" class="outline-3">
<h3 id="org7f9c409"><span class="section-number-3">1.5</span> Curry-Howard</h3>
<div class="outline-text-3" id="text-1-5">
  </div></div>
<div id="outline-container-orgb229f7f" class="outline-4">
<h4 id="orgb229f7f"><span class="section-number-4">1.5.1</span> Proof Witnesses</h4>
  <div class="outline-text-4" id="text-1-5-1"></div></div>
For which of the following types can you write a terminating, total (i.e., not returning error, undefined or causing other runtime errors, but a value of the result type) MinHs function? Try to answer this question without trying to implement the function.


What proposition does each of these types correspond to?

1. $(a \rightarrow b) \rightarrow (b \rightarrow c) \rightarrow (a \rightarrow c)$

> > Corresponds to the transitivity of implication which is constructively provable, therefore a program can be written in MinHS.

2. $((a \times b) \rightarrow c) \rightarrow (a \rightarrow c)$

> > Corresponds to the proposition $((a \land b) \rightarrow c) \rightarrow (a \rightarrow c)$ which is not constructively provable and therefore such a program cannot be written.

3. $(a \rightarrow c) \rightarrow ((a \times b) \rightarrow c)$

> > Corresponds to the proposition $(a \rightarrow c) \rightarrow ((a \land b) \rightarrow c)$, which is constructively provable. Therefore such a program can be written.

<div id="outline-container-org78c1147" class="outline-4">
<h4 id="org78c1147"><span class="section-number-4">1.5.2</span> Proving a proposition</h4>
  <div class="outline-text-4" id="text-1-5-2"></div></div>
Write a program which is a proof of the symmetry of disjunction, i.e.   

$$A \lor B \Rightarrow B \lor A$$

> ```haskell
> proof = (recfun x = case x of InL a -> InR a; InR b -> InL b)
> ```

<div id="outline-container-org77ebc27" class="outline-4">
<h4 id="org77ebc27"><span class="section-number-4">1.5.3</span> Constructivity</h4>
  <div class="outline-text-4" id="text-1-5-3"></div></div>
Lambda calculus is said to correspond to <i>constructive</i> logic. What is meant by <i>constructive</i> here?


> Constructive logics require proofs to present evidence. Therefore, they do not accept principles like the *law of the excluded middle* and *double negation elimination*.
>
> Trying to write a typed $\lambda$ calculus program with a type that corresponds to $\neg(\neg A) \rightarrow A$ is indeed rather impossible.

<div id="outline-container-org277d150" class="outline-2">
<h2 id="org277d150"><span class="section-number-2">2</span> Polymorphism</h2>
<div class="outline-text-2" id="text-2">
</div>
<div id="outline-container-orge49b04e" class="outline-3">
<h3 id="orge49b04e"><span class="section-number-3">2.1</span> Quantifier Positions</h3>
  <div class="outline-text-3" id="text-2-1"></div></div></div>

Explain the difference between a function of type $\forall a.\ a \rightarrow a$ and $(\forall a.\ a) \rightarrow (\forall a.\ a)$

> The first function allows the caller to specify a type, and then the caller must provide a value of that type. As the function does not know what type the caller will specify, the only thing it can do to that value is return it.
>
> The second function requires the caller to provide a value that the function could instantiate to any type, and will then return a value that the caller can instantiate to any type. As there is no way to construct a value of type $\forall a. a$, this function is impossible to actually execute dynamically.

<div id="outline-container-orgd4fac2a" class="outline-3">
<h3 id="orgd4fac2a"><span class="section-number-3">2.2</span> Parametricity</h3>
  <div class="outline-text-3" id="text-2-2"></div></div>
What can we conclude about the following functions solely from looking at their type signature?  

1. $f_1 : \forall a.\ [a] \rightarrow a$

> > If the function returns at all, the output value must be one of the elements of the input list.

2. $f_2 : \forall a.\ \forall b.\ [a] \rightarrow [b]$

> > If the function returns at all, the output list is empty.

3. $f_3 : \forall a.\ \forall b.\ [a] \rightarrow b$

> > The function does not return.

4. $f_4 : [\texttt{Int}] \rightarrow [\texttt{Int}]$

> > Only that the output will be a list of integers, if the function returns at all.