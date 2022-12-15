<div id="content">
<h1 class="title">Tute (Week 7)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org4a9ce8b">1. Abstract machines</a>
<ul>
<li><a href="#org19d35ac">1.1. The E Machine</a></li>
<li><a href="#org0bf0505">1.2. Closures</a></li>
<li><a href="#org34b710f">1.3. Tail Calls</a></li>
</ul>
</li>
<li><a href="#orgf659ca3">2. Safety and Liveness</a>
<ul>
<li><a href="#org9213643">2.1. Decomposing Properties</a></li>
<li><a href="#orga775408">2.2. Type Safety</a></li>
</ul>
</li>
</ul>
</div>
  </div></div>
<div id="outline-container-org4a9ce8b" class="outline-2">
<h2 id="org4a9ce8b"><span class="section-number-2">1</span> Abstract machines</h2>
  <div class="outline-text-2" id="text-1"></div></div>

Recall the abstract machine from the [Week 5 tutorial](tut05.md).

<div id="outline-container-org19d35ac" class="outline-3">
<h3 id="org19d35ac"><span class="section-number-3">1.1</span> The E Machine</h3>
<div class="outline-text-3" id="text-1-1">
  </div></div>

Evaluate the following expression using E-machine rules given in the lecture (where $\mathtt{Num}$ is abbreviated to $\mathtt{N}$):

$$
\small (\mathtt{Apply}\ (\mathtt{Fun}\ (f.x. \mathtt{If}\ (\mathtt{Less}\ x\ (\mathtt{N}\ 2))\ (\mathtt{N}\ 0)\ (\mathtt{Apply}\ f\ (\mathtt{Minus}\ x\ (\mathtt{N}\ 1)))))\ (\mathtt{N}\ 3))
$$
You don't need to write down every single step, but show how the contents of the stack and environments change during evaluation.

> Feel free to skip even more steps of evaluation here. Just noting down the pattern of environments sitting on the stack that emerges, which is relevant to the third question.  
> 
> $\begin{array}{cl} & \circ\ \vert\ \bullet \succ (\mathtt{Apply}\ (\mathtt{Fun}\ (f.x.\ (\mathtt{If}\ (\mathtt{Less}\ x\ (\mathtt{N}\ 2))\ (\mathtt{N}\ 0)\ (\mathtt{Apply}\ f\ (\mathtt{Minus}\ x\ (\mathtt{N}\ 1))))))\ (\mathtt{N}\ 3))\\ \mapsto_E & (\texttt{Apply}\ \square\ (\texttt{N}\ 3)) \triangleright \circ\ \vert\ \bullet \succ (\texttt{Fun}\ (f.x.\ (\texttt{If}\ (\texttt{Less}\ x\ (\texttt{N}\ 2))\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))))))\\ \mapsto_E & (\texttt{Apply}\ \square\ (\texttt{N}\ 3)) \triangleright \circ\ \vert\ \bullet \prec \langle\!\langle\bullet ; f.x.\ \cdots \rangle\!\rangle\\ \mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\ \square) \triangleright \circ\ \vert\ \bullet \succ (\texttt{N}\ 3)\\ \mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots \rangle\!\rangle\ \square) \triangleright \circ\ \vert\ \bullet \prec 3\\[0.5em] & \text{Let }\eta_1 \text{ be the environment: } f = \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle, x = 3, \bullet\\[0.5em] \mapsto_E & \bullet \triangleright \circ\ \vert\ \eta_1 \succ (\texttt{If}\ (\texttt{Less}\ x\ (\texttt{N}\ 2))\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))))\\ \mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \succ (\texttt{Less}\ x\ (\texttt{N}\ 2))\\[0.25em] & \text{Skipping some steps...}\\[0.25em] \mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \prec \texttt{False}\\ \mapsto_E & \bullet \triangleright \circ\ \vert\ \eta_1 \succ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))\\ \mapsto_E & (\texttt{Apply}\ \square\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \succ f\\ \mapsto_E & (\texttt{Apply}\ \square\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \prec \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\\ \mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\ \square) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \succ (\texttt{Minus}\ x\ (\texttt{N}\ 1))\\[0.25em] & \text{Skipping some steps...}\\[0.25em] \mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\ \square) \triangleright \bullet \triangleright \circ\ \vert\ \eta_1 \prec 2\\ \end{array}$
> 
> $\begin{array}{cl} & \text{Let } \eta_2 \text{ be the environment: } f = \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle, x = 2, \bullet\\[0.5em]
\mapsto_E & \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \succ (\texttt{If}\ (\texttt{Less}\ x\ (\texttt{N}\ 2))\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))))\\
\mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \succ (\texttt{Less}\ x\ (\texttt{N}\ 2))\\[0.25em]
& \text{Skipping some steps...}\\[0.25em]
\mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \prec \texttt{False}\\
\mapsto_E & \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \succ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))\\
\mapsto_E & (\texttt{Apply}\ \square\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))) \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \succ f\\
\mapsto_E & (\texttt{Apply}\ \square\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))) \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \prec \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\\
\mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle\ \square) \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \succ (\texttt{Minus}\ x\ (\texttt{N}\ 1))\\[0.25em]
& \text{Skipping some steps...}\\[0.25em]
\mapsto_E & (\texttt{Apply}\ \langle\!\langle\bullet ; f.x.\ \cdots\triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \prec 1\\[0.5em]
 & \text{Let } \eta_3 \text{ be the environment: } f = \langle\!\langle\bullet ; f.x.\ \cdots\rangle\!\rangle, x = 1, \bullet\\[0.5em]
\mapsto_E & \eta_2 \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_3 \succ (\texttt{If}\ (\texttt{Less}\ x\ (\texttt{N}\ 2))\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1))))\\
\mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \eta_2 \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_3 \succ (\texttt{Less}\ x\ (\texttt{N}\ 2))\\[0.25em]
& \text{Skipping some steps...}\\[0.25em]
\mapsto_E & (\texttt{If}\ \square\ (\texttt{N}\ 0)\ (\texttt{Apply}\ f\ (\texttt{Minus}\ x\ (\texttt{N}\ 1)))) \triangleright \eta_2 \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_3 \prec \texttt{True}\\
\mapsto_E & \eta_2 \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_3 \succ (\texttt{N}\ 0)\\
\mapsto_E & \eta_2 \triangleright \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_3 \prec 0\\
\mapsto_E & \eta_1 \triangleright \bullet \triangleright \circ\ \vert\ \eta_2 \prec 0\\
\mapsto_E & \bullet \triangleright \circ\ \vert\ \eta_1 \prec 0\\
\mapsto_E & \circ\ \vert\ \bullet \prec 0\\
\end{array}$

<div id="outline-container-org0bf0505" class="outline-3">
<h3 id="org0bf0505"><span class="section-number-3">1.2</span> Closures</h3>
  <div class="outline-text-3" id="text-1-2"></div></div>
Give an example of a program that evaluates to different results in an environment semantics, depending on whether or not closures are used. You may use the MinHS dialect used in your assignment.

> $$
> \mathbf{let}\ x = 2\ \mathbf{in}\ (\mathbf{let}\ x = 3\ \mathbf{in}\ (\mathbf{recfun}\ f\ y = x))\ 1
> $$
>
>
> Evaluates to 3 with closures, and 2 without.


<div id="outline-container-org34b710f" class="outline-3">
<h3 id="org34b710f"><span class="section-number-3">1.3</span> Tail Calls</h3>
  <div class="outline-text-3" id="text-1-3"></div></div>

Consider the following two programs:

```haskell
sumInt :: Int -> Int
sumInt 0 = 0
sumInt n = n + (sumInt (n-1))

sumInt' :: Int -> Int
sumInt' n = sum2 0 n
  where
    sum2 m 0 = m
    sum2 m n = sum2 (m+n) (n-1)
```


In a strict (call-by-value) language, the first program would lead to a stack overflow if applied to a sufficiently large number, but the second would not.


1. Explain how <i>tail-call elimination</i> can be applied to these examples.

> > The first example is not tail-recursive, in that the last computation done by the function body is an addition, not a recursive function call.  
> >
> > In the second example, the last thing performed by the inner computation is a recursive function call, which means the stack frame allocated can be re-used for the function call, without allocating any more memory.
>
2. How can we change the definition of our E-Machine to optimize tail-calls?

> > The pattern produced by tail calls in the E-Machine is a series of environments sitting on the stack with no intermediate computations, as in the above example.
> >
> > Changing the rule for function application to include a special case when an environment is already on the stack (and not saving the current environment in that case) just leaves the environment that was first pushed onto the stack, and doesn't bother to save the rest:
> > $$
> > \dfrac{}{ (\mathtt{Apply}\ \langle\!\langle \eta_f; f.x.\ e \rangle\!\rangle\ \square)
> >    \triangleright \eta_s \triangleright s\ \vert\ \eta \prec v \mapsto_E \eta_s \triangleright s\ \vert\ f=\langle\!\langle \cdots \rangle\!\rangle, x=v, \eta_f \succ e  }
> > $$
>
3. In Haskell, the second version will still exhaust all available memory if applied to a sufficiently large number. Why is this the case?

> > Haskell, being lazily evaluated, does not bother to evaluate the accumulator parameter until it is pattern matched on:
> > ```haskell
> > sum2 0 10 = sum2 (0 + 10) (10-1)
> >           = sum2 (0 + 10) 9          -- evaluated from pattern match
> >           = sum2 (0 + 10 + 9) (9-1) 
> >           = sum2 (0 + 10 + 9) 8      -- pattern match
> >           = sum2 (0 + 10 + 9 + 8) (8-1)
> > ```
> > As can be seen, the accumulator is constantly growing in size, as it is never matched on.
> >
> > GHC can be fooled into evaluating the accumulator by doing a pointless pattern match:
> >
> > ```haskell
> > sum2 0 0 = 0
> > sum2 m 0 = 0 
> > sum2 m n = sum2 (m + n) (n - 1)
> > ```
> >
> > But a more idiomatic way is to use ```BangPatterns```:
> >
> > ```haskell
> > sum2 !m 0 = 0 
> > sum2 !m n = sum2 (m + n) (n - 1)
> > ```
> >
> > Or, if extensions are not desired, the ```seq```combinator, which forces evaluation of the left hand side before returning the right:
> > ```haskell
> > sum2 m 0 = 0 
> > sum2 m n = let m' = m + n 
> >            in m' `seq` sum2 (m + n) (n - 1)
> > ```

<div id="outline-container-orgf659ca3" class="outline-2">
<h2 id="orgf659ca3"><span class="section-number-2">2</span> Safety and Liveness</h2>
  <div class="outline-text-2" id="text-2"></div></div>
  
1. Type Safety is said to be a safety property, and termination is said to be a liveness property. Suppose I was impatient, and stated a stronger termination property as follows:

<center> The process will terminate and halt execution <i>within a billion steps</i>.</center>

​		Is this version still a liveness property?

> >  No, it is a safety property, as a violation can be observed after a finite amount of steps.

2. What are the properties of <i>progress</i> and <i>preservation</i>? Are they safety or liveness properties?

> > Progress states that well-typed terms are not stuck. Preservation states that well-typed terms evaluate to terms that have the same type.
> >
> > Both of these properties are safety properties, as they comprise the type safety property.

<div id="outline-container-org9213643" class="outline-3">
<h3 id="org9213643"><span class="section-number-3">2.1</span> Decomposing Properties</h3>
  <div class="outline-text-3" id="text-2-1"></div></div>
For each of the following program properties, decompose it into the
intersection of a <i>safety</i> property and a <i>liveness</i> property.

1. The program will allocate exactly $100MB$ of memory.
> > The safety component is that the program will not allocate more than $100MB$ of memory. The liveness component is that the program will allocate at least $100MB$ of memory.

2. The program will not overflow the stack.

> >  The safety component is that the program will not overflow the stack. The liveness component is the set of all behaviours.
3. The program will return the sum of its inputs.

> >  The liveness component is that the program will return. The safety component is that if the program returns, it will return the sum of its inputs.
4. The program will call the function <code>foo</code>.

> >  The safety component is the set of all behaviours. The liveness component is that the function ```foo``` will be called.

<div id="outline-container-orga775408" class="outline-3">
<h3 id="orga775408"><span class="section-number-3">2.2</span> Type Safety</h3>
  <div class="outline-text-3" id="text-2-2"></div></div>

Why is the handling of partial functions important for a type safe language? 
How does it impact <i>progress</i> and <i>preservation</i>?
> In order to satisfy progress, we need a successor state for every well-typed expression, including invocations of partial functions. Thus, we must introduce an ```error``` state, that is a final state, that is the result of evaluating a partial function outside of its domain.
> 
> In order to satisfy preservation, we allow ```error``` to take on any type at all.
