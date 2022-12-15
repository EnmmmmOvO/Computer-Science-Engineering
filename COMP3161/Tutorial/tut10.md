<div id="content">
<h1 class="title">Tute (Week 10)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org8b5d672">1. Overloading</a></li>
<li><a href="#org93a78c7">2. Subtyping</a>
<ul>
<li><a href="#orga8b3e68">2.1. Coercions and Subtyping</a></li>
<li><a href="#org0fb732d">2.2. Constructor variance</a></li>
</ul>
</li>
<li><a href="#org681eba1">3. LCR Conditions</a></li>
<li><a href="#orgcc643b4">4. Critical Section Solutions</a></li>
</ul>
</div>
  </div></div>

<div id="outline-container-org8b5d672" class="outline-2">
<h2 id="org8b5d672"><span class="section-number-2">1</span> Overloading</h2>
  <div class="outline-text-2" id="text-1"></div></div>

Consider the following file in Haskell:

```haskell
class Compare a where
  cmp :: a -> a -> Bool

instance Compare Int where
  cmp x y = x <= y

instance (Compare a) => Compare [a] where
  cmp xs ys = and (zipWith cmp xs ys)

group  :: (Compare a) => [a] -> [[a]]
group []     = []
group (x:xs) = let (ys, zs) = span (cmp x) xs
                in (x:ys) : group zs
```


How would the type checker translate this code to remove the type classes?

> ```haskell
> type CompareDict a = (a -> a -> Bool)
> 
> intCompareDict :: CompareDict Int
> intCompareDict x y = x <= y
> 
> listCompareDict :: CompareDict a -> CompareDict [a]
> listCompareDict cmp xs ys = and (zipWith cmp xs ys)
> 
> group  :: CompareDict a -> [a] -> [[a]]
> group cmp []     =  []
> group cmp (x:xs) = let (ys, zs) = span (cmp x) xs
>                     in (x:ys) : group cmp zs
> ```

<div id="outline-container-org93a78c7" class="outline-2">
<h2 id="org93a78c7"><span class="section-number-2">2</span> Subtyping</h2>
<div class="outline-text-2" id="text-2">
</div>
<div id="outline-container-orga8b3e68" class="outline-3">
<h3 id="orga8b3e68"><span class="section-number-3">2.1</span> Coercions and Subtyping</h3>
<div class="outline-text-3" id="text-2-1">
  </div></div>

You are given the type <code>Rectangle</code>, parameterised by its height and width, and the type <code>Square</code> parameterised by the length of one of its sides. Neither type is mutable.

1. Which type is the subtype, which type is the supertype?

> > <code>Square</code> is a subtype of <code>Rectangle</code>.


2. Give a subtype/supertype ordering of the following set of function types: <code>Rectangle -&gt; Rectangle</code>, <code>Rectangle -&gt; Square</code>, <code>Square -&gt; Rectangle</code>, <code>Square -&gt; Square</code>. 

> > <code>Rectangle -&gt; Square</code> is a subtype of <code>Rectangle -&gt; Rectangle</code> and <code>Square -&gt; Square</code>, which are both subtypes of <code>Square -&gt; Rectangle</code>.

3. Define a data type <code>Square</code> and a data type <code>Rectangle</code> in Haskell. Then define a coercion function from elements of the subclass to elements of the superclass.

> > ```haskell
> > data Square = Square Int
> > data Rectangle = Rect Int Int
> > 
> > coerce :: Square -> Rectangle
> > coerce (Square w) = Rect w w
> > ```


4. Show that the ordering you have given in the previous question is correct by defining coercion functions for each pair of types in a subtyping relationship in part (b).

> > ```haskell
> > rs2rr :: (Rectangle -> Square) -> (Rectangle -> Rectangle)
> > rs2rr f = coerce . f
> > 
> > rs2ss :: (Rectangle -> Square) -> (Square -> Square)
> > rs2ss f = f . coerce
> > 
> > rr2sr :: (Rectangle -> Rectangle) -> (Square -> Rectangle)
> > rr2sr f = f . coerce
> > 
> > ss2sr :: (Square -> Square) -> (Square -> Rectangle)
> > ss2sr f = coerce . f
> > ```

<div id="outline-container-org0fb732d" class="outline-3">
<h3 id="org0fb732d"><span class="section-number-3">2.2</span> Constructor variance</h3>
  <div class="outline-text-3" id="text-2-2"></div></div>
List some examples of a <i>covariant</i>, <i>contravariant</i> and <i>invariant</i> type constructor.

> A function's argument is contravariant. A function's return type is covariant. A data type like <code>Endo</code> below 
> is invariant:
>
> > ```haskell
> > data Endo a = E (a -> a)
> > ```

<div id="outline-container-org681eba1" class="outline-2">
<h2 id="org681eba1"><span class="section-number-2">3</span> LCR Conditions</h2>
  <div class="outline-text-2" id="text-3"></div></div>
Consider the following two processes, each manipulating a shared variable $0$

**Thread 1** $x := x + 1; x:= x - 1;$

**Thread 2** $x := x \times 2$

1. What are the possible final values of $x$ assuming each statement is executed <i>atomically</i>?

> > $x$ is either zero or one.

2. Rewrite the above program into one where each statement obeys the <i>limited critical reference</i> restriction. What are the possible final values now?

> > **Thread 1** $\textbf{var}\ t; t := x; x := t + 1; t := x; x := t - 1;$
> >
> > **Thread 2** $\textbf{var}\ u; u := x; x := u \times 2$
> >
> > This allows the final write of thread 2 to happen well after the read of thread 2. Thus, a final result of $x = -1$ is now also possible.

3. How could <i>locks</i> be used in your answer to (b) to ensure that only the final results from part (a) are possible?

> > Each formerly-atomic statement must now be protected by a shared lock $\ell$:
> >
> > **Thread 1**: $\begin{array}{l}\textbf{var}\ t; \mathbf{take}(\ell); t := x; x := t + 1; \mathbf{release}(\ell);\\ \mathbf{take}(\ell); t := x; x := t - 1; \mathbf{release}(\ell);\end{array}$
> >
> > **Thread 2**: $\textbf{var}\ u; \mathbf{take}(\ell); u := x; x := u \times 2; \mathbf{release}(\ell);$

<div id="outline-container-orgcc643b4" class="outline-2">
<h2 id="orgcc643b4"><span class="section-number-2">4</span> Critical Section Solutions</h2>
  <div class="outline-text-2" id="text-4"></div></div>

This is the Manna-Pnueli algorithm for critical sections:
$$
\begin{array}{| c |}
\hline
\textbf{var}\ \mathit{wantp, wantq} := 0, 0\\
\begin{array}{l | l}\hline
\mathbf{while}\ \mathit{True}\ \mathbf{do} &
\mathbf{while}\ \mathit{True}\ \mathbf{do} \\
p_1: \quad \textit{non-critical section} & q_1: \quad \textit{non-critical section}\\
p_2: \quad \textbf{if}\ \mathit{wantq} = -1 & q_2: \quad \textbf{if}\ \mathit{wantp} = -1 \\
\quad\qquad\mathbf{then}\ \mathit{wantp} := -1 & \quad\qquad\mathbf{then}\ \mathit{wantq} := 1\\
\quad\qquad\mathbf{else}\ \mathit{wantp} := 1 & \quad\qquad\mathbf{else}\ \mathit{wantq} := -1\\
p_3: \quad \textbf{await}\ \mathit{wantp} \neq \mathit{wantq} & q_3: \quad \textbf{await}\ \mathit{wantp} \neq -\mathit{wantq} \\
p_4: \quad \textit{critical section} & q_4: \quad \textit{critical section}\\
p_5: \quad \mathit{wantp} := 0 & q_5: \quad \mathit{wantq} := 0\\
\textbf{od}&\textbf{od}\\\end{array}\\\hline
\end{array}
$$

1. Explain how this algorithm meets the <i>mutual exclusion</i> property for critical section solutions.
Note that the $\textbf{if}$ statement is <i>atomic</i> - executed in one step.

> > At statement $p_3$, observe that we know already that $|\mathit{wantp}| = 1$ from the previous if statement.
> > Similarly at statement $q_3$ we also know that $|\mathit{wantq}| = 1$.
> >
> > For $p$ to enter its critical section, it must pass the $\textbf{await}$ guard, thus for $p$ to be in it's critical section it must be the case that $\mathit{wantp} \neq \mathit{wantq}$. Similarly, for $q$ to be in it's critical section it must be the case that $\mathit{wantp} \neq -\mathit{wantq}$.
> >
> > If both processes were in their critical section at the same time, that would mean that $|\mathit{wantp}| = 1 = |\mathit{wantq}|$. This is a contradiction. Therefore, these two processes cannot be in their critical section at the same time and mutual exclusion is satisfied.

2. Now assume that the $\textbf{if}$ statement is split into two steps, one that checks the condition, and one that runs the $\textbf{else}$ branch. Show that mutual exclusion is <i>violated</i> if that is the case.

> > Let the statement $p_C$ before the condition is checked, and $p_E$ before the then and else branches respectively. Similarly for the statement $q_2$.
> >
> > Then the following interleaving violates mutual exclusion.
> > $$
> > p_1q_1p_Cq_Cp_Eq_Eq_3q_4p_3p_4
> > $$