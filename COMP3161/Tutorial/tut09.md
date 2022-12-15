<div id="content">
<h1 class="title">Tute (Week 10)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orga391087">1. Overloading</a></li>
<li><a href="#org77e29df">2. Subtyping</a>
<ul>
<li><a href="#org1d99a95">2.1. Coercions and Subtyping</a></li>
<li><a href="#org3daca95">2.2. Constructor variance</a></li>
</ul>
</li>
<li><a href="#org6cb8cd5">3. LCR Conditions</a></li>
<li><a href="#org9cd2f44">4. Critical Section Solutions</a></li>
</ul>
</div>
  </div></div>

<div id="outline-container-orga391087" class="outline-2">
<h2 id="orga391087"><span class="section-number-2">1</span> Overloading</h2>
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

<div id="outline-container-org77e29df" class="outline-2">
<h2 id="org77e29df"><span class="section-number-2">2</span> Subtyping</h2>
<div class="outline-text-2" id="text-2">
</div>
<div id="outline-container-org1d99a95" class="outline-3">
<h3 id="org1d99a95"><span class="section-number-3">2.1</span> Coercions and Subtyping</h3>
  <div class="outline-text-3" id="text-2-1"></div></div></div>


You are given the type <code>Rectangle</code>, parameterised by its height and width, and the type <code>Square</code> parameterised by the length of one of its sides. Neither type is mutable.

1. Which type is the subtype, which type is the supertype?

2. Give a subtype/supertype ordering of the following set of function types: <code>Rectangle -&gt; Rectangle</code>, <code>Rectangle -&gt; Square</code>, <code>Square -&gt; Rectangle</code>, <code>Square -&gt; Square</code>. 

3. Define a data type <code>Square</code> and a data type <code>Rectangle</code> in Haskell. Then define a coercion function from elements of the subclass to elements of the superclass.

4. Show that the ordering you have given in the previous question is correct by defining coercion functions for each pair of types in a subtyping relationship in part (b).
</p>

<div id="outline-container-org3daca95" class="outline-3">
<h3 id="org3daca95"><span class="section-number-3">2.2</span> Constructor variance</h3>
  <div class="outline-text-3" id="text-2-2"></div></div>


List some examples of a <i>covariant</i>, <i>contravariant</i> and <i>invariant</i> type constructor.

<div id="outline-container-org6cb8cd5" class="outline-2">
<h2 id="org6cb8cd5"><span class="section-number-2">3</span> LCR Conditions</h2>
  <div class="outline-text-2" id="text-3"></div></div>


Consider the following two processes, each manipulating a shared variable $0$.

<b>Thread 1</b>: $x := x + 1; x:= x - 1;$

<b>Thread 2</b>: $x := x \times 2$

1. What are the possible final values of $x$ assuming each statement is executed <i>atomically</i>?

2. Rewrite the above program into one where each statement obeys the <i>limited critical reference</i> restriction. What are the possible final values now?
3. How could <i>locks</i> be used in your answer to (2) to ensure that only the final results from part (1) are possible?

<div id="outline-container-org9cd2f44" class="outline-2">
<h2 id="org9cd2f44"><span class="section-number-2">4</span> Critical Section Solutions</h2>
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


1. Explain how this algorithm meets the <i>mutual exclusion</i> property for critical section solutions. Note that the $\textbf{if}$ statement is <i>atomic</i> - executed in one step.
2. Now assume that the $\textbf{if}$ statement is split into two steps, one that checks the condition, and one that runs the $\textbf{then}$ or $\textbf{else}$ branch. Show that mutual exclusion is <i>violated</i> if that is the case.