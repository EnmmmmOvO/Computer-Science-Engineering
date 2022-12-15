<div id="content">
<h1 class="title">Tute (Week 1)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org5d5c17d">1. Predicate Logic</a>
<ul>
<li><a href="#orgb7e35c5">1.1. Question 1</a></li>
<li><a href="#org1a4267d">1.2. Question 2</a></li>
<li><a href="#org9ab70c3">1.3. Question 3</a></li>
<li><a href="#orged53b89">1.4. Question 4</a></li>
<li><a href="#orgabdb4e7">1.5. Question 5</a></li>
</ul>
</li>
<li><a href="#orge605081">2. Haskell</a>
<ul>
<li><a href="#org0440d11">2.1. Haskell lexical structure</a></li>
<li><a href="#org6a819d8">2.2. Haskell programming</a></li>
</ul>
</li>
<li><a href="#orgfd58c9c">3. Subtyping Sins</a></li>
</ul>
</div>
  </div>
</div>

<div id="outline-container-org5d5c17d" class="outline-2">
<h2 id="org5d5c17d"><span class="section-number-2">1. </span> Predicate Logic</h2>
<div class="outline-text-2" id="text-1">
</div>
<div id="outline-container-orgb7e35c5" class="outline-3">
<h3 id="orgb7e35c5"><span class="section-number-3">1.1</span> Question 1</h3>
<div class="outline-text-3" id="text-1-1"></div>
</div>
</div>

For which values of $A$ and $B$ does the boolean expression $\varphi = \neg (A \Rightarrow B) \lor \neg B$ hold?
> |  $A$   |  $B$   | $A \Rightarrow B$ | $\neg (A \Rightarrow B)$ | $\neg B$ | $\varphi$ |           |
> | :----: | :----: | :---------------: | :----------------------: | :------: | :-------: | :-------: |
> | $\top$ | $\top$ |      $\top$       |          $\bot$          |  $\top$  |  $\bot$   |           |
> | $\top$ | $\bot$ |      $\bot$       |          $\top$          |  $\top$  |  $\top$   | $\bullet$ |
> | $\bot$ | $\top$ |      $\top$       |          $\bot$          |  $\bot$  |  $\bot$   |           |
> | $\bot$ | $\bot$ |      $\top$       |          $\bot$          |  $\top$  |  $\top$   | $\bullet$ |
>
> $\mathbf{Proof}$:
> This is an answer but it is not so informative. Using boolean manipulation instead:
> $$
> \begin{array}{lcl}
> \neg (A \Rightarrow B) \lor \neg B & = & \neg (\neg A \lor B) \lor \neg B \\
>                                    & = &  (A \land \neg B) \lor \neg B \\
>                                    & = &  (A \lor \neg B) \land (\neg B \lor \neg B) \\
>                                    & = &  (A \lor \neg B) \land \neg B \\
>                                    & = &  \neg B \\
> \end{array}
> $$
> Here we can see clearly that $\varphi$ holds only when $B$ is false, and the value of $A$ does not matter.

<div id="outline-container-org1a4267d" class="outline-3">
<h3 id="org1a4267d"><span class="section-number-3">1.2</span> Question 2</h3>
<div class="outline-text-3" id="text-1-2"></div>
</div>

Simplify the boolean expression $(A \Rightarrow B) \lor (B \Rightarrow A)$.

> $$
> \begin{array}{lcl} (A \Rightarrow B) \lor (B \Rightarrow A) & = & (\neg A \lor B) \lor (\neg B \lor A) \\                                   & = &  (\neg A \lor A) \lor (\neg B \lor B) \\                                   & = &  \top \lor \top\\                                   & = &  \top \\ \end{array}
> $$
>
> This proof is not *constructive*. Discuss what it means for a proof to be constructive.

<div id="outline-container-org9ab70c3" class="outline-3">
<h3 id="org9ab70c3"><span class="section-number-3">1.3</span> Question 3</h3>
<div class="outline-text-3" id="text-1-3"></div>
</div>

A binary connective $\cdot$ is defined as follows:
| $A$    |  $B$   | $A \cdot B$|
| :---:  | :---:  | :------------:|
| $\bot$ | $\bot$ | $\top$ |
| $\bot$ | $\top$ | $\bot$ |
| $\top$ | $\bot$ | $\top$ |
| $\top$ | $\top$ | $\bot$ |

Restate the formula $A \lor B$ in terms of $\cdot$. What is the $\cdot$ connective?


> $A \cdot \neg B$, $\cdot$ is a flipped implication operator. The *ex falso quodlibet principle* is relevant here: from false, you can prove anything.

<div id="outline-container-orged53b89" class="outline-3">
<h3 id="orged53b89"><span class="section-number-3">1.4</span> Question 4</h3>
<div class="outline-text-3" id="text-1-4"></div>
</div>

Assuming that $F(x)$ states that the person $x$ is my friend and that $P(x)$ states that the person $x$ is perfect, what is a logical translation of the phrase "None of my friends are perfect"?


> One option is $\lnot \exists x. \; F(x) \land P(x)$, which can be read literally as saying <i>"there does not exist a person $x$ such that they are both my friend and perfect"</i> in plain English. There are a number of other equally-valid translations too:
>
> $\forall x. \; F(x) \Rightarrow \lnot P(x)$ , which can be read as saying <i>"if a person is my friend, then they aren't perfect"</i>.
>
> $\forall x. \; P(x) \Rightarrow \lnot F(x)$, , which can be read as saying <i>"if a person is perfect, then they aren't my friend"</i>.
>
> The logical formulae for all 3 are equivalent. As an exercise, prove this!

<div id="outline-container-orgabdb4e7" class="outline-3">
<h3 id="orgabdb4e7"><span class="section-number-3">1.5</span> Question 5</h3>
<div class="outline-text-3" id="text-1-5">
  </div></div>
Given the following function

$$
\begin{align}
f(n)=\left\{
\begin{array}{rcl}
0  & {if\ n = 0}\\
2n-1 + f(n-1) & {if\ n > 0}\\
\end{array}
\right.
\end{align}
$$

Prove that $\forall\ n \in \mathbb{N}.\ f(n) = n^2$

> Proof by mathematical induction on the natural number $n$
>
> Base Case: $n=0$
> $$
> \begin{array}{lcl}
>   f(0) & = & 0 \\
>        & = & 0^2 \\
>        &   & \blacksquare
> \end{array}
> $$
> Inductive Case: $n=k+1$, for arbitrary $k \in \mathbb{N}$. Assume the inductive hypothesis that $f(k)=k^2$
> $$
> \begin{array}{lcl}
>   f(k+1) & = & 2(k+1) - 1 + f(k) \\
>        & = & 2k + 2 - 1 + f(k) \\
>        & = & 2k + 1 + f(k) \\
>        & = & 2k + 1 + k^2 \quad \text{(I.H)}\\
>        & = & k^2+k+k+1 \\
>        & = & k(k+1)+(k+1) \\
>        & = & (k+1)(k+1) \\
>        & = & (k+1)^2 \\
>        &   & \blacksquare
> \end{array}
> $$
>  Thus $f(n)=n^2$ for all $n \in \mathbb{N}$

<div id="outline-container-orge605081" class="outline-2">
<h2 id="orge605081"><span class="section-number-2">2. </span> Haskell</h2>
<div class="outline-text-2" id="text-2">
<p>
Consider the Haskell code written in the lecture.
</p>
  </div></div>

<div id="outline-container-org0440d11" class="outline-3">
<h3 id="org0440d11"><span class="section-number-3">2.1</span> Haskell lexical structure</h3>
<div class="outline-text-3" id="text-2-1">
  </div></div>

1. What is the difference between a <code>data</code> and a <code>type</code> declaration?

> > A <code>data</code> declaration introduces a new type, for example the <code>Tree</code> type below. <code>type</code> keyword just introduces a new name for an existing type, like <code>typedef</code> in C. For example, the <code>String</code> type in the standard library is defined merely to be <code>[Char]</code> using a <code>type</code> declaration.


2. What is the difference between a <i>type</i> and a <i>data constructor</i>? List the identifiers in the code which represent <i>type names</i>, and those which represent data <i>constructor names</i>.

> > A <i>data constructor</i> describes a way to create a value of a certain <i>type</i>. For example, the <i>data constructors</i> in the below <code>Tree</code> type are <code>Leaf</code> and <code>Branch</code>: 
> >
> > ```haskell
> > data Tree a = Branch a (Tree a) (Tree a) | Leaf
> > ```

3. Which phase of the compiler would be responsible for distinguishing type and data constructors?  

> > The <i>parser</i> is responsible, as it requires information from the <i>grammar</i> of the language to determine if, for example, <code>Tree</code> is a data constructor or a type name, as it is lexically indistinguishable.

<div id="outline-container-org6a819d8" class="outline-3">
<h3 id="org6a819d8"><span class="section-number-3">2.2</span> Haskell programming</h3>
<div class="outline-text-3" id="text-2-2">
  </div></div>
1. Write a Haskell function <code>mySum</code> that sums all elements in a list of numbers. Feel free to use the following template:

2. Find a generalisation <code>myBinop</code> that applies a given binary operator <code>f</code> with unit element <code>z</code> to a list of numbers. We will then be able to define <code>myProduct</code> and <code>mySum</code> using <code>myBinop</code>.

  ```haskell
  mySum :: [Int] -> Int
  mySum [] = 0
  mySum (n:ns) = n + mySum ns
  
  myProduct :: [Int] -> Int
  myProduct [] = 1
  myProduct (n:ns) = n*myProduct ns
  
  myBinop :: (Int -> Int -> Int) -> Int -> ([Int] -> Int)
  myBinop f z [] = z
  myBinop f z (n:ns) = n `f` myBinop f z ns
  
  mySum2 :: [Int] -> Int
  mySum2 = myBinop (+) 0
  
  myProduct2 :: [Int] -> Int
  myProduct2 = myBinop (*) 1
  
  mySum3 :: [Int] -> Int
  mySum3 = foldr (+) 0
  
  myProduct3 :: [Int] -> Int
  myProduct3 = foldr (*) 1
  ```
2. Write a Haskell function <code>myProduct</code> that multiplies all elements in a list of numbers.
3. You probably used copypaste to solve the previous question, didn't you? No reason to be ashamed, we've all done it! But let's try not to.

   Find a generalisation <code>myBinop</code> that applies a given binary operator <code>f</code> with unit element <code>z</code> to a list of numbers. We will then be able to define <code>myProduct</code> and <code>mySum</code> using <code>myBinop</code>.

  ```haskell
  myBinop :: (Int -> Int -> Int) -> Int -> ([Int] -> Int)
  myBinop f z [] = ???
  myBinop f z (n:ns) = ???
  
  mySum :: [Int] -> Int
  mySum ns = myBinop (+) 0 ns
  
  myProduct :: [Int] -> Int
  myProduct ns = myBinop (*) 1 ns
  ```

4. We just reinvented a wheel. The <a href="https://hackage.haskell.org/package/base-4.17.0.0/docs/Data-List.html#g:3">fold functions</a> are general-purpose library functions that completely subsume <code>myBinop</code>. Try to implement <code>mySum</code> and <code>myProduct</code> using <code>foldr</code> instead of <code>myBinop</code>.

   The linked library documentation references a lot of concepts that we don't assume familiarity with, so don't worry if you don't fully understand it. Perhaps start by looking at the examples.

> > ```haskell
> > mySum :: [Int] -> Int
> > mySum [] = 0
> > mySum (n:ns) = n + mySum ns
> > 
> > myProduct :: [Int] -> Int
> > myProduct [] = 1
> > myProduct (n:ns) = n*myProduct ns
> > 
> > myBinop :: (Int -> Int -> Int) -> Int -> ([Int] -> Int)
> > myBinop f z [] = z
> > myBinop f z (n:ns) = n `f` myBinop f z ns
> > 
> > mySum2 :: [Int] -> Int
> > mySum2 = myBinop (+) 0
> > 
> > myProduct2 :: [Int] -> Int
> > myProduct2 = myBinop (*) 1
> > 
> > mySum3 :: [Int] -> Int
> > mySum3 = foldr (+) 0
> > 
> > myProduct3 :: [Int] -> Int
> > myProduct3 = foldr (*) 1
> > ```

<div id="outline-container-orgfd58c9c" class="outline-2">
<h2 id="orgfd58c9c"><span class="section-number-2">3. </span> Subtyping Sins</h2>
<div class="outline-text-2" id="text-3">
  </div></div>

The Tuesday lecture demonstrated a flaw in Java's static type system. It's been there for decades and it's well-known, including by the Java developers. Yet they've chosen not to fix it. Why do you think that is?

> There's no right or wrong answer to this question (unless your name is James Gosling).
