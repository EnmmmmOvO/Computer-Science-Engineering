<div id="content">
<h1 class="title">Tute (Week 3)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org6e3dcd4">1. Parsing Relation</a></li>
<li><a href="#orgeb3a77c">2. Substitution</a></li>
<li><a href="#org4afa4a8">3. Semantics</a>
<ul>
<li><a href="#orge2a8c97">3.1. Denotational Semantics</a></li>
<li><a href="#org76d6ac1">3.2. Operational Semantics</a>
<ul>
<li><a href="#org7ef5347">3.2.1. Small-Step Semantics</a></li>
<li><a href="#org297905e">3.2.2. Big-Step Semantics</a></li>
</ul>
</li>
</ul>
</li>
<li><a href="#orgf7bd297">4. Lambda calculus and binding</a>
<ul>
<li><a href="#org9232c9d">4.1. Reduction</a></li>
<li><a href="#org00453a0">4.2. de Bruijn Indices</a></li>
</ul>
</li>
</ul>
</div>
</div>
<div id="outline-container-org6e3dcd4" class="outline-2">
<h2 id="org6e3dcd4"><span class="section-number-2">1</span> Parsing Relation</h2>
  <div class="outline-text-2" id="text-1"></div></div></div>

Using the inference rules for the parsing relation of arithmetic expressions given in [the syntax slides](/Lecture/lec06/slide06.pdf), derive the <i>abstract syntax</i> corresponding to the <i>concrete syntax</i> <code>3 + let x = 5 in x + 2 end</code>.

> Here <code>Num</code> nodes are shortened to just <code>N</code>.
> $$
> {\dfrac{\dfrac{ \dfrac{}{ \texttt{3}\ \mathbf{Atom} \longleftrightarrow (\mathtt{N}\ 3)} }{\texttt{3}\ \mathbf{PExp} \longleftrightarrow (\mathtt{N}\ 3) } \dfrac{ \dfrac{ \dfrac{ \dfrac{  \dfrac{ \dfrac{}{ \texttt{5}\ \mathbf{Atom} \longleftrightarrow (\mathtt{N}\ 5)} }{\texttt{5}\ \mathbf{PExp} \longleftrightarrow (\mathtt{N}\ 5) } }{\texttt{5}\ \mathbf{SExp} \longleftrightarrow (\mathtt{N}\ 5) }\dfrac{ \dfrac{ \dfrac{}{ \texttt{x}\ \mathbf{Atom} \longleftrightarrow (\mathtt{Var}\ \texttt{"x"})} }{\texttt{x}\ \mathbf{PExp} \longleftrightarrow (\mathtt{Var}\ \texttt{"x"}) }\dfrac{ \dfrac{ \dfrac{}{ \texttt{2}\ \mathbf{Atom} \longleftrightarrow (\mathtt{N}\ 2)} }{\texttt{2}\ \mathbf{PExp} \longleftrightarrow (\mathtt{N}\ 2) } }{\texttt{2}\ \mathbf{SExp} \longleftrightarrow (\mathtt{N}\ 2) }}{\texttt{x + 2}\ \mathbf{SExp} \longleftrightarrow (\mathtt{Plus}\ (\mathtt{Var}\ \texttt{"x"})\ (\mathtt{N}\ 2) ) }}{\texttt{let x = 5 in x + 2 end}\ \mathbf{Atom} \longleftrightarrow (\mathtt{Let}\ \texttt{"x"}\ (\mathtt{N}\ 5)\ (\mathtt{Plus}\ (\mathtt{Var}\ \texttt{"x"})\ (\mathtt{N}\ 2))) }}{\texttt{let x = 5 in x + 2 end}\ \mathbf{PExp} \longleftrightarrow (\mathtt{Let}\ \texttt{"x"}\ (\mathtt{N}\ 5)\ (\mathtt{Plus}\ (\mathtt{Var}\ \texttt{"x"})\ (\mathtt{N}\ 2))) }}{\texttt{let x = 5 in x + 2 end}\ \mathbf{SExp} \longleftrightarrow (\mathtt{Let}\ \texttt{"x"}\ (\mathtt{N}\ 5)\ (\mathtt{Plus}\ (\mathtt{Var}\ \texttt{"x"})\ (\mathtt{N}\ 2))) }}{\texttt{3 + let x = 5 in x + 2 end}\ \mathbf{SExp} \longleftrightarrow (\mathtt{Plus}\ (\mathtt{N}\ 3)\ (\mathtt{Let}\ \texttt{"x"}\ (\mathtt{N}\ 5)\ (\mathtt{Plus}\ (\mathtt{Var}\ \texttt{"x"})\ (\mathtt{N}\ 2))))}}
> $$

Typically this is computed by first doing the concrete syntax derivation, then filling the abstract syntax in from axioms down.

<div id="outline-container-orgeb3a77c" class="outline-2">
<h2 id="orgeb3a77c"><span class="section-number-2">2</span> Substitution</h2>
  <div class="outline-text-2" id="text-2"></div></div>


What is the result of the substitution in the following expressions? 


1. $\mathtt{Let}\ x\ (y.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ x)))[x:=y]$  

   > Capture is possible. Alpha renaming could be used to make this work:  $(\mathtt{Let}\ y\ (z.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ y)))$

2. $\mathtt{Let}\ y\ (z.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ z))[x:=y]$  

   > No effect: $(\mathtt{Let}\ y\ (z.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ z))$

3. $\mathtt{Let}\ x\ (z.\ (\mathtt{Plus}\ x\ z))[x:=y]$

   > $(\mathtt{Let}\ y\ (z.\ (\mathtt{Plus}\ y\ z))$

4. $\mathtt{Let}\ x\ (x.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ x))[x:=y]$  

   > Remember that a substitution only applies to the <i>free</i> occurrences of a variable, and only the first $x$ is free: $\mathtt{Let}\ y\ (x.\ (\mathtt{Plus}\ (\mathtt{Num}\ 1)\ x))$

<div id="outline-container-orgebc489b" class="outline-2">
<h2 id="orgebc489b"><span class="section-number-2">3</span> Semantics</h2>
  <div class="outline-text-2" id="text-3"></div></div>

You may want to look at the W3 Thursday notes before attempting these questions.  


A robot moves along a grid according to a simple program. 

The program consists of a sequence of commands <code>move</code> and <code>turn</code>, separated by semicolons,
with the command sequence terminated by the keyword <code>stop</code>:
$$
\mathcal{R} ::= \texttt{move};\ \mathcal{R}\ |\ \texttt{turn};\ \mathcal{R}\ |\ \texttt{stop}
$$
Initially, the robot faces east and starts at the grid coordinates <code>(0,0)</code>. The command <code>turn</code> causes the robot to turn 90 degrees counter-clockwise, and <code>move</code> to move one unit in the direction it is facing. 

<div id="outline-container-org40ae421" class="outline-3">
<h3 id="org40ae421"><span class="section-number-3">3.1</span> Denotational Semantics</h3>
  <div class="outline-text-3" id="text-3-1"></div></div>


 First, devise a suitable <i>denotational semantics</i> for this language. For this exercise, we are only interested in the final position of the robot, so the mathematical object which we associate to the sequence of instructions should merely be the final coordinates of the robot as a 2D vector.
$$
\llbracket \cdot \rrbracket : \mathcal{R} \rightarrow \mathbb{Z}^2
$$


> Remember from linear algebra that <a href="https://en.wikipedia.org/wiki/Rotation_matrix">rotation matrices</a> can be used to rotate a vector anticlockwise in the plane. For our purposes, we want $\theta = \pi/2$.
> $$
> \begin{array}{lcl}\llbracket \mathtt{turn}; r \rrbracket & = & \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}\llbracket r \rrbracket\\\llbracket \mathtt{move}; r \rrbracket & = & \llbracket r \rrbracket + \begin{pmatrix} 1 \\ 0 \end{pmatrix} \\\llbracket \mathtt{stop} \rrbracket & = & \begin{pmatrix} 0 \\ 0 \end{pmatrix}\end{array}
> $$

<div id="outline-container-orgc505bd3" class="outline-3">
<h3 id="orgc505bd3"><span class="section-number-3">3.2</span> Operational Semantics</h3>
<div class="outline-text-3" id="text-3-2">
</div>
<div id="outline-container-org617b6aa" class="outline-4">
<h4 id="org617b6aa"><span class="section-number-4">3.2.1</span> Small-Step Semantics</h4>
  <div class="outline-text-4" id="text-3-2-1"></div></div></div>


Next, we will devise a set of small-step semantics rules for this language. 

This means determining answers to the following questions:

1. What is the set of states?
2. Which of those states are final states, and which are initial states?
3. What transitions exist between those states?


> The set of states will be a triple $\mathbb{Z}^2 \times \mathbb{Z}^2 \times \mathcal{R}$ containing:
>
> > $\small\bullet$ The robot's current position,  
> > $\small\bullet$ A unit vector for the robot's facing direction, and  
> > $\small\bullet$ The current commands being executed  
>
> The initial states are all states where the robot faces east– $\begin{pmatrix}1 \\ 0\end{pmatrix}$ – at coordinates $\begin{pmatrix} 0 \\ 0 \end{pmatrix}$. 
> $$
> I = \left\{ \left(\begin{pmatrix} 0 \\ 0 \end{pmatrix}, \begin{pmatrix} 1 \\ 0 \end{pmatrix}, r\right)\ \Big\vert\ r\ \mathcal{R} \right\}
> $$
> The final states are those where the commands under execution are just <code>stop</code>.
> $$
> F = \left\{ (\mathbf{p}, \mathbf{d}, \texttt{stop})\ \vert\ \mathbf{p}, \mathbf{d} \in \mathbb{Z}^2 \right\}
> $$
> Lastly, the transition relation is specified by the following rules:  
> $$
> \dfrac{  }{ (\mathbf{p}, \mathbf{d}, \texttt{move}; r\mapsto  \left(\mathbf{p} + \mathbf{d}, \mathbf{d}, r\right) }
> $$
>
> $$
> \dfrac{  }{ (\mathbf{p}, \mathbf{d}, \texttt{turn}; r) \mapsto  \left(\mathbf{p}, \begin{pmatrix}0 & -1 \\ 1 & 0\end{pmatrix}\mathbf{d}, r\right) }
> $$

<div id="outline-container-org297905e" class="outline-4">
<h4 id="org297905e"><span class="section-number-4">3.2.2</span> Big-Step Semantics</h4>
  <div class="outline-text-4" id="text-3-2-2"></div></div>


Lastly, we will devise a set of big-step evaluation rules for this language.

This means determining answers to the following questions:

1. What is the set of evaluable expressions?
2. What is the set of values?
3. How do evaluable expressions evaluate to those values?


> The set of evaluable expressions is once again a triple of position, direction, and commands to execute – the same as the states in the small step semantics.  
>
> The set of values is a tuple of both the final position and direction of the robot after executing the program.  
>
> There are three rules to describe the evaluation:
> $$
> \dfrac{ }{(\mathbf{p}, \mathbf{d}, \texttt{stop} ) \Downarrow (\mathbf{p}, \mathbf{d})}
> $$
>
> $$
> \dfrac{ (\mathbf{p} + \mathbf{d},\mathbf{d}, r) \Downarrow (\mathbf{p'}, \mathbf{d'}) }{ (\mathbf{p}, \mathbf{d}, \texttt{move}; r) \Downarrow (\mathbf{p'}, \mathbf{d'}) }
> $$
>
> $$
> \dfrac{ \left(\mathbf{p},\begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \mathbf{d}, r\right) \Downarrow (\mathbf{p'}, \mathbf{d'}) }{ (\mathbf{p}, \mathbf{d}, \texttt{turn}; r) \Downarrow (\mathbf{p'}, \mathbf{d'}) }
> $$

<div id="outline-container-orgf7bd297" class="outline-2">
<h2 id="orgf7bd297"><span class="section-number-2">4</span> Lambda calculus and binding</h2>
<div class="outline-text-2" id="text-4">
</div>
<div id="outline-container-org9232c9d" class="outline-3">
<h3 id="org9232c9d"><span class="section-number-3">4.1</span> Reduction</h3>
  <div class="outline-text-3" id="text-4-1"></div></div></div>


Apply $\beta$ and $\eta$ reduction as much as possible to this term, until you reach a <i>normal form</i>. Where necessary, use $\alpha$ renaming to avoid capture.
$$
(\lambda n\ f\ x.\ f\ (n\ x\ x))\ (\lambda f\ x.\ f)
$$


> $$
> \begin{array}{lcl}(\lambda n\ f\ x.\ f\ (n\ x\ x))\ (\lambda f\ x.\ f) & \mapsto_\beta & (\lambda f\ x.\ f\ ((\lambda f\ x.\ f)\ x\ x))\\ & \equiv_\alpha & (\lambda f\ x.\ f\ ((\lambda f\ x'.\ f)\ x\ x))\\ & \mapsto_\beta  & (\lambda f\ x.\ f\ ((\lambda x'.\ x)\ x))\\ & \mapsto_\beta  & (\lambda f\ x.\ f\ x)\\ & \mapsto_\eta & (\lambda f.\ f)\\ \end{array}
> $$

<div id="outline-container-org00453a0" class="outline-3">
<h3 id="org00453a0"><span class="section-number-3">4.2</span> de Bruijn Indices</h3>
  <div class="outline-text-3" id="text-4-2"></div></div>

How would the above $\lambda$ term be represented in de Bruijn indices? Repeat the same reduction with de Bruijn indices.
$$
\begin{array}{lcl} (\lambda.\ \lambda.\ \lambda.\ \mathbf{1}\ (\mathbf{2}\ \mathbf{0}\ \mathbf{0}))\ (\lambda.\ \lambda.\ \mathbf{1}) & \mapsto_\beta & (\lambda.\ \lambda.\ \mathbf{1}\ ((\lambda.\ \lambda.\ \mathbf{1})\ \mathbf{0}\ \mathbf{0}))\\& \mapsto_\beta &(\lambda.\ \lambda.\ \mathbf{1}\ ((\lambda.\ \mathbf{1})\ \mathbf{0}))\\& \mapsto_\beta &(\lambda.\ lambda.\ \mathbf{1}\ \mathbf{0})\\& \mapsto_\eta &(\lambda.\ \mathbf{0})\end{array}
$$
