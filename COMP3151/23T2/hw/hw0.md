<center><font size=6pt>COMP3151/9154 Tutorial 1</font> </center>
<center><font size=6pt>Review of Discrete Mathematics</font></center>

The following are some of the concepts that are likely to come up in the course, which it is assumed that you have previously acquired from a Discrete Mathematics class. (There are a few references to material from Lecture 1)

-  **Sets**:  Evaluate the following expressions, where $A=\{1,2,3,4\}$, and $B=\{2, 4, 7\}$
    1. $A\cap B = \{2, 4\}$
    1. $A\cup B=\{1, 2, 3, 4, 7\}$
    1. $A\setminus B = \{1, 3\}$
    1. $\{S\in \mathcal{P}(A)\ |\ \{1, 2\}\subseteq S\} = \{\{1, 2\},\ \{1, 2, 3\},\ \{1, 2, 4\},\ \{1, 2, 3, 4\}\}$
    1. $\{(x, y)\in A\times B\ |\ x < y\} = \{(1, 2),\ (1, 4),\ (1, 7),\ (2, 4),\ (2, 7),\ (3, 4),\ (3, 7),\ (4, 7)\}$ 


- **Functions**:  What is the function $g$ such that
  $$
  |\{f\ |\ f:A\rightarrow B\}|=g(|A|, |B|)\ ?
  $$
  We can think of the smallest infinite number ω as the set $\{ 0, 1, 2, . . .\}$ of all natural numbers. Explain why we also write $B^A$ for $\{f\ |\ f : A \rightarrow B\}$ , and write $\Sigma^\omega$ for the set of all infinite sequences of elements of $\Sigma$.

- **Relations**:  For $R = \{ (1, 2), (2, 1), (1, 1)\}$ , are the following TRUE or FALSE?

  1. $R \subseteq R \circ R$ 

     (Here $R_1 \circ R_2 = \{ (x, z )\ |\ (x, y ) \in R_1 \wedge (y, z ) \in R_2\}$.)

  2. $R$ is reflixive (as a relation over the set $\{ 1, 2\}$ ). 

     > Reflixive: $\forall\ a \in A, (a, a) \in R$

  3. $R$ is transitive.

     > Transitive: $\forall\ a, b, c \in A$, If $(a, b)\in R$ and $(b, c)\in R$, $(a, c)\in R$

  4. $R$ is antisymmetric.

     > Antisymmetric: $\forall\ a, b \in A$, If $(a, b)\in R$ and $(b, a)\in R$, $a=b$

  5. $R$ is symmetric. 

     > Symmetric: $\forall a, b \in A$, If$(a, b)\in R$, $(b, a)\in R$

  6. $R$ is a partial order over the set $\{ 1, 2\}$.

     > Partial Order: Satisfy **Transitive, Antisymmetic, Symmetric**

  7. For every nonempty set $A$ , the relation $\subseteq$ on $\mathcal{P} (A )$ is a partial order.

  8. For every nonempty set $A$, the relation $\subseteq$ on $\mathcal{P} (A )$ is a total order.

- **Inductive Definitions**:  Suppose that S is the smallest set X of natural numbers such that

  (a) $2 \in X$,

  (b) If $n \in X$ then $n^2 \in X$,

  (c) If $n \in X$ and $m < n$ then $m \in X$.

  Describe the set $S$ explicitly, i.e without using an inductive definition. What is the set $X$ if we replace the condition (a) by the following condition,
  $$
  (a’)\ 1 \in X
  $$
  but do not change conditions (b) and (c)?

-  **Propositional Logic**:  Construct a truth table for the following formula of propositional logic:

$$
(\not A \lor B) \Leftrightarrow (A \Rightarrow B)
$$
- **Inductive Definitions**:  Given a set of atomic propositions $Prop$, give an inductive definition of the set of formulas of propositional logic using the operators $\land$ and $\lnot$˛ and atomic propositions $Prop$.

- **Enumerability**:  Let $Prop$ be a finite set of propositions. Is the set of all formulas of propositional logic formulas over Prop enumerable (countable)?

- **Propositional Logic Semantics as a Relation**:  We can represent a propositional assignment (line of the truth table) over a set of atomic propositions $Prop$ as a set $\pi \in Prop$, with $p\in \pi$ meaning, intuitively, that $\pi$ says that the atomic proposition $p$ is true.

  The *satisfaction relation* for propositional logic is the binary relation $\vDash$ between propositional assignments $\pi$ and formulas $\phi$ of propositional logic, such that $\pi \vDash \phi$ if the formula $\phi$ evaluates to True when the atomic propositions have the truth vaues assigned by $\pi$. For example, if $p \notin \pi$ and $q\in \pi$, then $\pi \vDash (\lnot p)\land q$.

  Give an inductive definition of the relation $\vDash$. ( It is enough to cover formulas containing only the operators $\lnot$ and $\land$, since all other boolean operators can be defined in terms of these two.)

- **Predicate Logic**: Are the following formulae TRUE or FALSE?
  1. $\forall x \in \mathbb{N}\ \exist y \in \mathbb{N}\  [x ∗ y = y]$
  2. $\exist x \in \mathbb{N}\ \forall y \in \mathbb{N}\  [x ∗ y = x]$
  3. $\forall x ∈ \mathbb{N}\ \forall y ∈ \mathbb{N}\  (x < y → \exist z \in \mathbb{N}\ [z > 0 \land y = x + z])$

- Using quantifiers $\lor$, $\exist$, translate the following into logical notation:
  1. All natural numbers greater than 3 are greater than 2.
  2. There exists a natural number greater than 3 that is greater than 2.
  3. Some natural numbers are in all sets containing 1.
  4. For every time I am awake, there will be a later time when I am sleeping or dead.