<div id="content">
<h1 class="title">Tute (Week 4)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#org4592640">1. TinyImp</a>
<ul>
<li><a href="#org4c4ca9d">1.1. Static semantics</a></li>
<li><a href="#orgd5f5efd">1.2. Associativity of sequential composition</a></li>
<li><a href="#orgc5f1590">1.3. A different looping construct</a></li>
</ul>
</li>
</ul>
  </div></div></div>
<div id="outline-container-org4592640" class="outline-2">
<h2 id="org4592640"><span class="section-number-2">1</span> TinyImp</h2>
<div class="outline-text-2" id="text-1">
</div>
<div id="outline-container-org4c4ca9d" class="outline-3">
<h3 id="org4c4ca9d"><span class="section-number-3">1.1</span> Static semantics</h3>
  <div class="outline-text-3" id="text-1-1"></div></div></div>
Ideally, static semantics judgements such as the $\mathbf{ok}$ judgements should allow us to make some predictions about the dynamic behaviour of the program. In this case, we'd hope that an $\mathbf{ok}$ program would be guaranteed
not to misbehave in some way.


1. Give an example of a program where all variables are initialised before use, but that is nonetheless not $\mathbf{ok}$

> > For example, this program:
> > $$
> > \begin{array}{l}\mathbf{var}\;x\;\cdot \\ \mathbf{if}\;1\;\mathbf{then}\\ \quad x:=1\\ \mathbf{else}\\ \quad \mathbf{skip}\\ \mathbf{fi}; \\ x := x + 1\end{array}
> > $$
> > We know that the else-branch will never be  aken, but the $\mathbf{ok}$ judgement doesn't take this into account.


Suppose we have proven that

$$
\emptyset;\emptyset\vdash s\;\mathbf{ok} \leadsto \emptyset
$$

1. The [W4 Tuesday notes](../Lecture/lec07/Imperative%20Programming%20Note.pdf) describe three different semantics for uninitialised variables: crash-and-burn, default values and junk data. Under each of these interpretations, state (informally, in English) some desirable property about the runtime behaviour of $s$ that follows as a result of the $\mathbf{ok}$ judgement above.

> > Under all of these semantics, we know that no variable is ever read or written outside its scope.  
> >
> > Under crash-and-burn semantics, an $\mathbf{ok}$ program will never have execution aborted by accessing an uninitialised variable.
> >
> > Under junk data semantics, an \mathbf{ok} program will have deterministic evaluation.
>


2. Can you think of a way to formalise these properties as logical statements involving judgements?
> > "No variable used outside its scope" can be stated syntactically as follows:
> > $$
> > \mathit{FV}(s) = \emptyset
> > $$
> > Semantically, we can say, e.g., that the result of evaluation doesn't depend on any of the free variables in the state:
> > $$
> > \forall \sigma,\sigma',x. (\sigma,s) \Downarrow \sigma' \;\Rightarrow\; (\sigma|_x,s) \Downarrow \sigma'|_x
> > $$
> > Deterministic evaluation can be stated as follows:
> > $$
> > \forall \sigma_1,\sigma_2,\sigma_3.\;(\sigma_1,s) \Downarrow \sigma_2 \;\wedge\; (\sigma_1,s) \Downarrow \sigma_3 \;\Rightarrow\; \sigma_2 = \sigma_3
> > $$
> > To say "no aborts due to uninitialised variables", it would be tempting to say that $s$ will evaluate to something:
> > $$
> > \forall \sigma. \exists \sigma'. (\sigma,s) \Downarrow \sigma'
> > $$
> > Unfortunately, this doesn't quite work. The reason is that there are $\mathbf{ok}$ programs that do not evaluate to any state, because they run forever (diverge). For example, we have
> > $$
> > \forall \sigma,\sigma'. \neg((\sigma,\mathbf{while}\ 1\ \mathbf{do}\ \mathbf{skip}\ \mathbf{od}) \Downarrow \sigma')
> > $$
> > This means that our big-step semantics is not adequate here, because it cannot distinguish divergence from failure.
> >
> > If we had a small-step semantics $\mapsto$ for TinyImp, we could state our desired property as follows: for all $\sigma$, every maximal trace starting from $(\sigma,s)$ is complete.

<div id="outline-container-orgd5f5efd" class="outline-3">
<h3 id="orgd5f5efd"><span class="section-number-3">1.2</span> Associativity of sequential composition</h3>
  <div class="outline-text-3" id="text-1-2"></div></div>
We never bothered specifying whether sequential composition in TinyImp is left-associative or right-associative. That is, whether $s_1;s_2;s_3$ should be evaluated as $(s_1; s_2); s_3$, or as $s_1; (s_2; s_3)$.

Prove that $(\sigma_1, (s_1;s_2);s_3) \Downarrow \sigma_2$ holds iff $(\sigma_1, s_1;(s_2;s_3)) \Downarrow \sigma_2$


> > We show only the $\Rightarrow$ direction. The $\Leftarrow$ direction is similar.
> >
> > Assume $(\sigma_1, (s_1;s_2);s_3) \Downarrow \sigma_2$. We proceed by case analysis on the derivation of this judgement. The only rule that is applicable is the sequential composition rule, which means there must exists a $\sigma_3$ such that
> > $$
> > (\sigma_1, s_1;s_2) \Downarrow \sigma_3 \qquad (1)
> > $$
> > and
> > $$
> > (\sigma_3, s_3) \Downarrow \sigma_2 \qquad (2)
> > $$
> > Further case analysis on the derivation of (1) yields that there must exists $\sigma_4$ such that
> > $$
> > (\sigma_1, s_1) \Downarrow \sigma_4 \qquad (3)
> > $$
> > and
> > $$
> > (\sigma_4, s_2) \Downarrow \sigma_3 \qquad (4)
> > $$
> > We can then complete the proof by constructing the following derivation:
> > $$
> > \dfrac{\dfrac{}{(\sigma_1, s_1) \Downarrow \sigma_4}(2)   \quad  \dfrac{         \dfrac           {}           {(\sigma_4, s_2) \Downarrow \sigma_3}(3)         \quad         \dfrac           {}           {(\sigma_3, s_3) \Downarrow \sigma_2}(4)        }       {(\sigma_1, s_2;s_3) \Downarrow \sigma_2} } {(\sigma_1, s_1;(s_2;s_3)) \Downarrow \sigma_2}
> > $$

<div id="outline-container-orgc5f1590" class="outline-3">
<h3 id="orgc5f1590"><span class="section-number-3">1.3</span> A different looping construct</h3>
  <div class="outline-text-3" id="text-1-3"></div></div>

Suppose we wanted to extend TinyImp with a new type of loop:
$$
\mathbf{do}\ s\ \mathbf{until}\ e
$$

Which, running the loop body $s$ at least once, checks the guard of the loop <b>after</b> the loop body has executed, terminating if it is true (i.e. nonzero).


1. Give big-step semantics rules for this construct in the style of the lecture slides.
> > $$
> > \dfrac{ (\sigma_1, s) \Downarrow \sigma_2 \quad \sigma_2 \vdash e \Downarrow v \quad v \neq 0  }{ (\sigma_1, \mathbf{do}\ s\ \mathbf{until}\ e) \Downarrow \sigma_2  }
> > $$
> >
> > $$
> > \dfrac{ (\sigma_1, s) \Downarrow \sigma_2 \quad \sigma_2 \vdash e \Downarrow 0 \quad (\sigma_2, \mathbf{do}\ s\ \mathbf{until}\ e) \Downarrow \sigma_3   }{ (\sigma_1, \mathbf{do}\ s\ \mathbf{until}\ e) \Downarrow \sigma_3  }
> > $$

2. Propose a translation of this construct into existing TinyImp constructs.
> > $$
> > \mathbf{do}\ s\ \mathbf{until}\ e \equiv s; \mathbf{while}\ \neg e\ \mathbf{do}\ s\ \mathbf{od}
> > $$

3. Validate your translation by showing that the Hoare logic rule for this loop is derivable for your translation:

$$
\dfrac{ \{ \varphi \}\ s\ \{ \varphi \}  }{\{ \varphi \}\ \mathbf{do}\ s\ \mathbf{until}\ e\ \{ \varphi \land e \} }
$$

> > $$
> > \dfrac{ \dfrac{ }{\{ \varphi \}\ s\ \{ \varphi \}}\quad    \dfrac{       \dfrac{ \dfrac{ \dfrac{}{\{ \varphi \}\ s\ \{ \varphi \}  }  }{ \{ \varphi \land \neg e \}\ s\ \{ \varphi \}  }\text{Con}           }{\{ \varphi \}\ \mathbf{while}\ \neg e\ \mathbf{do}\ s\ \mathbf{od}\ \{ \varphi \land \neg (\neg e) \}}\text{Loop}         }{\{ \varphi \}\ \mathbf{while}\ \neg e\ \mathbf{do}\ s\ \mathbf{od}\ \{ \varphi \land e \}}\text{Con}  }{\{ \varphi \}\  s; \mathbf{while}\ \neg e\ \mathbf{do}\ s\ \mathbf{od}\ \{ \varphi \land e \} }\text{Seq}
> > $$

