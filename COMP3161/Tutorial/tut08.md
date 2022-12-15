<div id="content">
<h1 class="title">Tute (Week 9)</h1>
<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orgf513040">1. Type Inference</a>
<ul>
<li><a href="#orgcd811d2">1.1. Examples</a></li>
<li><a href="#org6d594a6">1.2. Inference Algorithm</a></li>
</ul>
</li>
<li><a href="#org586ff45">2. Existential Types</a></li>
<li><a href="#orgecd58e0">3. Monadic programming</a></li>
</ul>
</div>
</div>
<div id="outline-container-orgf513040" class="outline-2">
<h2 id="orgf513040"><span class="section-number-2">1</span> Type Inference</h2>
<div class="outline-text-2" id="text-1">
</div>
<div id="outline-container-orgcd811d2" class="outline-3">
<h3 id="orgcd811d2"><span class="section-number-3">1.1</span> Examples</h3>
  <div class="outline-text-3" id="text-1-1"></div></div></div></div>
What is the most general type of the following implicitly-typed MinHs expressions? 

What would their explicitly-typed equivalents be?

1. <code>recfun f x = ((fst x) + 1)</code>
> > <code>type a. recfun f :: (Int * a -> Int) x = ((fst@Int@a x) + 1)</code>
2. <code>InL (InR True)</code>
> > <code>type a. type b. InL@(b + Bool)@a (InR@b@Bool True)</code>

3. <code>recfun f x = if (fst x) then (snd x) else f x</code>
> > <code>type a. type b. InL@(b + Bool)@a (InR@b@Bool True)</code>

4. <code>recfun f x = if (fst x) then (InL x) else (InR x)</code>
> > <code>type b. recfun f x = if (fst@Bool@b x) then (InL@(Bool * b)@(Bool * b) x) else (InR@(Bool * b)@(Bool * b) x)</code>

<div id="outline-container-org6d594a6" class="outline-3">
<h3 id="org6d594a6"><span class="section-number-3">1.2</span> Inference Algorithm</h3>
  <div class="outline-text-3" id="text-1-2"></div></div>
In the lecture, we introduced two sets of typing rules for an implicitly typed variant of MinHs. Explain the difference between these rules. 

Derive the type of 
$$
\mathtt{Apply}\ (\mathtt{Recfun}\ (f.x.\ \texttt{Pair}\ x\ x))\ 5)
$$
using both sets of inference rules. 
> The first set of rules don't specify an algorithm, as several rules require us to guess what types to put in the context, and several other rules (forall introduction and elimination) can be applied at any time. 
>  
> The second set of rules fixed that problem by allowing unification variables to occur inside types, standing for types that are not yet known. As we do type checking, whenever we want two types to be equal, we find a substitution to the unification variables such that the types become the same. In this way, as we complete type checking, we will generate a substitution that, when applied to the types, will produce the most general type for a given term.  
> 
> Here's a derivation by Liam using the algorithmic rules:  
> 
> https://www.youtube.com/watch?v=sQKOstGLe5Y

<div id="outline-container-org586ff45" class="outline-2">
<h2 id="org586ff45"><span class="section-number-2">2</span> Existential Types</h2>
  <div class="outline-text-2" id="text-2"></div></div>
  
Existential types are often over-used in languages that support them. 
For each of the following existential types, propose a non-existential type
that could be used instead:
1. $\exists t.\ t \times (t \rightarrow \texttt{String})$ 

> > <code>𝚂𝚝𝚛𝚒𝚗𝚐</code> , seeing as consumers of the data type can only produce one string from a value of that type.


2. $\exists t.\ t \times (\texttt{Int} \times t \rightarrow t)$
> > $\mathbf{1}$, seeing as there is no way to extract any information from that data type.

3. $\exists t.\ (t \rightarrow t \times t) \times (t \times t \rightarrow t)$
> > $\mathbf{1}$, seeing as there is no way to extract any information or indeed to construct an instance of the abstract data type.

<div id="outline-container-orgecd58e0" class="outline-2">
<h2 id="orgecd58e0"><span class="section-number-2">3</span> Monadic programming</h2>
  <div class="outline-text-2" id="text-3"></div></div>
Let's use the list monad! We're revisiting this puzzle from the very first lecture:


```
1    2    3    4    5
  🕁   🕁   🕁   🕁   🕁

A mole is disturbing a row of five graves. The mole is always
underneath one of the graves.

1. Each day, we may attempt to catch the mole by
   digging up a grave. If we found the mole, we win;
   otherwise, we put the grave back in order and go to sleep.
2. Each night, the mole must move from its current position to an
   adjacent grave.

Find a sequence of digs that is guaranteed to find the mole.
```


1. Write a function <code>move_mole : Int -&gt; [Int]</code> such that, if the mole is at grave <code>n</code> initially, <code>move_mole n</code> is the list of graves the
mole might be at after its nightly move.
> > ```haskell
> > move_mole :: Int -> [Int]
> > move_mole 1 = [2]
> > move_mole 5 = [4]
> > move_mole n = [n-1,n+1]
> > ```
2. Write a function <code>kill_mole : Int -&gt; Int -&gt; [Int]</code>. If we dig at grave <code>d</code>, and the mole is at position <code>m</code>, <code>kill_mole d m</code> should return the empty list if we found the mole, and <code>[m]</code> if the mole is still at loose.

> > ```haskell
> > kill_mole :: Int -> Int -> [Int]
> > kill_mole n m = if n == m then [] else [m]
> >```

3. Let's define the list monad! Write Haskell functions that inhabit the following type signatures, and think about whether they satisfy the monad laws:

```haskell
myReturn :: a -> [a]
myBind   :: [a] -> (a -> [b]) -> [b]
```
> > ```haskell
> > myReturn x = [x]
> > myBind xs f = concat(map f xs)
> > ```
> > We can check the monad laws algebraically as follows (doing this in the tute might be overkill):
> > ```haskell
> > return x >>= f =
> > concat (map f [x]) =
> > concat([f x]) =
> > f x
> > 
> > xs >>= return =
> > concat (map return xs) =
> > xs
> > 
> > xs >>= (\x -> f x >>= g) =
> > concat (map (\x -> f x >>= g) xs) =
> > concat (map (\x -> concat (map g (f x))) xs) =
> > concat (map (concat . map g . f) xs) =
> > concat (map concat (map (map g . f) xs)) =
> > concat (concat (map (map g . f) xs)) =
> > concat (concat (map (map g) (map f xs))) =
> > concat (map g (concat (map f xs))) =
> > concat (map g (xs >>= f)) =
> > (xs >>= f) >>= g
> > ```
> > The last derivation here uses the free theorems of <code>map</code> and <code>concat</code>, eta-equivalence, and the fact that <code>concat(concat l) = concat(map concat l)</code>


4. Here's an implementation of a <code>move</code> function for following a sequence of moves. If the mole is initially at position <code>m</code>, and we perform the sequence of digs <code>xs</code>, then <code>move xs m</code> is the list of final positions the mole could be at. (The final result may contain duplicates but we don't care.) Can you use the list monad (either the one you just defined, or the built-in one in Haskell) to simplify it?

```haskell
move :: [Int] -> Int -> [Int]
move [] m = [m]
move (x:xs) m =
  let ys = kill_mole x m
      zs = concat (map move_mole ys)
  in
    concat (map (move xs) zs)
```

> > ```haskell
> > move :: [Int] -> Int -> [Int]
> > move (n:ns) pos =
> >   do
> >     pos' <- kill_mole n pos
> >     pos'' <- move_mole pos'
> >     move ns pos''
> > move [] pos = return pos
> > ```

5. Using <code>do</code> notation and <code>move</code>, write a function <code>play : [Int] -&gt; [Int]</code>
that returns the possible final locations of the mole after we've performed a sequence of moves, regardless of the mole's initial position.

> > ```haskell
> > play xs =
> >   do
> >     pos <- [1,2,3,4,5]
> >     move xs pos
> > ```