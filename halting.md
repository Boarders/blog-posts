---
title: "The Halting Problem in Haskell"
author: "Callan McGill"
# tags: ["Partial Types", "Haskell", "Halting Problem"]
categories:
  - posts
date: "2020-03-03"
draft: false
mathjax: true
---

The halting problem says (informally) that there is no algorithm which for any generally recursive program with arbitrary input tells us whether that program terminates. This is usually formalised by first picking some specific theory of computation and then showing within that theory that no such program can be written. For example, in the setting of the untyped lambda calculus this can be stated as follows:


**Theorem ($\lambda$-halting)**: There does not exist a $\lambda$-term
$\def\h{\mathrm{h}} \def\l{\mathrm{l}} \def\true{\mathrm{true}} \def\false{\mathrm{false}} \h$ such that $(\mathrm{h} \; \mathrm{L})$ evaluated to $\true$ precisely when $\mathrm{L}$ terminates (meaning here, that there exists some  finite sequence of $\beta$-reductions under which $\mathrm{L}$ reduces to a normal form).

Let us try to prove this fact (the arguments here taken from the paper _Computational foundatios of basic recursive function theory_ by Constable and Smith) . Consider the fixed-point $\def\Y{\mathrm{Y}} \Y$-combinator. This is defined as:

$$
\def\mr#1{\mathrm{#1}}
\def\la#1{\lambda \; \mathrm{#1} \; . \; }
\def\ap#1#2{\mathrm{#1} \; {\mathrm{#2}}}
\def\be{\mapsto_{\beta}}
\Y = \la{f} \ap{(\la{x} \ap{f}{(\ap{x}{x})})}{(\la{x} \ap{f}{(\ap{x}{x})})}
  $$

The key property this satisfies, is that for any lambda term $\rm{g}$ we have that $(\ap{\Y}{\rm{g}})$ is a fixed point for $\rm{g}$ in the sense that $\ap{g}{(\ap{\Y}{g})}$ is $\beta$-equivalent to $\ap{\Y}{g}$. This is easy to observe as follows:

$$
\ap{\Y}{g} \be \ap{(\la{x} \ap{g}{(\ap{x}{x})})}{(\la{x} \ap{g}{(\ap{x}{x})})}
 \be \ap{g}{\ap{(\la{x} \ap{g}{(\ap{x}{x})})}{(\la{x} \ap{g}{(\ap{x}{x})})}}
 \equiv_{\beta} \ap{g}{(\ap{Y}{g})}
  $$

Now in order to prove this theorem let us consider the consider the terms:
$$
  \bot = \ap{Y}{(\la{x}x)}
  $$
$$
  \rm{p} = {\la{n}\text{if $(\ap{h}{n})$ then $\bot$ else true}}
  $$
$$
  \rm{d} = \ap{Y}{p}
  $$
Let us think about the value of $\rm{h}$ on this (admittedly rather mysterious) term $\rm{d}$.

  - if $\ap{h}{d}$ is $\rm{true}$ then we note that:
  $$
     \rm{d} \equiv_\beta \ap{p}{d} :\equiv \text{if $(\ap{h}{d})$ then $\bot$ else true} \mapsto \bot
    $$
    We therefore have that $\rm{d}$ does not terminate and so $\ap{h}{d}$ is false.

  - Simlarly if $\ap{h}{d}$ is $\rm{false}$ then:
    $$
     \rm{d} \equiv_\beta \ap{p}{d} :\equiv \text{if $(\ap{h}{d})$ then $\bot$ else true} \mapsto \text{true}
    $$
    and so we get that $\rm{d}$ terminates and so we should have $\ap{h}{d}$ is true.

In order to make this argument perhaps more concrete, let us consdier what it looks like in a typed setting with Haskell's concrete syntax. Note that in Haskell all types are _partial_ (using some distortion of Constable's terminology). This means that every type is inhabited by some non-terminating term which is typically denoted $\bot$ (analogous to the term considered above). Let us then reformulate a version of the above theorem in terms of Haskell types.

**Theorem (haskell-halting)**: In Haskell there is no function $\rm{h}$ with the following behaviour:
```haskell
h :: Nat -> Nat
h ⊥ = 0
h _ = 1
```
  
This is not legal Haskell and we are claiming this fact cannot be remedied. More precisely, the above says that there is no Haskell function on the natural numbers which determines whether the input is, in fact, a diverging computation. This may seem far away from the Halting problem insomuch as we are only considering the natural numbers but we can observe that for any $\rm{f} :: \rm{Nat} \rightarrow \rm{Nat}$ we can compute $\ap{h}{(\ap{f}{n})}$ to determine if $\rm{f}$ halts on input $\rm{n}$ and so this would indeed determine those inputs for which $\rm{f}$ halted.

In order to mimic the argument above we need to introduce a fixed point function which we can do as follows:
```haskell
{-# LANGUAGE ScopedTypeVariables #-}

fix :: forall a . (a -> a) -> a
fix f = let x = f x in x
```
We can then define once and for all a non-terminating term inhabiting all (concrete) types:
```haskell
bottom :: forall a . a
bottom = fix id
```

We note that $\rm{fix}$ satisies precisely the same property as $\Y$, namely:
$$
  \ap{f}{(\ap{fix}{f})} \equiv_\beta \ap{fix}{f}
  $$
This is perhaps best explained by thinking about how $\rm{letrec}$ gets elaborated into the lambda calculus:
$$
  \text{letrec x} = \text {f in g}  \rightsquigarrow \ap{(\la{x}g)}{(\ap{Y}({\la{x}f}))}
  $$

We can think of this as substituting the $\rm{x}$ fixed point of $\rm{f}$ into the body $g$ (without first evaluating the fixed point itself as we are in a call-by-need/call-by-name context). We can then see that $\rm{fix}$ does indeed have the above behaviour:
$$
  \ap{fix}{g} = (\text{letrec x} = \text{g x in x}) \rightsquigarrow \ap{(\la{x} x)}{(\ap{Y}{\la{x}\ap{g}{x}})} \mapsto \ap{Y}{(\la{x} \ap{g}{x})} = \ap{g}{(\ap{Y}{g})} = \ap{g}{(\ap{fix}{g})}
  $$

This explains that fix does indeed deserve its namesake but doesn't necessarily elucidate its general usage. In fact having such a fixed-point function in a programming language is enough to give us general recursion. For example here is how we can define a sum over lists:
```haskell
{-# LANGUAGE LambdaCase #-}

sumR :: forall n . (Num n) => ([n] -> n) -> ([n] -> n)
sumR tailFn = \case
  []     -> 0
  (x:xs) -> x + r xs

mySum :: forall n . (Num n) => ([n] -> n)
mySum = fix sumF
```
```shell
> mySum [1..100]
5050
```

To further understand how this works I recommend [this lovely blog post](https://www.parsonsmatt.org/2016/10/26/grokking_fix.html) by Matt Parsons.


Let us now recast our terms from earlier into Haskell:
```haskell
p :: Natural -> Natural
p n = if h n == 0 then 1 else bottom

problem :: Natural
problem = fix p
```

As above let us think about the value of $(\ap{h}{problem})$:
```haskell
problem ≡ fix p ≡ p (problem) ≡ if h problem == 0 then 1 else bottom
```

We note again that:
  
  - If $\ap{h}{problem}$ is $0$ then it is 1.
  
  - If $\ap{h}{problem}$ is $1$ then it is 0.


We therefore conclude that no such $\rm{h}$ can be written in Haskell and so we cannot tell (in general) whether a particular term of type nat will diverge or not.


