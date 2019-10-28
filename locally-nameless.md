---
title: "Locally Nameless"
author: "Callan McGill"
# tags: ["Type theory", "Lambda Calculus", "Haskell", "Substitution"]
categories:
  - posts
date: "2019-10-27"
draft: false
mathjax: true
---

The untyped lambda calculus has a very simple grammar with just three term formers:

$$ \mathrm{term}
 \mathrel{\vcenter{\hbox{::}}{=}} v \;
  | \; \lambda \; v \; . \; \mathrm{term} \;
  | \; \mathrm{term} \; \mathrm{term} \;
  $$

Or in Haskell:

```haskell
data Lam a where
  Var :: a -> Lam a
  Lam :: a -> Lam a -> Lam a
  App :: Lam a -> Lam a -> Lam a
```

In order that this work as a theory of computation, we need some notion of evaluation and this is driven by $\beta$-reduction. The standard jargon in lambda caluclus is to say that a $\beta$-redux is any subterm of the form $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$. On such a $\beta$-redux we can then step via (capture-avoiding) substitution:

$$ (\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}
    \rightsquigarrow
   f\;[x  \mathrel{\vcenter{\hbox{:}}{=}} \mathrm{arg}]
  $$

Formally we then extend this to a congruence relation on Lambda terms via rules of the form:

$$
  M \rightsquigarrow M' \Rightarrow M N \rightsquigarrow M' N
$$
$$
  N \rightsquigarrow N' \Rightarrow M N \rightsquigarrow M  N'
  $$

Precisely how we choose to set up these rules to give a computational semantics to our language corresponds
algorithmically to a choice of evaluation strategy. As such, this opens up myriad interesting questions related to order of evaluation and normal forms and so on. Instead we will largely bypass these considerations and concentrate on the more humdrum (but no less vital) matter of the practicalities of performing such capture-avoiding substitutions. The basic problem with too naive an approach is as follows:

$$ (\lambda \mathrm{x} \; . \; \lambda \; y \; . \;  x) \; \mathrm{y}
    \rightsquigarrow
   (\lambda \mathrm{y} \; . \; y \;)
  $$

Here we have substituted the _free_ variable y into our lambda term and it has become _bound_. This is semantically incorrect: the names of free variables are meaningful because, in spirit, they refer to names we have defined elsewhere (that is, they can be looked up within a context, or, in other words, they are _open_ for further substitution). Conversely, the names of bound variables are, computationally speaking, unimportant. In fact, it is usual to refer to the grammar we have introduced earlier as _pre-lambda terms_ and to take lambda terms as referring to the equivalence classes under $\alpha$-equivalence. This refers to the (equivalence) relation whereby two terms are equivalent if we can consistently rename the bound variables of one to obtain the other (here too we need to take care, $\alpha$-renaming $\mathrm{x}$ to $\mathrm{y}$ in the above term would lead to a different sort of variable capture). Most accounts of $\alpha$-equivalence are themselves intimiately tied up with the question of how to perform substitution (and locally nameless is no different in this respect).

In practice this means that in order to compute  $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$ we would first $\alpha$-rename $\mathrm{x}$ to a variable that is neither already named within $\mathrm{f}$, nor appears free within $\mathrm{arg}$. Carrying out such a procedure by brute force is workable, but tends to be rather error-prone. A straightforward approach along these lines is described in [this excellent post](http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html) by Lennart Augustsson. 

There are a [whole host](https://www.schoolofhaskell.com/user/edwardk/bound) of more sophisticated methods for dealing with the problem of capture-avoiding substitution. Perhaps one of the best known is to use De-Bruijn indices. The idea here is to replace all bound variables by a natural number. This indicates the variable's distance from its binding site. All free variables are then represented by distinct natural numbers greater than the maximum depth of any binding site in the term. We then keep track of these variables within the environment under which computation is performed. For instance, the following is how one might translate a typical term into De-Bruijn indices:

$$ (\lambda \mathrm{x} \; . \; \lambda \; y \; . \;  x \; z)
    \longrightarrow
   (\lambda \; \lambda \; . \; 1 \; 3 \;)
   $$
  $$
   [z \mapsto 3]
  $$

Here we keep both the translated lambda term but also the context for how to read free variables.

This approach offers two key advantages:

  * Capture avoiding substitution becomes a matter of keeping binding distance arithmetic in check.
  * The De-Bruijn representation gives canonical representatives for $\alpha$-equivalence classes, thus allowing us to test for $\alpha$-equivalence via syntactic equality of terms.

On the other hand, Bob Atkey has, rather aptly, referred to the ability to read terms written with DeBruijn indices as a "cylon detector". What we gain in ease of implementation we give in much worse readability.

Instead we turn to the hybrid approach in the paper [I Am Not a Number -- I am a Free Variable](http://www.cs.ru.nl/~james/RESEARCH/haskell2004.pdf). Let us keep free variables free and use De-Bruijn indices only for bound variables:


```haskell
-- Our variable type keeps the old free variables and uses
--integers to represent bound variables.
data Var a
  = F a
  | B Int

-- Locally nameless terms will be the same lambda terms with
-- variables now labelled either bound or free.
type LocallyNameless a = Lam (Var a)
```

Notice how, because we use the same lambda terms with this representation, we still have names at binders. This is useful as we can recover the named term we started out with, carrying along all such names as we perform work. Here is how we convert between the two representations:

```haskell
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Data.Map as M
{-
[...]
-}
toLocallyNameless :: forall a . (Ord a) => Term a -> Term (Var a)
toLocallyNameless = go mempty
  where
    go :: Map a Int -> Term a -> Term (Var a)
    go env = \case
      Var a  ->
      -- we check if our variable has been bound elsewhere
        case a `lookup` env of
          Just bv -> Var (B bv)
          Nothing -> Var (F a)
      App l r -> App (go env l) (go env r)
      Lam n e ->
        let
       -- As we have gone under a binder we bump each variable
       -- by 1, inserting our newly bound variable at 0.
          env' = insert n 0 (M.map (+ 1) env)
        in
          Lam (F n) (go env' e)

fromLocallyNameless :: forall a . (Ord a) => Term (Var a) -> Term a
fromLocallyNameless = go mempty
  where
    go :: Map Int a -> Term (Var a) -> Term a
    go env = \case
      Var v ->
        case v of
          F a  -> Var a
               -- we look up our bound variable with the name we collected from
               -- its binder
          B bv -> case bv `lookup` env of
            Just name -> Var name
            Nothing   -> error $ "Found bound variable :" <> show bv <> " without binder."
      App l r -> App (go env l) (go env r)
      Lam n e ->
        case n of
       -- if our lambda term has a Bound variable at a binding site something
       -- has gone horribly wrong
          B bv -> error $ "Found unnamed variable at binding site" <> show bv
          F v  ->
            let
           -- We store the name of the binder in the environment
              env' = insert 0 v (mapKeysMonotonic (+ 1) env)
            in
              Lam v (go env' e)
```

Now let's see that this works as expected (this is, for me, a worrying amount of bookeeping to leave to "Looks good!"). Let us use quickcheck to see that __fromLocallyNameless__ is a left inverse to __toLocallyNameless__:

``` haskell
import Test.Tasty.QuickCheck as QC
{-
[...]
-}
-- We use a somewhat unprincipled approach to generating arbitrary terms
-- but for our purposes it will do the job.
instance Arbitrary a => Arbitrary (Lam a) where
  arbitrary =
    do
      i <- choose (0,10)
      buildTerm i
    where
      buildTerm :: Int -> Gen (Term a)
      buildTerm i
        | i <= 2    = arbitrary >>= pure . Var
        | i <= 8    = Lam <$> arbitrary <*> arbitrary
       -- so that our terms don't explode we limit
       -- the amount of branching we allow
        | otherwise = App <$> arbitrary <*> arbitrary

-- |
-- fromLocalyNameless is a left inverse to toLocallyNameless.
fromLocallyNamelessLeftInverse :: (Ord a, Show a) => Lam a -> Property
fromLocallyNamelessLeftInverse e =
  (fromLocallyNameless . toLocallyNameless) e === e

```

Thankfully, this does indeed work as expected:
```shell
Tests
  Property Tests
    fromLocallyNameless ∘ toLocallyNameless == id: OK (0.35s)
      +++ OK, passed 1000 tests.
```

Now that we have terms in locally nameless representation, we can perform substitution in a fairly straightforward manner. In the McBride--McKinna (MK) paper, they refer to this operation as __"instantiate"__. It is also common in the locally nameless literature to call the operation __"opening"__ or __"open"__ because it involves opening the body of a term to substitute for its outermost bound variable. As this accords with our intuitions on the meaning of substitution of locally nameless terms, we will follow this convention.

Note that in the code below, we follow (at least in spirit) the MK approach of using a scope type to denote a term that is only legal as the body of an expression (i.e. a term which may have bound variables referring to a non-existant outer binder such as $\lambda \; . \; 1$). In our case, we
only use a type synonym; however, in a more substantial implementation, one should use a newtype to get the type safety that such a measure confers.
```haskell
type Scope f x = f x
                    -- ┌─── term we are substituting
                    -- │
                    -- │                 ┌─── body we are substituting into
                    -- │                 │
                    -- │                 │
open :: forall a . Term (Var a) -> Scope Term (Var a) -> Term (Var a)
open image = go 0 -- the bound variable begins at 0
  where
    go :: Int -> Term (Var a) -> Term (Var a)
    go outer =
      \case
        Var fbv ->
          case fbv of
         -- if the bound variable refers to the outer binder of the body
         -- of the term then we substitute the image.
            B bv | bv == outer -> image
                 | otherwise   -> Var (B bv)
            F fv -> Var (F fv)
        App l r -> App (go outer l) (go outer r)
                -- Note that as we have gone under another binder we must
                -- in turn bump the binding variable we substitute for
                -- so that it still refers to the outermost binder.
        Lam n b -> Lam n (go (outer + 1) b)
```

From here it is easy for us to implement reduction to both normal form and weak-head normal form (where we use call-by-name semantics). We will, in both cases, write a function that does all of the work using locally nameless terms and functions that make use of that work on named lambda terms
via the previously defined conversion functions:

```haskell
whnfLN :: Term (Var a) -> Term (Var a)
whnfLN term = go term []
  where
              -- ┌─── current leftmost lambda term
              -- │
              -- │             ┌─── list of collected arguments
              -- │             │
              -- │             │
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (t, as) of
        ((App l r), args)
          -- if we encounter an application then we collect the
          -- argument on the right and recurse into the left term
          -> go l (r : args)
     -- We only perform substitution if we have both
     -- a non-empty list of arguments to substitute and
     -- a leftmost lambda term.
        ((Lam _ body) , a:args)
          -- Note that we substitute the body before evaluation
          -- and hence we follow call-by-name semantics.
          -> go (substitute a body) args
        _
          -- otherwise we encountered no further leftmost
          -- lambda terms and so we re-apply App to the
          -- built-up list of arguments
          -> foldl' App t as


whnf :: (Ord a) => Term a -> Term a
    -- defer the work to the locally nameless terms
whnf = fromLocallyNameless . whnfLN . toLocallyNameless


nfLN :: Term (Var a) -> Term (Var a)
nfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (t, as) of
        ((App l r), args)
          -- the same as above we collect right arguments in a list.
          -> go l (r : args)
      -- If we have no arguments to apply to a lambda then we
      -- recurse into the body (this is the difference between
      -- normal form and weak head normal form).
        ((Lam n body) , [])
          -> (Lam n (nfLN body))
        ((Lam _ body) , a:args)
          -> go (substitute a body) args
        _
          -- If we encounter no further lambdas then we reduce each of our built-up
          -- arguments before re-applying App.
          -> foldl' App t (fmap nfLN as)


nf :: (Ord a) => Term a -> Term a
  -- again we defer all the actual work to locally nameless terms.
nf = fromLocallyNameless . nfLN . toLocallyNameless
```

Now that we have written this reduction code, we should test it. But what on? A natural choice is to consider church encodings of the natural numbers. Since all we have in the lambda calculus is a theory of functions (with no base data types), we must encode any data in the form of functions. Church numerals act as a prototypical example of such an encoding:


$$ \mathrm{zero} = \lambda \; \mathrm{s} \; . \; \lambda \; \mathrm{z} \; . \; \mathrm{z} $$
$$ \mathrm{succ}\; \mathrm{n} = \lambda \; \mathrm{s} \; . \; \lambda \; \mathrm{z} \; . \; \mathrm{s} \; (\mathrm{n} \; \mathrm{s} \; \mathrm{z}) $$

The idea here is that zero takes as arguments a step function $\mathrm{s}$ and a starting value $\mathrm{z}$, returning the starting value. A positive number n, on the other hand, takes those arguments and applies the step function to the starting value n times. Here is what this looks like using our named terms:

```haskell
{-# LANGUAGE OverloadedStrings #-}
-- [...]
-- We give ourselves some handy infix syntax for apply.
infixl 5 .$
(.$) :: Term a -> Term a -> Term a
(.$) = App

-- |
-- The unary natural numbers.
data Nat = Z | S Nat

-- Notice here in the inductive case we reduce to normal form. Not doing so
-- leads to a subtly different term wherein we are applying "S" to a term
-- that itself is a lambda term applied to two arguments but not yet β-reduced.
fromNat :: Nat -> Term Text
fromNat Z     = Lam "S" (Lam "Z" "Z")
fromNat (S n) = Lam "S" (Lam "Z" ("S" .$ (nf $ fromNat n .$ "S" .$ "Z")))

-- Let us also give ourselves names for the first few church numerals for convenience:
cZero  = fromNat Z
cOne   = fromNat (S Z)
cTwo   = fromNat (S (S Z))
cThree = fromNat (S (S (S Z)))
cFour  = fromNat (S (S (S (S Z))))
cFive  = fromNat (S (S (S (S (S Z)))))
cSix   = fromNat (S (S (S (S (S (S Z))))))
```

Now recall that we wish to test how our code _evaluates_ to normal form and thus
we should consider some functions to actually run. Two such functions that come to mind are addition and multiplication.
But how are these defined for Church numerals? Remember that $\mathrm{n}$ is meant to represent applying
a step function $\mathrm{n}$ times to a value. If the value we apply to the step function is the result of applying a step function argument $\mathrm{s}$ to a starting value $\mathrm{m}$ times, we see that this is operationally the same as $\mathrm{m} + \mathrm{n}$. In lambda terms:

  $$ \mathrm{add} := \lambda \mathrm{n} \; . \; \lambda \; \mathrm{m} \; . \;
      \lambda \mathrm{s} \; . \; \lambda \; \mathrm{z} \; . \;
      \mathrm{n} \; \mathrm{s} \; (\mathrm{m} \;  \mathrm{s} \; \mathrm{z} )
  $$

Similarly, we can define multiplication of $\mathrm{m}$ by $\mathrm{n}$ by applying $\mathrm{n}$ to
the step funtion $(\mathrm{m} \; s)$ (the $\mathrm{m}$-fold application of $\mathrm{s}$) and starting value $\mathrm{z}$:

  $$ \mathrm{mult}:= \lambda \mathrm{n} \; . \; \lambda \; \mathrm{m} \; . \;
      \lambda \mathrm{s} \; . \; \lambda \; \mathrm{z} \; . \;
      \mathrm{n} \; (\mathrm{m} \; \mathrm{s}) \; z
  $$

Let us translate this into Haskell:
```haskell
churchAdd :: Term Text
churchAdd = Lam "m" (Lam "n" (Lam "S" (Lam "Z" ((App "m" "S") .$ ("n" .$ "S" .$ "Z")))))

churchMult :: Term Text
churchMult = Lam "m" (Lam "n" (Lam "S" (Lam "Z" ("n" .$ ("m" .$ "S") .$ "Z"))))
```



As a first check let us see that $2 + 2 \rightsquigarrow 4$ and that $2 * 3 \rightsquigarrow 6$:

```haskell
import Test.Tasty.HUnit      as HU
-- [...]
unitTests :: TestTree
unitTests = testGroup "Church Arithmetic Unit Tests"
  [ HU.testCase
      "2 + 2 ⇝ 4" $
      (nf $ (churchAdd .$ cTwo) .$ cTwo) @?= cFour
  , HU.testCase
      "2 * 3 ⇝ 6" $
      (nf $ churchMult .$ cTwo .$ cThree) @?= cSix
  ]
```
This is fortunately the case:
```bash
Church Arithmetic Unit Tests
    2 + 2 ⇝ 4:                         OK
    2 * 3 ⇝ 6:                         OK
```

For a slightly more robust test, we can also write property tests to check that addition and multiplication are each commutative. First we will want to have an arbitrary instance for our definition of the unary natural numbers:
```haskell
fromInt :: Int -> Nat
fromInt 0 = Z
fromInt n = S (fromInt (n - 1))

-- We convert from a randomly generated integer
-- between 0 and 50.
instance Arbitrary Nat where
    arbitrary =
      do
        i <- choose (0,50)
        pure $ fromInt i
```
Now we can write our properties as follows:
```haskell
import Test.Tasty.QuickCheck as QC
{-
[...]
-}
additionIsCommutative :: Nat -> Nat -> Property
additionIsCommutative n m =
      nf (churchAdd .$ fromNat n .$ fromNat m)
  === nf (churchAdd .$ fromNat m .$ fromNat n)


multiplicationIsCommutative :: Nat -> Nat -> Property
multiplicationIsCommutative n m =
      nf (churchMult .$ fromNat n .$ fromNat m)
  === nf (churchMult .$ fromNat m .$ fromNat n)

churchProperties :: [TestTree]
churchProperties =
  [ QC.testProperty
      "Addition of Church numerals is commutative"
     (withMaxSuccess 100 additionIsCommutative)
  , QC.testProperty
      "Multiplication of Church numerals is commutative"
     (withMaxSuccess 100 multiplicationIsCommutative)
  ]
```

Running this gives us the following:
```bash
    Addition of Church numerals is commutative:       OK (0.05s)
      +++ OK, passed 100 tests.
    Multiplication of Church numerals is commutative: OK (0.07s)
      +++ OK, passed 100 tests.
```

It looks like our implementation might be (close to) working as hoped! Phew.

We should note that one downside to our version of locally nameless terms is
that there are syntacticaly valid terms in our grammar which, nevertheless, do
not make sense as lambda terms. For example, the following term is perfectly valid
in our grammar:
  $$
    \lambda \; . \; \lambda \; . \; (1 \; 3)
  $$

Here there is a bound variable $3$ but the binding depth is only 1 (counting from $0$).
We would like, instead, to use the type system to enforce that each of our terms
is (intrinsically) a valid lambda term. Doing this in Haskell is quite a challenge as
such an endeavour necessarily involves types which keep track of the maximum current
binding variable, and thus dependent types. In our next post we will see how to do this
in Agda and then prove various properties of our locally nameless terms.

Thank you for reading! Feel free to contact me [here](mailto:callan.mcgill@gmail.com) with questions, thoughts, ideas, or all of the above.