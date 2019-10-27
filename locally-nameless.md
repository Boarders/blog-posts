---
title: "Locally Nameless"
author: "Callan McGill"
# tags: ["Type theory", "Lambda Calculus", "Haskell", "Substitution"]
categories:
  - posts
date: "2019-09-17"
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

In order that this work as a theory of computation we need some notion of evaluation and this is driven by $\beta$-reduction. The standard jargon is to say that a $\beta$-redux is any subterm of the form $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$. On such a $\beta$-redux we can then step via (capture-avoiding) substititon:

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
algorithmically to a choice of evaluation strategy. As such, this opens up a lot of interesting questions related to order of evaluation and normal forms and so on. Instead we will largely bypass these considerations and concentrate on the more humdrum (but no less vital) matter of the practicalities of performing such capture-avoiding substitutions. The basic problem with too naive an approach is as follows:

$$ (\lambda \mathrm{x} \; . \; \lambda \; y \; . \;  x) \; \mathrm{y}
    \rightsquigarrow
   (\lambda \mathrm{y} \; . \; y \;)
  $$

Here we have substituted the _free_ variable y into our lambda term and it has become _bound_. This is semantically incorrect, the names of free variables are meaningful - in spirit they refer to names we have defined elsewhere (that is, they are can be looked up within a context or in other words they are _open_ for further substitution). Conversely, the names of bound variables are, computationally speaking, unimportant. In fact it is usual to refer to the grammar we have introduced earlier as _pre-lambda terms_ and to take lambda terms as referring to the equivalence classes under $\alpha$-equivalence. This refers to the (equivalence) relation whereby two terms are equivalent if we can consistently rename the bound variables of one to obtain the other (here too we need to take care, alpha renaming $\mathrm{x}$ to $\mathrm{y}$ in the above term would lead to a different sort of variable capture). In fact most accounts of $\alpha$-equivalence are themselves intimiately tied up with the question of how to perform substitution (and locally nameless is no different).

In practice this means that in order to compute  $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$ we would first $\alpha$-rename $\mathrm{x}$ to a variable that is not already named within $\mathrm{f}$ and is also not free within $\mathrm{arg}$. Doing this via brute force is not _too_ bad but rather fiddly and error prone. A simple version of such a scheme is described by Lennart Augustsson [here](http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html). 

There are a [whole host](https://www.schoolofhaskell.com/user/edwardk/bound) of more sophisticated methods for dealing with the problem. Perhaps one of the best known is to use De-Bruijn indices. The idea here is to replace all bound variables by a natural number indicating the variable's distance from a binding site and all free variables by distinct natural numbers greater than the maximum depth of any binding site (which we then keep track of within the environment under which computation is performed). For instance the following is how one might translate a term into De-Bruijn indices:

$$ (\lambda \mathrm{x} \; . \; \lambda \; y \; . \;  x \; z)
    \longrightarrow
   (\lambda \; \lambda \; . \; 1 \; 3 \;)
   $$
  $$
   [z \mapsto 3]
  $$

Here we keep both the translated lambda term but also the context for how to read free variables. This approach is quite nice in certain respects:

  * Capture avoiding substitution becomes a matter of keeping binding distance arithmetic in check.
  * The De-Bruijn representation gives canonical representatives for $\alpha$-equivalence classes thus allowing us to test for $\alpha$-equivalence via syntactic equality of terms.

On the other hand, Bob Atkey has, rather aptly, referred to the ability to read terms written with DeBruijn indices as a "cylon detector". What we have gained in the form of ease of implementation we have more than adequately abondoned in the form of readability. Instead we turn to the paper [I Am Not a Number -- I am a Free Variable](http://www.cs.ru.nl/~james/RESEARCH/haskell2004.pdf). Let us keep free variables free and use De-Bruijn indices only for bound variables:


```haskell
-- Our variable type keeps the old free variables and uses
--integers to represent bound variables.
data Var a
  = F a
  | B Int

-- Locally nameless terms will be the same lambda terms with
-- variables now either labelled either bound or free.
type LocallyNameless a = Lam (Var a)
```

Notice how because we keep the old lambda terms with this representation we still keep names at binders. This is useful as we can recover the named term we started out with, ignoring all such names as we perform work. Here is how we convert between the two representations:

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

Just to see that this works as expected (this is, for me, a worrying amount of bookeeping to leave to "Looks good!"). Let us use quickcheck to see that __fromLocallyNameless__ is a left inverse to __toLocallyNameless__:

``` haskell
import Test.Tasty.QuickCheck as QC
{-
[...]
-}
-- We use a somewhat unprincipled approach to generating arbitrary instances
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
-- fromLocalyNameless provides a left inverse to toLocallyNameless.
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

Now that we have terms in locally nameless representation we can perform substitution in a fairly straightforward manner. In the McBride--McKinna (MK) paper they refer to this operation as __instantiate__, though it is also common in the literate to call the operation opening as we open a binder instatiating its outermost binding layer, and we will follow this convention. We note in the code below that we follow (in spirit at least) the MK convention of using a scope type (in our case we
only use a type synonym but in a more substantial implementation one should use a newtype). This is supposed to remind us that the term we are substitutiing into is not itself a legal lambda term. Instead, it is only legal if it appears as the _body_ of a lambda term (that is to say it may have bound variables within it so long as they are only a single layer so to speak).
```haskell
type Scope f x = f x

open :: forall a . Term (Var a) -> Scope Term (Var a) -> Term (Var a)
open image = go 0
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

From here it is easy for us to implement reduction to both normal form and weak-head normal form (where we use call by name semantics). We will, in both cases, write a function that does all of the work using locally nameless terms and functions that make use of that work on named lambda terms
via the conversion functions we defined previously:

```haskell
whnfLN :: Term (Var a) -> Term (Var a)
whnfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (t, as) of
        ((App l r), args)
          -> go l (r : args )
     -- We only perform substitution if we have found
     -- a list of arguments to substitute and otherwise
     -- an outermost lambda is left untouched.
        ((Lam _ body) , a:args)
          -> go (substitute a body) args
        _
          -> foldl' App t as


whnf :: (Ord a) => Term a -> Term a
whnf = fromLocallyNameless . whnfLN . toLocallyNameless


nfLN :: Term (Var a) -> Term (Var a)
nfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (t, as) of
        ((App l r), args)
          -> go l (r : args)
      -- Here we go under a lamda and continue
      -- to perform reduction within the body.
        ((Lam n body) , [])
          -> (Lam n (nfLN body))
        ((Lam _ body) , a:args)
          -- We substitute the body before evaluation here
          -- hence call-by-name semantics.
          -> go (substitute a body) args
        _
          -> foldl' App t (fmap nfLN as)


nf :: (Ord a) => Term a -> Term a
nf = fromLocallyNameless . nfLN . toLocallyNameless
```

Now that we have written this reduction code we should test it, but what on? A natural choice is to consider church encodings of the natural numbers. Since all we have in the lambda calculus is a theory of functions (with no base data types), we must encode any data in the form of functions. Church numerals act as a prototypical example of such an encoding:


$$ \mathrm{zero} = \lambda \mathrm{s} . \lambda \mathrm{z} . \mathrm{z} $$
$$ \mathrm{succ}\; \mathrm{n} = \lambda \mathrm{s} . \lambda \mathrm{z} . \mathrm{s} \; (\mathrm{n} \; \mathrm{s} \; \mathrm{z}) $$

The idea here is that zero takes as arguments a step function $\mathrm{s}$ and a starting value $\mathrm{z}$ and returns that starting value. A positive number n on the other hand takes those arguments and applies the step function to the starting value n times. Here is what that looks like in our implementation:

```haskell
{-# LANGUAGE OverloadedStrings #-}
-- [...]
-- We give ourselves some handy infix syntax for apply.
infixl 5 .$
(.$) :: Term a -> Term a -> Term a
(.$) = App

data Nat = Z | S Nat

-- Notice here in the inductive case we reduce to normal form. Not doing so
-- leads to a subtly different term wherein we are applying "S" to a term
-- that itself is a lambda term applied to two arguments but not yet reduced.
fromNat :: Nat -> Term Text
fromNat Z     = Lam "S" (Lam "Z" "Z")
fromNat (S n) = Lam "S" (Lam "Z" ("S" .$ (nf $ fromNat n .$ "S" .$ "Z")))

-- Let us also give ourselves names for the first few church numerals:
cZero  = fromNat Z
cOne   = fromNat (S Z)
cTwo   = fromNat (S (S Z))
cThree = fromNat (S (S (S Z)))
cFour  = fromNat (S (S (S (S Z))))
cFive  = fromNat (S (S (S (S (S Z)))))
cSix   = fromNat (S (S (S (S (S (S Z))))))
```

Now recall that we wish to test how our code _evaluates_ to normal form and thus
we should consider some functions to actually run. One idea here is addition and multiplication
but how are these defined for Church numerals? Remember that $\mathrm{n}$ is meant to represent applying
a step function n times to a value. If the value we apply the function to is that which has
already been gotten by applying a step function argument $\mathrm{s}$ to a starting value $\mathrm{m}$ times we see that this is operationally the same as $\mathrm{m} + \mathrm{n}$:

  $$ \lambda \mathrm{n} \; . \; \lambda \; \mathrm{m} \; . \;
      \lambda \mathrm{s} \; . \; \lambda \; \mathrm{z} \; . \;
      \mathrm{n} \; \mathrm{s} \; (\mathrm{m} \;  \mathrm{s} \; \mathrm{z} )
  $$

Similarly we can define multiplication of $\mathrm{m}$ by $\mathrm{n}$ by applying $\mathrm{n}$ to
the step funtion $(\mathrm{m} \; s)$ (the $\mathrm{m}$-fold application of $\mathrm{s}$) and starting value $\mathrm{z}$:

  $$ \lambda \mathrm{n} \; . \; \lambda \; \mathrm{m} \; . \;
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



As a first check let us test that $2 + 2 \rightsquigarrow 4$ and that $2 * 3 \rightsquigarrow 6$:

```haskell
import Test.Tasty.HUnit      as HU
-- [...]
unitTests :: TestTree
unitTests = testGroup "Unit Tests"
  [ HU.testCase
      "2 + 2 -> 4" $
      (nf $ (churchAdd .$ cTwo) .$ cTwo) @?= cFour
  , HU.testCase
      "2 * 3 -> 6" $
      (nf $ churchMult .$ cTwo .$ cThree) @?= cSix
  ]
```
This is fortunately the case:
```bash
Unit Tests
    2 + 2 -> 4:                         OK
    2 * 3 -> 6:                         OK
```

For a slightly more robust (for some definition of robust) test we can also write property tests in order to check that addition and multiplication are each commutative. First we will want to have an arbitrary instance for our definition of the unary natural numbers:
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
Now we can write our properties:
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
