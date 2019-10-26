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

In order that this work as a theory of computation we need some notion of evaluation and this is driven by $\beta$-reduction. The standard jargon is to say that a $\beta$-redux is any subterm of the form $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$. On such a $\beta-redux$ we can then step via (capture-avoiding) substititon:

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

Here we have substituted the _free_ variable y into our lambda term and it has become _bound_. This is semantically incorrect, the names of free variables are meaningful - in spirit they refer to names we have defined elsewhere (that is, they are can be looked up within a context or in other words they are _open_ for further substitution). Conversely, the names of bound variables are, computationally speaking, unimportant. In fact it is usual to refer to the grammar we have introduced earlier as _pre-lambda terms_ and to take lambda terms as referring to the equivalence classes under $\alpha$-equivalence. This refers to the (equivalence) relation whereby two terms are equivalent if we can consistently rename the bound variables of one to obtain the other (here too we need to take care, alpha renaming $\mathrm{x}$ to $\mathrm{y}$ in the above term would lead to a different sort of variable capture). In fact most accounts of $alpha$-equivalence are themselves intimiately tied up with the question of how to perform substitution.

In practice this means that in order to compute  $(\lambda \mathrm{x} \; . \; \mathrm{f}) \; \mathrm{arg}$ we would first $\alpha$-rename $\mathrm{x}$ to a variable that is not (_free or bound_) already named within $\mathrm{f}$ and is also not free within $\mathrm{arg}$. Doing this via brute force is not _too_ bad but rather fiddly and error prone. A simple version of such a scheme is described by Lennart Augustsson [here](http://augustss.blogspot.com/2007/10/simpler-easier-in-recent-paper-simply.html). 

There are a [whole host](https://www.schoolofhaskell.com/user/edwardk/bound) of most sophisticated methods for dealing with the problem. Perhaps one of the best known is to use De-Bruijn indices. The idea here is to replace all bound variables by a natural number indicating the variable's distance from a binding site and all free variables by a natural number larger than any binding site (kept track of within the environment under which computation is performed). For instance the following is how one might translate a term into De-Bruijn indices:

$$ (\lambda \mathrm{x} \; . \; \lambda \; y \; . \;  x \; z)
    \longrightarrow
   (\lambda \; \lambda \; . \; 1 \; 3 \;)
   $$
  $$
   [z \mapsto 3]
  $$

Here we keep both the translated lambda term but also the context for how to read free variables. This is quite nice in many respects:

  * Capture avoiding substitution becomes a matter of keeping binding distance arithmetic in check.
  * The De-Bruijn representation gives canonical representatives for the equivalence classes of $\alpha$-equivalence and
  so allow us to test for $\alpha$-equivalence via syntactic equality.

On the other hand, Bob Atkey has, rather aptly, referred to the ability to read terms written with DeBruijn indices as a "cylon detector". What we have gained in the form of ease of implementation we have more than adequately abondoned in the form of readability. Instead we turn to the paper [I Am Not a Number -- I am a Free Variable](http://www.cs.ru.nl/~james/RESEARCH/haskell2004.pdf). Let us keep free variables free and use De-Bruijn indices only for bound variables:


```haskell
data Var a
  = F a
  | B Int

var :: a -> Var a
var = F

type LocallyNameless a = Lam (Var a)
```

Notice how with this representation we still keep names at binders. This is useful as we can recover the named term we started out with, ignoring all such names as we perform work. Here is how we convert between the two representations:

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
      Lam n e   ->
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
            Nothing   -> error $ "Found bound variable with binding:" <> show bv
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

Thankfully this does indeed work as expected:
```shell
Tests
  Property Tests
    fromLocallyNameless ∘ toLocallyNameless === id: OK (0.35s)
      +++ OK, passed 1000 tests.
```

Now that we have terms in locally nameless representation we can perform substitution in a fairly straightforward manner. In the McBride--McKinna paper they refer to this operation as __instatiate__, it is also common in the literate to refer to the operation as opening as we open a binder instatiating its outermost layer and we will follow this convention:
```haskell
-- We use a type synonym similar to the newtype in the paper
-- (perhaps as a reminder to go back and atone).
type Scope f x = f x

open :: forall a . Term (Var a) -> Scope Term (Var a) -> Term (Var a)
open image = go 0
  where
    go :: Int -> Term (Var a) -> Term (Var a)
    go outer =
      \case
        Var fbv ->
          case fbv of
            B bv | bv == outer -> image
                 | otherwise   -> Var (B bv)
            F fv -> Var (F fv)
        App l r -> App (go outer l) (go outer r)
        Lam n b -> Lam n (go (outer + 1) b)
```

From here it is easy for us to implement reduction to both normal form and weak-head normal form (where we use call by name semantics):

```haskell
whnfLN :: Term (Var a) -> Term (Var a)
whnfLN term = go term []
  where
    go :: Term (Var a) -> [Term (Var a)] -> Term (Var a)
    go t as =
      case (t, as) of
        ((App l r), args)
          -> go l (r : args )
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
        ((Lam n body) , [])
          -> (Lam n (nfLN body))
        ((Lam _ body) , a:args)
          -> go (substitute a body) args
        _
          -> foldl' App t (fmap nfLN as)


nf :: (Ord a) => Term a -> Term a
nf = fromLocallyNameless . nfLN . toLocallyNameless
```

Let us check this too is correct by quickly whipping together a church encoding of the natural numbers. To anyone unfamiliar with this idea we give an all-too-brief introduction hopefully starting with something familiar to any functional programmer -- lists!


We start with what is called the pattern functor for list. If we were to take fixed points of this with respect to the variable r we recover (something isomorphic to) ordinary Haskell lists:
```haskell
data ListP a r = NilP | ConsP a r
```

An algebra $\mathrm{t}$ for a functor $\mathrm{F}$ is defined to be a function $\mathrm{F \; t} \rightarrow \mathrm{t}$. In this case this is slightly complicated by the fact that our functor is also polymorphic in the 'a' variable but don't let this be a distraction.
```haskell
type AlgL a t = ListP a t -> t
```

Now suppose that $\mathrm{C}$ is a $\mathrm{ListP}$ algebra and so $\mu :: \mathrm{AlgL} \; \mathrm{a} \; \mathrm{C}$. This means we have a function:
```haskell
mu :: ListP a t -> t
```
Some thought will convince us that in fact we have the following isomorphism of types:
```haskell
forward :: (ListP a t -> t) -> (t, (a -> t -> t))
forward alg = (alg NilP, \a t -> alg (ConsP a t))

backward :: (t, (a -> t -> t)) -> (ListP a t -> t)
backward (n, c) NilP        = n
backward (n, c) (ConsP a t) = c a t
```

Now the important point here is that the fixed point (in this case List) is the _initial_ $\mathrm{F}$-algebra. Let us see what this means in terms of the above type isomorphism:
```haskell
-- any F-algebra structure t we have a function from [a] using that structure:
initialityListP :: forall a .  [a] -> (t , (a -> t -> t)) -> t

-- Re-arranging the order of arguments and currying we see that this is nothing more than
-- the type signature of foldr:
foldr :: forall a . (a -> t -> t) -> t -> [a] -> t
```

Similarly (in fact this is really a special case when a = ()) for the natural
numbers we can consider:
```haskell
data NatP r = ZeroP | SuccP r

data Nat = Zero | Succ Nat
```

Precisely the same re-arrangements as above give us:
```haskell
initialityNatP :: t -> (t -> t) -> Nat -> t
```

In  fact, that the natural numbers can be described as an _initial_ $\mathrm{F}$-algebra opens up the possibility that we give them an alternative description in which we do not use data types:
```haskell
natIsoForward :: Nat -> (forall t . t -> (t -> t) -> t)
natIsoForward Zero z s     = z
natIsoForward (Succ n) z s = s (natIsoForward z s)

natIsoBackwards :: (forall t . t -> (t -> t) -> t) -> Nat
natIsoBackwards f = f Zero Succ
```


Now getting back to our regularly scheduled programming we note that the above gives us a characterization of the natural numbers in terms of functions. This is perfect for the lambda caluclus as all it has is functions. As such, we can instead define the _Church_ numerals with this in mind:


$$ \mathrm{zero} = \lambda s . \lambda z . z $$
$$ \mathrm{succ}\; n = \lambda s . \lambda z . s \; (n \; s \; z) $$


Encoding the same thing in our code (and adding some syntax to make our life slightly easier):

```haskell
{-# LANGUAGE OverloadedStrings #-}
-- [...]
infixl 5 .$
(.$) :: Term a -> Term a -> Term a
(.$) = App

data Nat = Z | S Nat

fromInt :: Int -> Nat
fromInt 0 = Z
fromInt n = S (fromInt (n - 1))

-- this will allow us to write some property tests
-- for our normal form functions.
instance Arbitrary Nat where
    arbitrary =
      do
        i <- choose (0,50)
        pure $ fromInt i

-- This is precisely the same as the above encodings
fromNat :: Nat -> Term Text
fromNat Z     = Lam "S" (Lam "Z" "Z")
fromNat (S n) = Lam "S" (Lam "Z" ("S" .$ (nf $ fromNat n .$ "S" .$ "Z")))

cZero  = fromNat Z
cOne   = fromNat (S Z)
cTwo   = fromNat (S (S Z))
cThree = fromNat (S (S (S Z)))
cFour  = fromNat (S (S (S (S Z))))
cFive  = fromNat (S (S (S (S (S Z)))))
cSix   = fromNat (S (S (S (S (S (S Z))))))

-- we apply the successor function m times to the result of
-- applying it n times to z.
churchAdd :: Term Text
churchAdd = Lam "m" (Lam "n" (Lam "S" (Lam "Z" ((App "m" "S") .$ ("n" .$ "S" .$ "Z")))))

-- Similarly here we apply the m-fold successor function n times to z.
churchMult :: Term Text
churchMult = Lam "m" (Lam "n" (Lam "S" (Lam "Z" ("n" .$ ("m" .$ "S") .$ "Z"))))
```

As a first check let us see that the following unit tests pass:

```haskell
import Test.Tasty.HUnit      as HU
-- [...]
unitTests :: TestTree
unitTests = testGroup "Unit Tests"
  [ HU.testCase
      "two plus two is four" $
      (nf $ (churchAdd .$ cTwo) .$ cTwo) @?= cFour
  , HU.testCase
      "two times three is six" $
      (nf $ churchMult .$ cTwo .$ cThree) @?= cSix
  ]
```
```bash
Unit Tests
    2 + 2 = 4:                           OK
    2 * 3 = 6:                         OK
```

In order to be more robust (for some definition of robust) let us also check that addition
and multiplication are each commutative:
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

Running this gives us:
```bash
    Addition of Church numerals is commutative:       OK (0.05s)
      +++ OK, passed 100 tests.
    Multiplication of Church numerals is commutative: OK (0.07s)
      +++ OK, passed 100 tests.
```

Looks like we might be (close to) working as hoped! Phew.
