# 001 - Category Theory

## Table of Contents

1. [Introduction](#introduction)
2. [Formal Definitions](#formal-definitions)
3. [Basic Concepts](#basic-concepts)
4. [Functors](#functors)
5. [Natural Transformations](#natural-transformations)
6. [Limits and Colimits](#limits-and-colimits)
7. [Adjunctions](#adjunctions)
8. [Monads](#monads)
9. [Applications](#applications)
10. [Haskell Implementation](#haskell-implementation)
11. [References](#references)

## Introduction

Category Theory provides a unified framework for understanding mathematical structures through:

- **Objects** and **morphisms**
- **Composition** and **identity**
- **Universal properties**
- **Abstraction** of mathematical concepts

**Cross-Reference**: Builds on [001-Set-Theory](../01-Mathematics/001-Set-Theory.md) and provides foundation for [001-Functional-Programming](../../haskell/001-Functional-Programming.md).

## Formal Definitions

### Category

A **category** $\mathcal{C}$ consists of:

1. **Objects**: A collection $\text{Ob}(\mathcal{C})$
2. **Morphisms**: For each pair $A, B \in \text{Ob}(\mathcal{C})$, a set $\text{Hom}_{\mathcal{C}}(A, B)$
3. **Composition**: For $f: A \rightarrow B$ and $g: B \rightarrow C$, a morphism $g \circ f: A \rightarrow C$
4. **Identity**: For each object $A$, an identity morphism $1_A: A \rightarrow A$

**Axioms**:

- **Associativity**: $(h \circ g) \circ f = h \circ (g \circ f)$
- **Identity**: $f \circ 1_A = f = 1_B \circ f$

### Examples of Categories

1. **Set**: Objects are sets, morphisms are functions
2. **Grp**: Objects are groups, morphisms are group homomorphisms
3. **Top**: Objects are topological spaces, morphisms are continuous maps
4. **Hask**: Objects are Haskell types, morphisms are functions

## Basic Concepts

### Isomorphisms

A morphism $f: A \rightarrow B$ is an **isomorphism** if there exists $g: B \rightarrow A$ such that:
$$g \circ f = 1_A \quad \text{and} \quad f \circ g = 1_B$$

### Monomorphisms and Epimorphisms

- **Monomorphism**: $f: A \rightarrow B$ is monic if $f \circ g = f \circ h \implies g = h$
- **Epimorphism**: $f: A \rightarrow B$ is epic if $g \circ f = h \circ f \implies g = h$

### Initial and Terminal Objects

- **Initial object**: Object $I$ such that for any object $A$, there's exactly one morphism $I \rightarrow A$
- **Terminal object**: Object $T$ such that for any object $A$, there's exactly one morphism $A \rightarrow T$

## Functors

### Definition

A **functor** $F: \mathcal{C} \rightarrow \mathcal{D}$ consists of:

- A function $F: \text{Ob}(\mathcal{C}) \rightarrow \text{Ob}(\mathcal{D})$
- For each $f: A \rightarrow B$, a morphism $F(f): F(A) \rightarrow F(B)$

**Axioms**:

- $F(1_A) = 1_{F(A)}$
- $F(g \circ f) = F(g) \circ F(f)$

### Types of Functors

1. **Covariant**: Preserves direction of morphisms
2. **Contravariant**: Reverses direction of morphisms
3. **Bifunctor**: Functor from product category $\mathcal{C} \times \mathcal{D}$

### Examples

- **Identity functor**: $1_{\mathcal{C}}: \mathcal{C} \rightarrow \mathcal{C}$
- **Forgetful functor**: $U: \text{Grp} \rightarrow \text{Set}$
- **Power set functor**: $P: \text{Set} \rightarrow \text{Set}$

## Natural Transformations

### Definition1

A **natural transformation** $\eta: F \Rightarrow G$ between functors $F, G: \mathcal{C} \rightarrow \mathcal{D}$ consists of:

- For each object $A \in \mathcal{C}$, a morphism $\eta_A: F(A) \rightarrow G(A)$

**Naturality**: For any $f: A \rightarrow B$, the following diagram commutes:

```latex
F(A) --η_A--> G(A)
 |            |
F(f)         G(f)
 |            |
F(B) --η_B--> G(B)
```

### Natural Isomorphisms

A natural transformation $\eta$ is a **natural isomorphism** if each $\eta_A$ is an isomorphism.

## Limits and Colimits

### Products

A **product** of objects $A$ and $B$ is an object $A \times B$ with projections:
$$\pi_1: A \times B \rightarrow A \quad \text{and} \quad \pi_2: A \times B \rightarrow B$$

**Universal property**: For any object $X$ with morphisms $f: X \rightarrow A$ and $g: X \rightarrow B$, there exists unique $h: X \rightarrow A \times B$ such that:
$$\pi_1 \circ h = f \quad \text{and} \quad \pi_2 \circ h = g$$

### Coproducts

A **coproduct** of objects $A$ and $B$ is an object $A + B$ with injections:
$$\iota_1: A \rightarrow A + B \quad \text{and} \quad \iota_2: B \rightarrow A + B$$

### Equalizers and Coequalizers

- **Equalizer**: Universal solution to $f \circ x = g \circ x$
- **Coequalizer**: Universal solution to $x \circ f = x \circ g$

## Adjunctions

### Definition2

An **adjunction** between categories $\mathcal{C}$ and $\mathcal{D}$ consists of:

- Functors $F: \mathcal{C} \rightarrow \mathcal{D}$ and $G: \mathcal{D} \rightarrow \mathcal{C}$
- Natural isomorphism: $\text{Hom}_{\mathcal{D}}(F(A), B) \cong \text{Hom}_{\mathcal{C}}(A, G(B))$

**Notation**: $F \dashv G$ (F is left adjoint to G)

### Unit and Counit

- **Unit**: $\eta: 1_{\mathcal{C}} \Rightarrow G \circ F$
- **Counit**: $\varepsilon: F \circ G \Rightarrow 1_{\mathcal{D}}$

### Examples1

- **Free-Forgetful**: Free group functor $\dashv$ forgetful functor
- **Product-Hom**: $(- \times A) \dashv \text{Hom}(A, -)$

## Monads

### Definition3

A **monad** on a category $\mathcal{C}$ is a triple $(T, \eta, \mu)$ where:

- $T: \mathcal{C} \rightarrow \mathcal{C}$ is a functor
- $\eta: 1_{\mathcal{C}} \Rightarrow T$ (unit)
- $\mu: T^2 \Rightarrow T$ (multiplication)

**Axioms**:

- $\mu \circ T\mu = \mu \circ \mu T$ (associativity)
- $\mu \circ T\eta = \mu \circ \eta T = 1_T$ (unit laws)

### Kleisli Category

For a monad $(T, \eta, \mu)$, the **Kleisli category** $\mathcal{C}_T$ has:

- Objects: Same as $\mathcal{C}$
- Morphisms $A \rightarrow B$: Morphisms $A \rightarrow T(B)$ in $\mathcal{C}$

## Applications

### Functional Programming

**Monads in Haskell**:

- **Maybe**: Handling partial functions
- **List**: Nondeterministic computation
- **State**: Stateful computation
- **IO**: Input/output operations

**Example**: Maybe monad

```haskell
data Maybe a = Nothing | Just a

-- Unit (return)
return :: a -> Maybe a
return = Just

-- Multiplication (join)
join :: Maybe (Maybe a) -> Maybe a
join Nothing = Nothing
join (Just Nothing) = Nothing
join (Just (Just x)) = Just x
```

### Algebraic Geometry

**Schemes**: Categories of sheaves on topological spaces
**Stacks**: Categories fibered in groupoids

### Topology

**Homology**: Functors from topological spaces to abelian groups
**Cohomology**: Contravariant functors

## Haskell Implementation

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module CategoryTheory where

import Prelude hiding (id, (.))

-- Category class
class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

-- Functor class (simplified)
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- Natural transformation
type Nat f g = forall a. f a -> g a

-- Monad class
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- Kleisli composition
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = \a -> f a >>= g

-- Product type
data Product a b = Product a b

-- Coproduct type (Either)
data Coproduct a b = Left a | Right b

-- Adjunction
class (Functor f, Functor g) => Adjunction f g where
  unit :: a -> g (f a)
  counit :: f (g a) -> a
  leftAdjunct :: (f a -> b) -> (a -> g b)
  rightAdjunct :: (a -> g b) -> (f a -> b)

-- Example: Product-Hom adjunction
instance Adjunction ((,) a) ((->) a) where
  unit b = \a -> (a, b)
  counit (a, f) = f a
  leftAdjunct f a = \b -> f (a, b)
  rightAdjunct g (a, b) = g a b

-- Yoneda lemma implementation
newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

instance Functor (Yoneda f) where
  fmap f (Yoneda g) = Yoneda (\h -> g (h . f))

-- Yoneda embedding
yoneda :: Functor f => f a -> Yoneda f a
yoneda fa = Yoneda (\f -> fmap f fa)

-- Yoneda lemma
yonedaLemma :: Functor f => Yoneda f a -> f a
yonedaLemma (Yoneda f) = f id

-- Free monad
data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free fa) = Free (fmap (fmap f) fa)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= f = f a
  Free fa >>= f = Free (fmap (>>= f) fa)

-- Cofree comonad
data Cofree f a = Cofree a (f (Cofree f a))

instance Functor f => Functor (Cofree f) where
  fmap f (Cofree a fa) = Cofree (f a) (fmap (fmap f) fa)

-- Kan extensions
data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

data Ran g h a where
  Ran :: (a -> g b) -> h b -> Ran g h a

-- Limits and colimits
class Functor f => HasLimits f where
  limit :: f a -> a

class Functor f => HasColimits f where
  colimit :: a -> f a

-- Example: Terminal object
data Terminal = Terminal

instance Category (->) where
  id = \x -> x
  (.) = \g f -> g . f

-- Example: Initial object
data Void

absurd :: Void -> a
absurd = undefined

-- Example: Product
fst :: Product a b -> a
fst (Product a _) = a

snd :: Product a b -> b
snd (Product _ b) = b

-- Example: Coproduct
caseEither :: (a -> c) -> (b -> c) -> Coproduct a b -> c
caseEither f _ (Left a) = f a
caseEither _ g (Right b) = g b

-- Natural transformation example
maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just a) = [a]

-- Monad laws verification
monadLaw1 :: Monad m => a -> m a
monadLaw1 = return

monadLaw2 :: Monad m => m a -> m a
monadLaw2 ma = ma >>= return

monadLaw3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
monadLaw3 ma f g = (ma >>= f) >>= g

-- Functor laws verification
functorLaw1 :: Functor f => f a -> f a
functorLaw1 = fmap id

functorLaw2 :: Functor f => (b -> c) -> (a -> b) -> f a -> f c
functorLaw2 g f = fmap g . fmap f
```

## References

1. **Cross-Reference**: [001-Set-Theory](../01-Mathematics/001-Set-Theory.md) - Mathematical foundation
2. **Cross-Reference**: [001-Functional-Programming](../../haskell/001-Functional-Programming.md) - Programming applications
3. **Cross-Reference**: [002-First-Order-Logic](../02-Formal-Logic/002-First-Order-Logic.md) - Logical foundations

**Academic Sources**:

- Mac Lane, S. (1998). Categories for the Working Mathematician
- Awodey, S. (2010). Category Theory
- Barr, M., & Wells, C. (1990). Category Theory for Computing Science

**Next Document**: [002-Functors-and-Natural-Transformations](002-Functors-and-Natural-Transformations.md)
