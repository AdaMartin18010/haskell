# Theorem Proving Examples - Haskell Formal Verification

## 1. Introduction to Theorem Proving

### Theoretical Background

Theorem proving in Haskell leverages the Curry-Howard correspondence, where types correspond to propositions and programs correspond to proofs. This allows us to write programs that are guaranteed to be correct by construction.

### Mathematical Foundation

**Curry-Howard Correspondence**:
- Types ↔ Propositions
- Programs ↔ Proofs
- Type checking ↔ Proof verification
- Type inhabitation ↔ Theorem provability

## 2. Basic Propositional Logic

### Implication (Function Types)

```haskell
-- Implication: A → B
-- In Haskell: a -> b
implication :: a -> b
-- This type represents the proposition "if A then B"

-- Example: Modus Ponens
-- If we have A → B and A, then we can conclude B
modusPonens :: (a -> b) -> a -> b
modusPonens f x = f x

-- Proof that modus ponens is correct
-- Given: f :: a -> b (proof of A → B)
-- Given: x :: a (proof of A)
-- Result: f x :: b (proof of B)
```

### Conjunction (Product Types)

```haskell
-- Conjunction: A ∧ B
-- In Haskell: (a, b)
conjunction :: (a, b)
-- This type represents the proposition "A and B"

-- Introduction rule for conjunction
conjIntro :: a -> b -> (a, b)
conjIntro x y = (x, y)

-- Elimination rules for conjunction
conjElim1 :: (a, b) -> a
conjElim1 (x, _) = x

conjElim2 :: (a, b) -> b
conjElim2 (_, y) = y

-- Proof of commutativity: A ∧ B → B ∧ A
conjComm :: (a, b) -> (b, a)
conjComm (x, y) = (y, x)
```

### Disjunction (Sum Types)

```haskell
-- Disjunction: A ∨ B
-- In Haskell: Either a b
disjunction :: Either a b
-- This type represents the proposition "A or B"

-- Introduction rules for disjunction
disjIntro1 :: a -> Either a b
disjIntro1 = Left

disjIntro2 :: b -> Either a b
disjIntro2 = Right

-- Elimination rule for disjunction (case analysis)
disjElim :: Either a b -> (a -> c) -> (b -> c) -> c
disjElim (Left x) f _ = f x
disjElim (Right y) _ g = g y

-- Proof of commutativity: A ∨ B → B ∨ A
disjComm :: Either a b -> Either b a
disjComm (Left x) = Right x
disjComm (Right y) = Left y
```

## 3. First-Order Logic

### Universal Quantification (Parametric Polymorphism)

```haskell
-- Universal quantification: ∀x. P(x)
-- In Haskell: forall a. p a
universal :: forall a. p a
-- This type represents "for all x, P(x) holds"

-- Example: Identity function
-- ∀x. x → x
id :: forall a. a -> a
id x = x

-- Example: Function composition
-- ∀x,y,z. (y → z) → (x → y) → (x → z)
compose :: forall a b c. (b -> c) -> (a -> b) -> (a -> c)
compose f g x = f (g x)

-- Proof of associativity of composition
-- ∀f,g,h. (f ∘ g) ∘ h = f ∘ (g ∘ h)
composeAssoc :: forall a b c d. 
    (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc f g h x = f (g (h x))
-- This is equivalent to: (f . g) . h = f . (g . h)
```

### Existential Quantification (Existential Types)

```haskell
-- Existential quantification: ∃x. P(x)
-- In Haskell: exists a. p a
-- We can simulate this with rank-2 types

-- Existential type using rank-2 polymorphism
newtype Exists p = Exists { unExists :: forall r. (forall a. p a -> r) -> r }

-- Introduction rule for existential quantification
existsIntro :: forall a. p a -> Exists p
existsIntro pa = Exists $ \f -> f pa

-- Elimination rule for existential quantification
existsElim :: Exists p -> (forall a. p a -> r) -> r
existsElim (Exists f) g = f g

-- Example: There exists a type that can be shown
-- ∃a. Show a
data Showable = forall a. Show a => Showable a

instance Show Showable where
    show (Showable x) = show x
```

## 4. Higher-Order Logic

### Function Types as Propositions

```haskell
-- Higher-order functions represent higher-order logic

-- Double negation: ¬¬A → A (classically)
-- In intuitionistic logic: A → ¬¬A
doubleNegIntro :: a -> ((a -> Void) -> Void)
doubleNegIntro x = \f -> f x

-- Contraposition: (A → B) → (¬B → ¬A)
contraposition :: (a -> b) -> ((b -> Void) -> (a -> Void))
contraposition f notB a = notB (f a)

-- Peirce's law (classical logic only)
-- ((A → B) → A) → A
-- This is not provable in intuitionistic logic
-- but can be added as an axiom
```

## 5. Inductive Types and Recursion

### Natural Numbers

```haskell
-- Natural numbers as an inductive type
data Nat = Zero | Succ Nat

-- Addition as a recursive function
add :: Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ (add m n)

-- Proof of commutativity of addition
-- ∀m,n. add m n = add n m
-- This requires structural induction

-- Base case: add Zero n = add n Zero
-- Induction step: if add m n = add n m, then add (Succ m) n = add n (Succ m)

-- Proof by structural induction
addComm :: Nat -> Nat -> Bool
addComm Zero Zero = True
addComm Zero (Succ n) = addComm Zero n
addComm (Succ m) Zero = addComm m Zero
addComm (Succ m) (Succ n) = addComm m n && addComm (Succ m) n
```

### Lists

```haskell
-- Lists as an inductive type
data List a = Nil | Cons a (List a)

-- Length function
length :: List a -> Nat
length Nil = Zero
length (Cons _ xs) = Succ (length xs)

-- Append function
append :: List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Proof of associativity of append
-- ∀xs,ys,zs. append (append xs ys) zs = append xs (append ys zs)
appendAssoc :: List a -> List a -> List a -> Bool
appendAssoc xs ys zs = 
    append (append xs ys) zs == append xs (append ys zs)
```

## 6. Dependent Types (Simulated)

### Length-Indexed Lists (Vectors)

```haskell
-- Length-indexed lists using type-level naturals
-- This simulates dependent types

-- Type-level naturals
data Z = Z
data S n = S n

-- Vector type indexed by length
data Vec a n where
    VNil :: Vec a Z
    VCons :: a -> Vec a n -> Vec a (S n)

-- Safe head function
vhead :: Vec a (S n) -> a
vhead (VCons x _) = x

-- Safe tail function
vtail :: Vec a (S n) -> Vec a n
vtail (VCons _ xs) = xs

-- Safe indexing
vindex :: Vec a n -> Fin n -> a
vindex (VCons x _) FZ = x
vindex (VCons _ xs) (FS i) = vindex xs i

-- Finite type for safe indexing
data Fin n where
    FZ :: Fin (S n)
    FS :: Fin n -> Fin (S n)

-- Proof that indexing is safe
-- ∀v,i. vindex v i is well-typed only if i < length v
```

## 7. Advanced Theorem Proving

### Equational Reasoning

```haskell
-- Equational reasoning in Haskell
-- We can prove properties by showing that functions are equal

-- Example: proving that map distributes over composition
-- map (f . g) = map f . map g

-- Proof by equational reasoning:
-- map (f . g) xs
-- = case xs of
--     [] -> []
--     (x:xs') -> (f . g) x : map (f . g) xs'
-- = case xs of
--     [] -> []
--     (x:xs') -> f (g x) : map (f . g) xs'
-- = case xs of
--     [] -> []
--     (x:xs') -> f (g x) : (map f . map g) xs'
-- = case xs of
--     [] -> []
--     (x:xs') -> f (g x) : map f (map g xs')
-- = map f (map g xs)
-- = (map f . map g) xs

-- Implementation of the proof
mapCompose :: (b -> c) -> (a -> b) -> [a] -> [c]
mapCompose f g = map f . map g

-- Verification that the property holds
verifyMapCompose :: Eq c => (b -> c) -> (a -> b) -> [a] -> Bool
verifyMapCompose f g xs = 
    map (f . g) xs == mapCompose f g xs
```

### Monad Laws

```haskell
-- Proving monad laws for Maybe

-- Left identity: return a >>= f = f a
leftIdentity :: Eq b => a -> (a -> Maybe b) -> Bool
leftIdentity a f = (return a >>= f) == f a

-- Right identity: m >>= return = m
rightIdentity :: Eq a => Maybe a -> Bool
rightIdentity m = (m >>= return) == m

-- Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
associativity :: Eq c => Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Bool
associativity m f g = 
    ((m >>= f) >>= g) == (m >>= (\x -> f x >>= g))

-- Proof for Maybe monad
-- Left identity:
-- return a >>= f = Just a >>= f = f a

-- Right identity:
-- Just x >>= return = Just x >>= Just = Just x
-- Nothing >>= return = Nothing

-- Associativity:
-- (Just x >>= f) >>= g = f x >>= g
-- Just x >>= (\x -> f x >>= g) = (\x -> f x >>= g) x = f x >>= g
```

## 8. Property-Based Testing

```haskell
-- Using QuickCheck for property-based testing
-- This is a form of automated theorem proving

import Test.QuickCheck

-- Property: reverse is involutive
prop_reverse_involutive :: [Int] -> Bool
prop_reverse_involutive xs = reverse (reverse xs) == xs

-- Property: map distributes over composition
prop_map_compose :: [Int] -> Bool
prop_map_compose xs = 
    map (f . g) xs == (map f . map g) xs
  where
    f = (+1)
    g = (*2)

-- Property: filter and map commute
prop_filter_map_commute :: [Int] -> Bool
prop_filter_map_commute xs = 
    filter p (map f xs) == map f (filter (p . f) xs)
  where
    f = (+1)
    p = (>0)

-- Property: foldr fusion
prop_foldr_fusion :: [Int] -> Bool
prop_foldr_fusion xs = 
    foldr f z (map g xs) == foldr (f . g) z xs
  where
    f = (+)
    g = (*2)
    z = 0
```

## 9. Formal Verification with Liquid Haskell

```haskell
-- Liquid Haskell allows us to write specifications
-- that are checked at compile time

{-@
-- Specification: length returns a non-negative integer
length :: xs:[a] -> {v:Nat | v = len xs}
@-}

{-@
-- Specification: head is safe for non-empty lists
head :: {xs:[a] | len xs > 0} -> a
@-}

{-@
-- Specification: tail is safe for non-empty lists
tail :: {xs:[a] | len xs > 0} -> {ys:[a] | len ys = len xs - 1}
@-}

{-@
-- Specification: append preserves length
append :: xs:[a] -> ys:[a] -> {zs:[a] | len zs = len xs + len ys}
@-}
```

## 10. Summary

This document demonstrates various approaches to theorem proving in Haskell:

1. **Curry-Howard Correspondence**: Using types as propositions and programs as proofs
2. **Propositional Logic**: Implication, conjunction, and disjunction
3. **First-Order Logic**: Universal and existential quantification
4. **Higher-Order Logic**: Function types as propositions
5. **Inductive Types**: Natural numbers and lists
6. **Dependent Types**: Length-indexed vectors
7. **Equational Reasoning**: Proving properties by calculation
8. **Property-Based Testing**: Automated verification with QuickCheck
9. **Formal Verification**: Specifications with Liquid Haskell

The key insight is that Haskell's type system can be used as a proof system, where well-typed programs correspond to valid proofs of theorems. 