# 001 - Type Theory

## Table of Contents

1. [Introduction](#introduction)
2. [Formal Definitions](#formal-definitions)
3. [Simple Type Theory](#simple-type-theory)
4. [Dependent Type Theory](#dependent-type-theory)
5. [Type Systems](#type-systems)
6. [Type Inference](#type-inference)
7. [Type Safety](#type-safety)
8. [Applications](#applications)
9. [Haskell Implementation](#haskell-implementation)
10. [References](#references)

## Introduction

Type Theory provides a foundation for:

- **Formal verification** of programs
- **Mathematical foundations** (alternative to set theory)
- **Programming language design**
- **Theorem proving** and formal mathematics

**Cross-Reference**: Builds on [001-Category-Theory](../03-Category-Theory/001-Category-Theory.md) and provides foundation for [001-Functional-Programming](../../haskell/001-Functional-Programming.md).

## Formal Definitions

### Type System

A **type system** consists of:

1. **Types**: A collection of type expressions
2. **Terms**: A collection of term expressions
3. **Typing Rules**: Rules that assign types to terms
4. **Reduction Rules**: Rules for computation

### Judgments

The basic judgment forms are:

- **Type Formation**: $\Gamma \vdash A : \text{Type}$
- **Term Formation**: $\Gamma \vdash t : A$
- **Type Equality**: $\Gamma \vdash A = B : \text{Type}$
- **Term Equality**: $\Gamma \vdash t = u : A$

### Contexts

A **context** $\Gamma$ is a sequence of variable declarations:
$$\Gamma ::= \emptyset \mid \Gamma, x : A$$

## Simple Type Theory

### Function Types

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma \vdash B : \text{Type}}{\Gamma \vdash A \rightarrow B : \text{Type}}$$

**Introduction Rule** (Abstraction):
$$\frac{\Gamma, x : A \vdash t : B}{\Gamma \vdash \lambda x : A. t : A \rightarrow B}$$

**Elimination Rule** (Application):
$$\frac{\Gamma \vdash t : A \rightarrow B \quad \Gamma \vdash u : A}{\Gamma \vdash t \, u : B}$$

**Computation Rule** ($\beta$-reduction):
$$(\lambda x : A. t) \, u \rightarrow t[u/x]$$

### Product Types

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma \vdash B : \text{Type}}{\Gamma \vdash A \times B : \text{Type}}$$

**Introduction Rule**:
$$\frac{\Gamma \vdash t : A \quad \Gamma \vdash u : B}{\Gamma \vdash (t, u) : A \times B}$$

**Elimination Rules**:
$$\frac{\Gamma \vdash t : A \times B}{\Gamma \vdash \pi_1(t) : A} \quad \frac{\Gamma \vdash t : A \times B}{\Gamma \vdash \pi_2(t) : B}$$

**Computation Rules**:
$$\pi_1(t, u) \rightarrow t \quad \pi_2(t, u) \rightarrow u$$

### Sum Types

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma \vdash B : \text{Type}}{\Gamma \vdash A + B : \text{Type}}$$

**Introduction Rules**:
$$\frac{\Gamma \vdash t : A}{\Gamma \vdash \text{inl}(t) : A + B} \quad \frac{\Gamma \vdash u : B}{\Gamma \vdash \text{inr}(u) : A + B}$$

**Elimination Rule** (Case Analysis):
$$\frac{\Gamma \vdash t : A + B \quad \Gamma, x : A \vdash u : C \quad \Gamma, y : B \vdash v : C}{\Gamma \vdash \text{case } t \text{ of } \text{inl}(x) \Rightarrow u \mid \text{inr}(y) \Rightarrow v : C}$$

## Dependent Type Theory

### Dependent Function Types (Π-types)

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma, x : A \vdash B : \text{Type}}{\Gamma \vdash \Pi_{x : A} B : \text{Type}}$$

**Introduction Rule**:
$$\frac{\Gamma, x : A \vdash t : B}{\Gamma \vdash \lambda x : A. t : \Pi_{x : A} B}$$

**Elimination Rule**:
$$\frac{\Gamma \vdash t : \Pi_{x : A} B \quad \Gamma \vdash u : A}{\Gamma \vdash t \, u : B[u/x]}$$

### Dependent Product Types (Σ-types)

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma, x : A \vdash B : \text{Type}}{\Gamma \vdash \Sigma_{x : A} B : \text{Type}}$$

**Introduction Rule**:
$$\frac{\Gamma \vdash t : A \quad \Gamma \vdash u : B[t/x]}{\Gamma \vdash (t, u) : \Sigma_{x : A} B}$$

**Elimination Rules**:
$$\frac{\Gamma \vdash t : \Sigma_{x : A} B}{\Gamma \vdash \pi_1(t) : A} \quad \frac{\Gamma \vdash t : \Sigma_{x : A} B}{\Gamma \vdash \pi_2(t) : B[\pi_1(t)/x]}$$

### Identity Types

**Formation Rule**:
$$\frac{\Gamma \vdash A : \text{Type} \quad \Gamma \vdash t : A \quad \Gamma \vdash u : A}{\Gamma \vdash \text{Id}_A(t, u) : \text{Type}}$$

**Introduction Rule** (Reflexivity):
$$\frac{\Gamma \vdash t : A}{\Gamma \vdash \text{refl}_t : \text{Id}_A(t, t)}$$

**Elimination Rule** (Path Induction):
$$\frac{\Gamma, x : A, y : A, p : \text{Id}_A(x, y) \vdash C : \text{Type} \quad \Gamma, x : A \vdash d : C[x, x, \text{refl}_x/x, y, p]}{\Gamma, x : A, y : A, p : \text{Id}_A(x, y) \vdash J_{x,y,p.C}(d, x, y, p) : C}$$

## Type Systems

### Simply Typed Lambda Calculus (STLC)

**Types**:
$$A, B ::= \text{Bool} \mid \text{Nat} \mid A \rightarrow B \mid A \times B$$

**Terms**:
$$t, u ::= x \mid \lambda x : A. t \mid t \, u \mid (t, u) \mid \pi_1(t) \mid \pi_2(t) \mid \text{true} \mid \text{false} \mid 0 \mid \text{succ}(t)$$

**Typing Rules**:

- Variables: $\frac{x : A \in \Gamma}{\Gamma \vdash x : A}$
- Abstraction: $\frac{\Gamma, x : A \vdash t : B}{\Gamma \vdash \lambda x : A. t : A \rightarrow B}$
- Application: $\frac{\Gamma \vdash t : A \rightarrow B \quad \Gamma \vdash u : A}{\Gamma \vdash t \, u : B}$

### System F (Polymorphic Lambda Calculus)

**Types**:
$$A, B ::= \alpha \mid A \rightarrow B \mid \forall \alpha. A$$

**Terms**:
$$t, u ::= x \mid \lambda x : A. t \mid t \, u \mid \Lambda \alpha. t \mid t \, A$$

**Typing Rules**:

- Type Abstraction: $\frac{\Gamma \vdash t : A}{\Gamma \vdash \Lambda \alpha. t : \forall \alpha. A}$ ($\alpha$ not free in $\Gamma$)
- Type Application: $\frac{\Gamma \vdash t : \forall \alpha. A}{\Gamma \vdash t \, B : A[B/\alpha]}$

### Calculus of Constructions (CoC)

**Sorts**: $\text{Prop}, \text{Set}, \text{Type}_i$

**Types**: $A, B ::= s \mid x \mid \Pi_{x : A} B \mid \lambda x : A. B$

**Terms**: $t, u ::= x \mid \lambda x : A. t \mid t \, u$

**Typing Rules**:

- Sort Formation: $\Gamma \vdash s : s'$ where $(s, s') \in \{(\text{Prop}, \text{Type}_0), (\text{Set}, \text{Type}_0), (\text{Type}_i, \text{Type}_{i+1})\}$
- Product Formation: $\frac{\Gamma \vdash A : s \quad \Gamma, x : A \vdash B : s}{\Gamma \vdash \Pi_{x : A} B : s}$

## Type Inference

### Algorithm W (Hindley-Milner)

**Unification**: Find most general unifier for type equations.

**Example**:

```latex
f : α → β
g : γ → δ
f (g x) : ?

Unification:
α = γ → δ
Result: f : (γ → δ) → β
```

### Principal Types

A type $A$ is a **principal type** for term $t$ if:

1. $\vdash t : A$
2. For any type $B$ with $\vdash t : B$, there exists substitution $\sigma$ such that $B = \sigma(A)$

## Type Safety

### Progress and Preservation

**Progress**: If $\vdash t : A$ and $t$ is not a value, then $t \rightarrow t'$ for some $t'$.

**Preservation**: If $\vdash t : A$ and $t \rightarrow t'$, then $\vdash t' : A$.

### Type Soundness

A type system is **sound** if:

- **Progress**: Well-typed terms don't get stuck
- **Preservation**: Reduction preserves types

### Type Completeness

A type system is **complete** if every term that doesn't get stuck is well-typed.

## Applications

### Theorem Proving

**Curry-Howard Correspondence**:

- Types ↔ Propositions
- Terms ↔ Proofs
- Type Checking ↔ Proof Checking

**Example**: Modus Ponens

```haskell
modusPonens :: (a -> b) -> a -> b
modusPonens f x = f x
```

### Program Verification

**Hoare Logic**: Preconditions and postconditions as types.

**Example**: Sorted list type

```haskell
data SortedList a where
  Nil :: SortedList a
  Cons :: a -> SortedList a -> SortedList a
```

### Dependent Types in Practice

**Agda/Coq**: Full dependent type theory
**Idris**: Dependent types with effects
**Haskell**: Limited dependent types via GADTs

## Haskell Implementation

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeTheory where

import Data.List (find)
import Control.Monad.State
import Control.Monad.Except

-- Type expressions
data Type = 
    TBool
  | TNat
  | TFun Type Type
  | TProd Type Type
  | TSum Type Type
  | TVar String
  | TForall String Type
  deriving (Eq, Show)

-- Term expressions
data Term = 
    Var String
  | Lam String Type Term
  | App Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Inl Type Term
  | Inr Type Term
  | Case Term String Term String Term
  | True
  | False
  | Zero
  | Succ Term
  | TAbs String Term
  | TApp Term Type
  deriving (Eq, Show)

-- Context
type Context = [(String, Type)]

-- Type checking monad
type TypeCheck = ExceptT String (State Int)

-- Fresh variable generation
freshVar :: TypeCheck String
freshVar = do
  n <- get
  put (n + 1)
  return $ "α" ++ show n

-- Type substitution
substType :: String -> Type -> Type -> Type
substType x t (TVar y) | x == y = t
substType x t (TVar y) | x /= y = TVar y
substType x t (TFun a b) = TFun (substType x t a) (substType x t b)
substType x t (TProd a b) = TProd (substType x t a) (substType x t b)
substType x t (TSum a b) = TSum (substType x t a) (substType x t b)
substType x t (TForall y a) | x == y = TForall y a
substType x t (TForall y a) | x /= y = TForall y (substType x t a)
substType _ _ t = t

-- Type checking
typeCheck :: Context -> Term -> TypeCheck Type
typeCheck ctx (Var x) = case lookup x ctx of
  Just t -> return t
  Nothing -> throwError $ "Unbound variable: " ++ x

typeCheck ctx (Lam x t1 body) = do
  t2 <- typeCheck ((x, t1) : ctx) body
  return $ TFun t1 t2

typeCheck ctx (App t1 t2) = do
  t1' <- typeCheck ctx t1
  t2' <- typeCheck ctx t2
  case t1' of
    TFun a b | a == t2' -> return b
    _ -> throwError $ "Type mismatch in application: " ++ show t1' ++ " vs " ++ show t2'

typeCheck ctx (Pair t1 t2) = do
  t1' <- typeCheck ctx t1
  t2' <- typeCheck ctx t2
  return $ TProd t1' t2'

typeCheck ctx (Fst t) = do
  t' <- typeCheck ctx t
  case t' of
    TProd a _ -> return a
    _ -> throwError $ "Expected product type, got: " ++ show t'

typeCheck ctx (Snd t) = do
  t' <- typeCheck ctx t
  case t' of
    TProd _ b -> return b
    _ -> throwError $ "Expected product type, got: " ++ show t'

typeCheck ctx (Inl t1 t2) = do
  t2' <- typeCheck ctx t2
  return $ TSum t1 t2'

typeCheck ctx (Inr t1 t2) = do
  t2' <- typeCheck ctx t2
  return $ TSum t2' t1

typeCheck ctx (Case t x1 t1 x2 t2) = do
  t' <- typeCheck ctx t
  case t' of
    TSum a b -> do
      t1' <- typeCheck ((x1, a) : ctx) t1
      t2' <- typeCheck ((x2, b) : ctx) t2
      if t1' == t2' then return t1' else throwError "Case branches have different types"
    _ -> throwError $ "Expected sum type, got: " ++ show t'

typeCheck ctx True = return TBool
typeCheck ctx False = return TBool
typeCheck ctx Zero = return TNat
typeCheck ctx (Succ t) = do
  t' <- typeCheck ctx t
  case t' of
    TNat -> return TNat
    _ -> throwError $ "Expected natural number, got: " ++ show t'

typeCheck ctx (TAbs x t) = do
  t' <- typeCheck ctx t
  return $ TForall x t'

typeCheck ctx (TApp t a) = do
  t' <- typeCheck ctx t
  case t' of
    TForall x b -> return $ substType x a b
    _ -> throwError $ "Expected universal type, got: " ++ show t'

-- Type inference (simplified Hindley-Milner)
data TypeScheme = Forall [String] Type
  deriving (Eq, Show)

type InferenceContext = [(String, TypeScheme)]

-- Unification
unify :: Type -> Type -> TypeCheck (Type -> Type)
unify (TVar x) (TVar y) | x == y = return id
unify (TVar x) t = return $ \s -> if s == TVar x then t else s
unify t (TVar x) = unify (TVar x) t
unify (TFun a1 b1) (TFun a2 b2) = do
  s1 <- unify a1 a2
  s2 <- unify (s1 b1) (s1 b2)
  return $ s2 . s1
unify (TProd a1 b1) (TProd a2 b2) = do
  s1 <- unify a1 a2
  s2 <- unify (s1 b1) (s1 b2)
  return $ s2 . s1
unify t1 t2 | t1 == t2 = return id
unify t1 t2 = throwError $ "Cannot unify: " ++ show t1 ++ " and " ++ show t2

-- Type inference
infer :: InferenceContext -> Term -> TypeCheck Type
infer ctx (Var x) = case lookup x ctx of
  Just (Forall [] t) -> return t
  Just (Forall xs t) -> do
    fresh <- mapM (\_ -> freshVar) xs
    return $ foldr (\x t -> substType x (TVar x) t) t (zip xs fresh)
  Nothing -> throwError $ "Unbound variable: " ++ x

infer ctx (Lam x t1 body) = do
  t2 <- infer ctx body
  return $ TFun t1 t2

infer ctx (App t1 t2) = do
  t1' <- infer ctx t1
  t2' <- infer ctx t2
  a <- freshVar
  s <- unify t1' (TFun t2' (TVar a))
  return $ s (TVar a)

-- Example: Identity function
identity :: Term
identity = Lam "x" (TVar "a") (Var "x")

-- Example: Church numerals
churchZero :: Term
churchZero = Lam "f" (TFun (TVar "a") (TVar "a")) (Lam "x" (TVar "a") (Var "x"))

churchSucc :: Term
churchSucc = Lam "n" (TForall "a" (TFun (TFun (TVar "a") (TVar "a")) (TFun (TVar "a") (TVar "a")))) 
  (Lam "f" (TFun (TVar "a") (TVar "a")) (Lam "x" (TVar "a") 
    (App (Var "f") (App (App (Var "n") (Var "f")) (Var "x")))))

-- Dependent types simulation with GADTs
data Vec a n where
  Nil :: Vec a Zero
  Cons :: a -> Vec a n -> Vec a (Succ n)

data Zero
data Succ n

-- Type-level natural numbers
type family Add n m where
  Add Zero m = m
  Add (Succ n) m = Succ (Add n m)

-- Safe vector concatenation
append :: Vec a n -> Vec a m -> Vec a (Add n m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Safe vector indexing
index :: Vec a n -> Fin n -> a
index (Cons x _) FZ = x
index (Cons _ xs) (FS i) = index xs i

data Fin n where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

-- Example usage
example :: Vec Int (Succ (Succ Zero))
example = Cons 1 (Cons 2 Nil)

-- Type-level programming
type family Length (xs :: [k]) :: Nat where
  Length '[] = Zero
  Length (x ': xs) = Succ (Length xs)

-- Heterogeneous lists
data HList xs where
  HNil :: HList '[]
  HCons :: a -> HList xs -> HList (a ': xs)

-- Safe head operation
hHead :: HList (a ': xs) -> a
hHead (HCons x _) = x
```

## References

1. **Cross-Reference**: [001-Category-Theory](../03-Category-Theory/001-Category-Theory.md) - Mathematical foundation
2. **Cross-Reference**: [001-Functional-Programming](../../haskell/001-Functional-Programming.md) - Programming applications
3. **Cross-Reference**: [002-First-Order-Logic](../02-Formal-Logic/002-First-Order-Logic.md) - Logical foundations

**Academic Sources**:

- Pierce, B. C. (2002). Types and Programming Languages
- Thompson, S. (1991). Type Theory and Functional Programming
- Martin-Löf, P. (1984). Intuitionistic Type Theory

**Next Document**: [002-Dependent-Types](002-Dependent-Types.md)
