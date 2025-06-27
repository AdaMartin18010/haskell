# 002 - First-Order Logic (Predicate Logic)

## Table of Contents

1. [Introduction](#introduction)
2. [Formal Definitions](#formal-definitions)
3. [Syntax](#syntax)
4. [Semantics](#semantics)
5. [Inference Rules](#inference-rules)
6. [Proof Systems](#proof-systems)
7. [Normal Forms](#normal-forms)
8. [Applications](#applications)
9. [Haskell Implementation](#haskell-implementation)
10. [References](#references)

## Introduction

First-Order Logic (FOL), also known as Predicate Logic, extends propositional logic by introducing:

- **Quantifiers** (∀, ∃)
- **Predicates** (relations)
- **Functions**
- **Variables**

**Cross-Reference**: Builds on [001-Propositional-Logic](001-Propositional-Logic.md) and provides foundation for [003-Non-Classical-Logic](003-Non-Classical-Logic.md).

## Formal Definitions

### Language of First-Order Logic

A first-order language $\mathcal{L}$ consists of:

1. **Logical Symbols**:
   - Variables: $x, y, z, \ldots$
   - Connectives: $\neg, \land, \lor, \rightarrow, \leftrightarrow$
   - Quantifiers: $\forall, \exists$
   - Equality: $=$
   - Parentheses: $(, )$

2. **Non-Logical Symbols**:
   - Function symbols: $f, g, h, \ldots$ with arities
   - Predicate symbols: $P, Q, R, \ldots$ with arities
   - Constants: $a, b, c, \ldots$

### Terms

Terms are defined inductively:

- Variables and constants are terms
- If $f$ is an $n$-ary function symbol and $t_1, \ldots, t_n$ are terms, then $f(t_1, \ldots, t_n)$ is a term

### Formulas

Formulas are defined inductively:

- If $P$ is an $n$-ary predicate and $t_1, \ldots, t_n$ are terms, then $P(t_1, \ldots, t_n)$ is an atomic formula
- If $\phi$ and $\psi$ are formulas, then $\neg\phi$, $\phi \land \psi$, $\phi \lor \psi$, $\phi \rightarrow \psi$, $\phi \leftrightarrow \psi$ are formulas
- If $\phi$ is a formula and $x$ is a variable, then $\forall x \phi$ and $\exists x \phi$ are formulas

## Syntax

### BNF Grammar

```latex
term ::= variable | constant | function_symbol(term_list)
term_list ::= term | term, term_list
formula ::= predicate_symbol(term_list) | term = term | 
           ¬formula | formula ∧ formula | formula ∨ formula |
           formula → formula | formula ↔ formula |
           ∀variable.formula | ∃variable.formula
```

### Free and Bound Variables

- A variable $x$ is **free** in $\phi$ if it's not in the scope of any quantifier
- A variable $x$ is **bound** in $\phi$ if it's in the scope of a quantifier $\forall x$ or $\exists x$

**Definition**: A formula is **closed** (a sentence) if it has no free variables.

## Semantics

### Structures

A **structure** $\mathcal{A}$ for language $\mathcal{L}$ consists of:

- A non-empty domain $A$
- For each constant $c$, an element $c^{\mathcal{A}} \in A$
- For each $n$-ary function symbol $f$, a function $f^{\mathcal{A}}: A^n \rightarrow A$
- For each $n$-ary predicate symbol $P$, a relation $P^{\mathcal{A}} \subseteq A^n$

### Variable Assignments

A **variable assignment** $\sigma$ maps variables to elements of the domain.

### Satisfaction Relation

$\mathcal{A} \models \phi[\sigma]$ means "$\mathcal{A}$ satisfies $\phi$ under assignment $\sigma$":

1. **Atomic formulas**: $\mathcal{A} \models P[t_1, \ldots, t_n](\sigma)$ iff $(t_1^{\mathcal{A}}[\sigma], \ldots, t_n^{\mathcal{A}}[\sigma]) \in P^{\mathcal{A}}$

2. **Connectives**: As in propositional logic

3. **Quantifiers**:
   - $\mathcal{A} \models \forall x \phi[\sigma]$ iff for all $a \in A$, $\mathcal{A} \models \phi[\sigma[x \mapsto a]]$
   - $\mathcal{A} \models \exists x \phi[\sigma]$ iff for some $a \in A$, $\mathcal{A} \models \phi[\sigma[x \mapsto a]]$

## Inference Rules

### Universal Quantifier

**Universal Generalization**:

```latex
φ
---
∀x.φ
```

(if x is not free in any premise)

**Universal Instantiation**:

```latex
∀x.φ
---
φ[t/x]
```

(where t is substitutable for x)

### Existential Quantifier

**Existential Generalization**:

```latex
φ[t/x]
---
∃x.φ
```

**Existential Instantiation**:

```latex
∃x.φ
---
φ[c/x]
```

(where c is a new constant)

### Quantifier Negation

```latex
¬∀x.φ ↔ ∃x.¬φ
¬∃x.φ ↔ ∀x.¬φ
```

## Proof Systems

### Natural Deduction

**Universal Introduction**:

```latex
[φ] (x arbitrary)
...
ψ
---
∀x.ψ
```

**Existential Elimination**:

```latex
∃x.φ    [φ] (x arbitrary)
...     ...
ψ       ψ
---
ψ
```

### Sequent Calculus

**Left Universal**:

```latex
φ[t/x], Γ ⊢ Δ
---
∀x.φ, Γ ⊢ Δ
```

**Right Universal**:

```latex
Γ ⊢ φ, Δ
---
Γ ⊢ ∀x.φ, Δ
```

(x not free in Γ, Δ)

## Normal Forms

### Prenex Normal Form

Every formula can be converted to the form:
$$Q_1x_1 \ldots Q_nx_n \psi$$
where $Q_i$ are quantifiers and $\psi$ is quantifier-free.

**Algorithm**:

1. Eliminate $\leftrightarrow$ using $A \leftrightarrow B \equiv (A \rightarrow B) \land (B \rightarrow A)$
2. Eliminate $\rightarrow$ using $A \rightarrow B \equiv \neg A \lor B$
3. Move negations inward using De Morgan's laws and quantifier negation
4. Move quantifiers to the front

### Skolem Normal Form

Convert to prenex form, then:

- Replace $\exists x \phi(x)$ with $\phi(c)$ where $c$ is a new Skolem constant
- Replace $\forall x_1 \ldots \forall x_n \exists y \phi(x_1, \ldots, x_n, y)$ with $\forall x_1 \ldots \forall x_n \phi(x_1, \ldots, x_n, f(x_1, \ldots, x_n))$ where $f$ is a new Skolem function

## Applications

### Mathematical Reasoning

**Example**: Prove that every natural number has a successor.

**Formalization**:

- Language: $\{0, S, <\}$ where $S$ is successor function
- Axioms:
  - $\forall x (S(x) \neq 0)$
  - $\forall x \forall y (S(x) = S(y) \rightarrow x = y)$
  - $\forall x (x = 0 \lor \exists y (x = S(y)))$

### Database Theory

**Relational Algebra**:

- Relations as predicates
- Queries as formulas
- SQL as first-order logic

**Example**: Find all employees who work in the IT department:
$$\exists d (\text{Works}(e, d) \land \text{Department}(d, \text{"IT"}))$$

### Artificial Intelligence

**Knowledge Representation**:

- Facts as atomic formulas
- Rules as implications
- Queries as existential formulas

**Example**: "All birds can fly except penguins":
$$\forall x (\text{Bird}(x) \land \neg\text{Penguin}(x) \rightarrow \text{CanFly}(x))$$

## Haskell Implementation

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module FirstOrderLogic where

import Data.List (nub)
import Control.Monad.State

-- Types for terms and formulas
data Term = Var String | Const String | Func String [Term]
  deriving (Eq, Show)

data Formula = 
    Pred String [Term]
  | Equal Term Term
  | Not Formula
  | And Formula Formula
  | Or Formula Formula
  | Implies Formula Formula
  | Iff Formula Formula
  | ForAll String Formula
  | Exists String Formula
  deriving (Eq, Show)

-- Free variables in a term
freeVarsTerm :: Term -> [String]
freeVarsTerm (Var x) = [x]
freeVarsTerm (Const _) = []
freeVarsTerm (Func _ terms) = concatMap freeVarsTerm terms

-- Free variables in a formula
freeVars :: Formula -> [String]
freeVars (Pred _ terms) = concatMap freeVarsTerm terms
freeVars (Equal t1 t2) = freeVarsTerm t1 ++ freeVarsTerm t2
freeVars (Not phi) = freeVars phi
freeVars (And phi psi) = freeVars phi ++ freeVars psi
freeVars (Or phi psi) = freeVars phi ++ freeVars psi
freeVars (Implies phi psi) = freeVars phi ++ freeVars psi
freeVars (Iff phi psi) = freeVars phi ++ freeVars psi
freeVars (ForAll x phi) = filter (/= x) (freeVars phi)
freeVars (Exists x phi) = filter (/= x) (freeVars phi)

-- Check if a formula is closed (a sentence)
isClosed :: Formula -> Bool
isClosed = null . freeVars

-- Substitution in terms
substTerm :: String -> Term -> Term -> Term
substTerm x t (Var y) | x == y = t
substTerm x t (Var y) | x /= y = Var y
substTerm _ _ (Const c) = Const c
substTerm x t (Func f terms) = Func f (map (substTerm x t) terms)

-- Substitution in formulas
subst :: String -> Term -> Formula -> Formula
subst x t (Pred p terms) = Pred p (map (substTerm x t) terms)
subst x t (Equal t1 t2) = Equal (substTerm x t t1) (substTerm x t t2)
subst x t (Not phi) = Not (subst x t phi)
subst x t (And phi psi) = And (subst x t phi) (subst x t psi)
subst x t (Or phi psi) = Or (subst x t phi) (subst x t psi)
subst x t (Implies phi psi) = Implies (subst x t phi) (subst x t psi)
subst x t (Iff phi psi) = Iff (subst x t phi) (subst x t psi)
subst x t (ForAll y phi) | x == y = ForAll y phi
subst x t (ForAll y phi) | x /= y = ForAll y (subst x t phi)
subst x t (Exists y phi) | x == y = Exists y phi
subst x t (Exists y phi) | x /= y = Exists y (subst x t phi)

-- Prenex normal form conversion
prenexNormalForm :: Formula -> Formula
prenexNormalForm = moveQuantifiers . eliminateImplications . eliminateIff

eliminateIff :: Formula -> Formula
eliminateIff (Iff phi psi) = And (Implies phi psi) (Implies psi phi)
eliminateIff (Not phi) = Not (eliminateIff phi)
eliminateIff (And phi psi) = And (eliminateIff phi) (eliminateIff psi)
eliminateIff (Or phi psi) = Or (eliminateIff phi) (eliminateIff psi)
eliminateIff (Implies phi psi) = Implies (eliminateIff phi) (eliminateIff psi)
eliminateIff (ForAll x phi) = ForAll x (eliminateIff phi)
eliminateIff (Exists x phi) = Exists x (eliminateIff phi)
eliminateIff phi = phi

eliminateImplications :: Formula -> Formula
eliminateImplications (Implies phi psi) = Or (Not (eliminateImplications phi)) (eliminateImplications psi)
eliminateImplications (Not phi) = Not (eliminateImplications phi)
eliminateImplications (And phi psi) = And (eliminateImplications phi) (eliminateImplications psi)
eliminateImplications (Or phi psi) = Or (eliminateImplications phi) (eliminateImplications psi)
eliminateImplications (ForAll x phi) = ForAll x (eliminateImplications phi)
eliminateImplications (Exists x phi) = Exists x (eliminateImplications phi)
eliminateImplications phi = phi

moveQuantifiers :: Formula -> Formula
moveQuantifiers = undefined -- Complex implementation for moving quantifiers to front

-- Example: Peano arithmetic axioms
peanoAxioms :: [Formula]
peanoAxioms = [
  -- Zero is not a successor
  ForAll "x" (Not (Equal (Func "S" [Var "x"]) (Const "0"))),
  
  -- Successor function is injective
  ForAll "x" (ForAll "y" (Implies 
    (Equal (Func "S" [Var "x"]) (Func "S" [Var "y"]))
    (Equal (Var "x") (Var "y")))),
  
  -- Mathematical induction (simplified)
  ForAll "x" (Or (Equal (Var "x") (Const "0")) 
    (Exists "y" (Equal (Var "x") (Func "S" [Var "y"]))))
]

-- Theorem prover (simplified)
prove :: [Formula] -> Formula -> Bool
prove axioms goal = undefined -- Implementation would use resolution or tableaux

-- Example usage
example :: Bool
example = do
  let phi = ForAll "x" (Exists "y" (Equal (Func "S" [Var "y"]) (Var "x")))
  let isSentence = isClosed phi
  let freeVarsList = freeVars phi
  isSentence && null freeVarsList
```

## References

1. **Cross-Reference**: [001-Propositional-Logic](001-Propositional-Logic.md) - Foundation
2. **Cross-Reference**: [003-Non-Classical-Logic](003-Non-Classical-Logic.md) - Extensions
3. **Cross-Reference**: [001-Set-Theory](../01-Mathematics/001-Set-Theory.md) - Mathematical foundation
4. **Cross-Reference**: [001-Functional-Programming](../../haskell/001-Functional-Programming.md) - Programming paradigm

**Academic Sources**:

- Enderton, H. B. (2001). A Mathematical Introduction to Logic
- Boolos, G., Burgess, J. P., & Jeffrey, R. C. (2007). Computability and Logic
- Smullyan, R. M. (1995). First-Order Logic

**Next Document**: [003-Non-Classical-Logic](003-Non-Classical-Logic.md)
