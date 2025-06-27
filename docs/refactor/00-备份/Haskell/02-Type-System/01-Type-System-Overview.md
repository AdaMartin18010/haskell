# 2.1 Type System Overview

## 2.1.1 Introduction to Type Systems

### 2.1.1.1 Type System Definition

A **type system** is a formal system for classifying expressions according to the kinds of values they compute. In Haskell, the type system is:

- **Static**: Types are checked at compile time
- **Strong**: No implicit type conversions
- **Polymorphic**: Functions can work with multiple types
- **Inferred**: Types can be automatically deduced

### 2.1.1.2 Type System Hierarchy

The Haskell type system forms a hierarchy:

```text
Type
├── Monotype (concrete types)
│   ├── Basic Types (Int, Bool, Char, etc.)
│   ├── Function Types (a -> b)
│   ├── Tuple Types ((a, b))
│   └── List Types ([a])
├── Polytype (type schemes)
│   ├── Universal Types (∀α.τ)
│   └── Constrained Types (C α => τ)
└── Kind
    ├── * (concrete types)
    ├── * -> * (type constructors)
    └── * -> * -> * (binary type constructors)
```

## 2.1.2 Basic Types and Kinds

### 2.1.2.1 Basic Types

```haskell
-- Basic types with their kinds
data Bool = True | False                    -- :: *
data Char = ...                             -- :: *
data Int = ...                              -- :: *
data Integer = ...                          -- :: *
data Float = ...                            -- :: *
data Double = ...                           -- :: *
data () = ()                                -- :: *

-- Type constructors
data Maybe a = Nothing | Just a            -- :: * -> *
data [] a = [] | a : [a]                   -- :: * -> *
data Either a b = Left a | Right b         -- :: * -> * -> *
```

### 2.1.2.2 Kind System

```haskell
-- Kind inference
:kind Int           -- Int :: *
:kind Maybe         -- Maybe :: * -> *
:kind Maybe Int     -- Maybe Int :: *
:kind Either        -- Either :: * -> * -> *
:kind Either Int    -- Either Int :: * -> *
:kind Either Int Bool -- Either Int Bool :: *

-- Higher-kinded types
data Fix f = In (f (Fix f))                -- :: (* -> *) -> *
data Free f a = Pure a | Free (f (Free f a)) -- :: (* -> *) -> * -> *
```

## 2.1.3 Type Inference

### 2.1.3.1 Hindley-Milner Type System

The **Hindley-Milner type system** provides:

- **Principal types**: Every typable expression has a most general type
- **Type inference**: Types can be automatically deduced
- **Let-polymorphism**: Bound variables can be used polymorphically

### 2.1.3.2 Type Inference Algorithm

```haskell
-- Type inference rules
-- Var: Γ(x) = σ
--     ---------
--     Γ ⊢ x : σ

-- Abs: Γ, x:τ₁ ⊢ e : τ₂
--      -----------------
--      Γ ⊢ λx.e : τ₁ → τ₂

-- App: Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
--      ---------------------------------
--      Γ ⊢ e₁ e₂ : τ₂

-- Let: Γ ⊢ e₁ : σ    Γ, x:σ ⊢ e₂ : τ
--      ------------------------------
--      Γ ⊢ let x = e₁ in e₂ : τ

-- Example type inference
example :: Num a => a -> a -> a
example x y = x + y

-- Type inference steps:
-- 1. x :: a (from parameter)
-- 2. y :: a (from parameter)
-- 3. (+) :: Num a => a -> a -> a (from class)
-- 4. x + y :: a (from application)
-- 5. λx.λy.x + y :: Num a => a -> a -> a (from abstraction)
```

### 2.1.3.3 Type Inference Examples

```haskell
-- Automatic type inference
id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

-- Type inference with constraints
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

-- Type inference with higher-order functions
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- Type inference with type classes
sum :: Num a => [a] -> a
sum [] = 0
sum (x:xs) = x + sum xs
```

## 2.1.4 Polymorphism

### 2.1.4.1 Parametric Polymorphism

**Parametric polymorphism** allows functions to work uniformly over a range of types.

```haskell
-- Parametric polymorphic functions
id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

-- Type constructors with parametric polymorphism
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b
data [] a = [] | a : [a]

-- Higher-order parametric polymorphism
data Fix f = In (f (Fix f))
data Free f a = Pure a | Free (f (Free f a))
```

### 2.1.4.2 Ad Hoc Polymorphism (Overloading)

**Ad hoc polymorphism** allows functions to behave differently for different types.

```haskell
-- Type class-based overloading
class Show a where
    show :: a -> String

instance Show Bool where
    show True = "True"
    show False = "False"

instance Show Int where
    show = showInt

-- Function overloading
(+) :: Num a => a -> a -> a
show :: Show a => a -> String
read :: Read a => String -> a
```

### 2.1.4.3 Rank-N Polymorphism

**Rank-N polymorphism** allows universal quantifiers to appear in function types.

```haskell
-- Rank-1 polymorphism (normal)
id :: forall a. a -> a

-- Rank-2 polymorphism
applyToInt :: (forall a. a -> a) -> Int -> Int
applyToInt f x = f x

-- Rank-N polymorphism
type Rank2 = forall a. (a -> a) -> a -> a
type Rank3 = forall a. ((forall b. b -> b) -> a -> a) -> a -> a

-- Example usage
{-# LANGUAGE RankNTypes #-}

-- Higher-rank function
higherRank :: (forall a. a -> a) -> (Int, Bool)
higherRank f = (f 42, f True)
```

## 2.1.5 Type Classes and Constraints

### 2.1.5.1 Type Class Constraints

```haskell
-- Constrained type variables
constrainedFunction :: (Eq a, Show a) => a -> a -> String
constrainedFunction x y
    | x == y = "Equal: " ++ show x
    | otherwise = "Different: " ++ show x ++ " and " ++ show y

-- Multiple constraints
complexFunction :: (Num a, Ord a, Show a) => a -> a -> String
complexFunction x y
    | x < y = show x ++ " < " ++ show y
    | x > y = show x ++ " > " ++ show y
    | otherwise = show x ++ " = " ++ show y
```

### 2.1.5.2 Constraint Kinds

```haskell
{-# LANGUAGE ConstraintKinds #-}

-- Constraint synonyms
type Numeric a = (Num a, Ord a, Show a)
type Printable a = Show a

-- Functions with constraint kinds
numericFunction :: Numeric a => a -> a -> String
numericFunction x y = show (x + y)

-- Constraint families
class (Show a, Read a) => StringConvertible a
instance StringConvertible Int
instance StringConvertible Bool
```

## 2.1.6 Advanced Type System Features

### 2.1.6.1 GADTs (Generalized Algebraic Data Types)

```haskell
{-# LANGUAGE GADTs #-}

-- GADT with type-level information
data Expr a where
    LitInt :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add :: Expr Int -> Expr Int -> Expr Int
    If :: Expr Bool -> Expr a -> Expr a -> Expr a

-- Type-safe evaluation
eval :: Expr a -> a
eval (LitInt n) = n
eval (LitBool b) = b
eval (Add e1 e2) = eval e1 + eval e2
eval (If cond e1 e2) = if eval cond then eval e1 else eval e2
```

### 2.1.6.2 Type Families

```haskell
{-# LANGUAGE TypeFamilies #-}

-- Type family for list element types
type family Elem xs where
    Elem (x ': xs) = x
    Elem '[] = Void

-- Associated type family
class Collection c where
    type Element c
    empty :: c
    insert :: Element c -> c -> c

instance Collection [a] where
    type Element [a] = a
    empty = []
    insert x xs = x : xs
```

### 2.1.6.3 Dependent Types

```haskell
{-# LANGUAGE DataKinds, GADTs, TypeFamilies #-}

-- Type-level natural numbers
data Nat = Zero | Succ Nat

-- Value-level representation
data SNat (n :: Nat) where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)

-- Type-safe vector
data Vec (n :: Nat) a where
    Nil :: Vec 'Zero a
    Cons :: a -> Vec n a -> Vec ('Succ n) a

-- Type-safe indexing
index :: SNat i -> Vec n a -> a
index SZero (Cons x _) = x
index (SSucc i) (Cons _ xs) = index i xs
```

## 2.1.7 Type System Extensions

### 2.1.7.1 Common Extensions

```haskell
{-# LANGUAGE 
    GADTs,
    TypeFamilies,
    DataKinds,
    KindSignatures,
    RankNTypes,
    ConstraintKinds,
    TypeOperators,
    FlexibleInstances,
    FlexibleContexts,
    UndecidableInstances
#-}

-- Type operators
type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
    '[] ++ ys = ys
    (x ': xs) ++ ys = x ': (xs ++ ys)

-- Kind signatures
data Proxy (a :: k) = Proxy

-- Flexible instances
instance Show (a -> b) where
    show _ = "<function>"
```

### 2.1.7.2 Type System Safety

```haskell
-- Type safety guarantees
-- 1. No runtime type errors
-- 2. Memory safety
-- 3. Referential transparency
-- 4. Termination guarantees (with restrictions)

-- Example of type safety
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- This prevents runtime errors:
-- head [] -- Would crash in unsafe languages
-- safeHead [] -- Returns Nothing safely
```

## 2.1.8 Type System Verification

### 2.1.8.1 Type Checking Algorithm

```haskell
-- Simplified type checking
type TypeEnv = [(String, Type)]
type Type = String -- Simplified for example

-- Type checking function
typeCheck :: TypeEnv -> Expr -> Maybe Type
typeCheck env (Var x) = lookup x env
typeCheck env (App e1 e2) = do
    t1 <- typeCheck env e1
    t2 <- typeCheck env e2
    case t1 of
        "a -> b" | t2 == "a" -> Just "b"
        _ -> Nothing
typeCheck env (Abs x t e) = do
    t' <- typeCheck ((x, t) : env) e
    Just (t ++ " -> " ++ t')
```

### 2.1.8.2 Type System Properties

```haskell
-- Type system properties to verify
-- 1. Progress: Well-typed terms don't get stuck
-- 2. Preservation: Evaluation preserves types
-- 3. Uniqueness: Each term has at most one type
-- 4. Decidability: Type checking terminates

-- Property-based testing
prop_type_preservation :: Expr -> Bool
prop_type_preservation e = case typeCheck [] e of
    Just t -> eval e `hasType` t
    Nothing -> True

prop_type_uniqueness :: Expr -> Bool
prop_type_uniqueness e = 
    case (typeCheck [] e, typeCheck [] e) of
        (Just t1, Just t2) -> t1 == t2
        (Nothing, Nothing) -> True
        _ -> False
```

## 2.1.9 References

- [1.6 Type Classes](../01-Basic-Concepts/06-Type-Classes.md)
- [2.2 Algebraic Data Types](02-Algebraic-Data-Types.md)
- [2.3 Type Classes and Instances](03-Type-Classes-and-Instances.md)
- [3.1 Data Structures Overview](../03-Data-Structures/01-Data-Structures-Overview.md)

---

**Next:** [2.2 Algebraic Data Types](02-Algebraic-Data-Types.md)
