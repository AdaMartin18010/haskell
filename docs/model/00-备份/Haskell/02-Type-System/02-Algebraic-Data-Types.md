# 2.2 Algebraic Data Types

## 2.2.1 Mathematical Foundation

### 2.2.1.1 Algebraic Data Type Definition

An **Algebraic Data Type (ADT)** is a composite type formed by combining other types using:

- **Sum types** (disjoint unions): $A + B = A \sqcup B$
- **Product types** (cartesian products): $A \times B = \{(a, b) \mid a \in A, b \in B\}$

### 2.2.1.2 Algebraic Structure

ADTs form an algebraic structure with:

- **Sum**: $A + B$ represents choice between $A$ and $B$
- **Product**: $A \times B$ represents pairing of $A$ and $B$
- **Exponential**: $A \to B$ represents functions from $A$ to $B$
- **Unit**: $1$ represents the singleton type
- **Zero**: $0$ represents the empty type

### 2.2.1.3 Algebraic Laws

```haskell
-- Distributivity: A × (B + C) ≅ (A × B) + (A × C)
-- Associativity: (A + B) + C ≅ A + (B + C)
-- Commutativity: A + B ≅ B + A (up to isomorphism)
-- Identity: A + 0 ≅ A, A × 1 ≅ A
-- Annihilation: A × 0 ≅ 0
```

## 2.2.2 Sum Types (Disjoint Unions)

### 2.2.2.1 Basic Sum Types

```haskell
-- Simple sum type
data Bool = True | False

-- Sum type with data
data Maybe a = Nothing | Just a

-- Multiple constructors
data Color = Red | Green | Blue | Yellow

-- Sum type with different data types
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double
```

### 2.2.2.2 Sum Type Operations

```haskell
-- Pattern matching on sum types
isRed :: Color -> Bool
isRed Red = True
isRed _ = False

-- Case analysis
describeShape :: Shape -> String
describeShape (Circle r) = "Circle with radius " ++ show r
describeShape (Rectangle w h) = "Rectangle " ++ show w ++ "x" ++ show h
describeShape (Triangle a b c) = "Triangle with sides " ++ show [a, b, c]

-- Sum type isomorphism
data Either a b = Left a | Right b

-- Converting between Maybe and Either
maybeToEither :: b -> Maybe a -> Either b a
maybeToEither defaultVal Nothing = Left defaultVal
maybeToEither _ (Just a) = Right a

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Left _) = Nothing
eitherToMaybe (Right b) = Just b
```

### 2.2.2.3 Sum Type Properties

```haskell
-- Cardinality of sum types
-- |A + B| = |A| + |B|
-- |Bool| = 2
-- |Maybe a| = 1 + |a|
-- |Either a b| = |a| + |b|

-- Sum type laws
-- Left (f a) = fmap f (Left a)  -- for Functor
-- Right (f b) = fmap f (Right b)  -- for Functor
```

## 2.2.3 Product Types (Tuples and Records)

### 2.2.3.1 Basic Product Types

```haskell
-- Tuple types (built-in)
type Pair a b = (a, b)
type Triple a b c = (a, b, c)

-- Record types
data Person = Person
    { name :: String
    , age :: Int
    , email :: String
    }

-- Product type with type parameters
data Pair' a b = Pair' a b
data Triple' a b c = Triple' a b c
```

### 2.2.3.2 Product Type Operations

```haskell
-- Tuple operations
fst :: (a, b) -> a
fst (a, _) = a

snd :: (a, b) -> b
snd (_, b) = b

-- Record operations
getName :: Person -> String
getName (Person name _ _) = name

-- Record update
updateAge :: Person -> Int -> Person
updateAge person newAge = person { age = newAge }

-- Product type isomorphism
-- (a, b) ≅ (b, a) (up to isomorphism)
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)
```

### 2.2.3.3 Product Type Properties

```haskell
-- Cardinality of product types
-- |A × B| = |A| × |B|
-- |(a, b)| = |a| × |b|

-- Product type laws
-- fst (a, b) = a
-- snd (a, b) = b
-- (fst p, snd p) = p
```

## 2.2.4 Mixed Algebraic Data Types

### 2.2.4.1 Complex ADTs

```haskell
-- Tree structure (sum of products)
data Tree a = Leaf a | Node (Tree a) (Tree a)

-- List structure (sum of products)
data List a = Nil | Cons a (List a)

-- Expression tree
data Expr = Lit Int | Add Expr Expr | Mul Expr Expr

-- Binary search tree
data BST a = Empty | Node (BST a) a (BST a)
```

### 2.2.4.2 ADT Operations

```haskell
-- Tree operations
treeSize :: Tree a -> Int
treeSize (Leaf _) = 1
treeSize (Node left right) = treeSize left + treeSize right

treeDepth :: Tree a -> Int
treeDepth (Leaf _) = 0
treeDepth (Node left right) = 1 + max (treeDepth left) (treeDepth right)

-- Expression evaluation
evalExpr :: Expr -> Int
evalExpr (Lit n) = n
evalExpr (Add e1 e2) = evalExpr e1 + evalExpr e2
evalExpr (Mul e1 e2) = evalExpr e1 * evalExpr e2
```

## 2.2.5 Recursive Data Types

### 2.2.5.1 Fixed Points

```haskell
-- Fixed point of a functor
newtype Fix f = In { out :: f (Fix f) }

-- List as fixed point
data ListF a r = NilF | ConsF a r
type List' a = Fix (ListF a)

-- Tree as fixed point
data TreeF a r = LeafF a | NodeF r r
type Tree' a = Fix (TreeF a)

-- Catamorphism (fold)
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . out

-- Anamorphism (unfold)
ana :: Functor f => (a -> f a) -> a -> Fix f
ana coalg = In . fmap (ana coalg) . coalg
```

### 2.2.5.2 Recursive Functions

```haskell
-- List operations using catamorphism
listSum :: Num a => [a] -> a
listSum = cata $ \case
    NilF -> 0
    ConsF x acc -> x + acc

listLength :: [a] -> Int
listLength = cata $ \case
    NilF -> 0
    ConsF _ acc -> 1 + acc

-- Tree operations using catamorphism
treeSum :: Num a => Tree a -> a
treeSum = cata $ \case
    LeafF x -> x
    NodeF left right -> left + right
```

## 2.2.6 Type-Level Programming with ADTs

### 2.2.6.1 Type-Level Natural Numbers

```haskell
{-# LANGUAGE DataKinds, GADTs, TypeFamilies #-}

-- Type-level natural numbers
data Nat = Zero | Succ Nat

-- Value-level representation
data SNat (n :: Nat) where
    SZero :: SNat 'Zero
    SSucc :: SNat n -> SNat ('Succ n)

-- Type-level addition
type family Add (n :: Nat) (m :: Nat) :: Nat where
    Add 'Zero m = m
    Add ('Succ n) m = 'Succ (Add n m)

-- Type-safe vector
data Vec (n :: Nat) a where
    Nil :: Vec 'Zero a
    Cons :: a -> Vec n a -> Vec ('Succ n) a

-- Type-safe concatenation
append :: Vec n a -> Vec m a -> Vec (Add n m) a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
```

### 2.2.6.2 Type-Level Lists

```haskell
-- Type-level lists
data HList (xs :: [*]) where
    HNil :: HList '[]
    HCons :: x -> HList xs -> HList (x ': xs)

-- Type-level list operations
type family Length (xs :: [*]) :: Nat where
    Length '[] = 'Zero
    Length (x ': xs) = 'Succ (Length xs)

type family (++) (xs :: [*]) (ys :: [*]) :: [*] where
    '[] ++ ys = ys
    (x ': xs) ++ ys = x ': (xs ++ ys)

-- Type-safe head operation
type family Head (xs :: [*]) :: * where
    Head (x ': xs) = x

-- Value-level head with type safety
hHead :: HList (x ': xs) -> x
hHead (HCons x _) = x
```

## 2.2.7 Advanced ADT Patterns

### 2.2.7.1 GADTs (Generalized Algebraic Data Types)

```haskell
{-# LANGUAGE GADTs #-}

-- GADT with type-level information
data Expr a where
    LitInt :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add :: Expr Int -> Expr Int -> Expr Int
    Mul :: Expr Int -> Expr Int -> Expr Int
    If :: Expr Bool -> Expr a -> Expr a -> Expr a
    Eq :: Expr Int -> Expr Int -> Expr Bool

-- Type-safe evaluation
eval :: Expr a -> a
eval (LitInt n) = n
eval (LitBool b) = b
eval (Add e1 e2) = eval e1 + eval e2
eval (Mul e1 e2) = eval e1 * eval e2
eval (If cond e1 e2) = if eval cond then eval e1 else eval e2
eval (Eq e1 e2) = eval e1 == eval e2
```

### 2.2.7.2 Existential Types

```haskell
{-# LANGUAGE ExistentialQuantification #-}

-- Existential type
data Showable = forall a. Show a => Showable a

-- Using existential types
showShowable :: Showable -> String
showShowable (Showable x) = show x

-- List of showable values
showables :: [Showable]
showables = [Showable 42, Showable True, Showable "hello"]

-- Existential type with constraints
data NumShowable = forall a. (Num a, Show a) => NumShowable a

addNumShowable :: NumShowable -> NumShowable -> NumShowable
addNumShowable (NumShowable x) (NumShowable y) = NumShowable (x + y)
```

### 2.2.7.3 Phantom Types

```haskell
-- Phantom type for type safety
data Safe a = Safe String

-- Type-level tags
data Validated
data Unvalidated

-- Type-safe validation
validate :: Safe Unvalidated -> Maybe (Safe Validated)
validate (Safe s)
    | length s > 0 = Just (Safe s)
    | otherwise = Nothing

-- Type-safe operations
processValidated :: Safe Validated -> String
processValidated (Safe s) = "Processing: " ++ s

-- This would be a type error:
-- processValidated (Safe "unvalidated" :: Safe Unvalidated)
```

## 2.2.8 ADT Laws and Properties

### 2.2.8.1 Algebraic Laws

```haskell
-- Sum type laws
-- Left (f a) = fmap f (Left a)
-- Right (f b) = fmap f (Right b)
-- case (Left a) of Left x -> f x; Right y -> g y = f a
-- case (Right b) of Left x -> f x; Right y -> g y = g b

-- Product type laws
-- fst (a, b) = a
-- snd (a, b) = b
-- (fst p, snd p) = p

-- Distributivity
-- A × (B + C) ≅ (A × B) + (A × C)
distribute :: (a, Either b c) -> Either (a, b) (a, c)
distribute (a, Left b) = Left (a, b)
distribute (a, Right c) = Right (a, c)

undistribute :: Either (a, b) (a, c) -> (a, Either b c)
undistribute (Left (a, b)) = (a, Left b)
undistribute (Right (a, c)) = (a, Right c)
```

### 2.2.8.2 Property-Based Testing

```haskell
import Test.QuickCheck

-- Properties for ADTs
prop_sum_identity :: Either a b -> Bool
prop_sum_identity x = case x of
    Left a -> Left a == x
    Right b -> Right b == x

prop_product_identity :: (a, b) -> Bool
prop_product_identity (a, b) = (fst (a, b), snd (a, b)) == (a, b)

prop_distributivity :: (Int, Either Bool Char) -> Bool
prop_distributivity x = undistribute (distribute x) == x

-- Properties for recursive types
prop_tree_size_positive :: Tree Int -> Bool
prop_tree_size_positive tree = treeSize tree >= 0

prop_tree_depth_positive :: Tree Int -> Bool
prop_tree_depth_positive tree = treeDepth tree >= 0
```

## 2.2.9 ADT Optimization

### 2.2.9.1 Memory Layout

```haskell
-- Unboxed types for performance
{-# LANGUAGE UnboxedTuples #-}

-- Unboxed tuple
unboxedPair :: (# Int, Double #)
unboxedPair = (# 42, 3.14 #)

-- Strict fields
data StrictPair a b = StrictPair !a !b

-- Lazy fields (default)
data LazyPair a b = LazyPair a b

-- Performance comparison
strictEval :: StrictPair Int Int -> Int
strictEval (StrictPair x y) = x + y  -- x and y are already evaluated

lazyEval :: LazyPair Int Int -> Int
lazyEval (LazyPair x y) = x + y  -- x and y are evaluated when needed
```

### 2.2.9.2 ADT Specialization

```haskell
-- Specialized ADTs for performance
data SpecializedList a where
    Empty :: SpecializedList a
    Single :: a -> SpecializedList a
    Multiple :: [a] -> SpecializedList a

-- Optimized operations
specializedLength :: SpecializedList a -> Int
specializedLength Empty = 0
specializedLength (Single _) = 1
specializedLength (Multiple xs) = length xs

-- Conversion functions
toSpecialized :: [a] -> SpecializedList a
toSpecialized [] = Empty
toSpecialized [x] = Single x
toSpecialized xs = Multiple xs

fromSpecialized :: SpecializedList a -> [a]
fromSpecialized Empty = []
fromSpecialized (Single x) = [x]
fromSpecialized (Multiple xs) = xs
```

## 2.2.10 References

- [2.1 Type System Overview](01-Type-System-Overview.md)
- [2.3 Type Classes and Instances](03-Type-Classes-and-Instances.md)
- [3.1 Data Structures Overview](../03-Data-Structures/01-Data-Structures-Overview.md)
- [4.1 Advanced Type System Features](../04-Advanced-Concepts/01-Advanced-Type-System-Features.md)

---

**Next:** [2.3 Type Classes and Instances](03-Type-Classes-and-Instances.md)
