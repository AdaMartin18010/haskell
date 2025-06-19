# 1.6 Type Classes

## 1.6.1 Definition and Mathematical Foundation

### 1.6.1.1 Type Class Definition

A **type class** is a collection of types that share a common interface. Mathematically, a type class $C$ defines:

- A set of types $\mathcal{T}_C$
- A set of operations $\mathcal{O}_C = \{f_1, f_2, \ldots, f_n\}$
- A set of laws $\mathcal{L}_C$ that must be satisfied

### 1.6.1.2 Type Class Hierarchy

A **type class hierarchy** forms a partial order $(\mathcal{C}, \leq)$ where:

- $C_1 \leq C_2$ means $C_1$ is a subclass of $C_2$
- $\mathcal{T}_{C_1} \subseteq \mathcal{T}_{C_2}$
- $\mathcal{O}_{C_2} \subseteq \mathcal{O}_{C_1}$

## 1.6.2 Core Type Classes

### 1.6.2.1 Eq Type Class

```haskell
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    
    -- Default implementation
    x /= y = not (x == y)
    x == y = not (x /= y)

-- Example instance
instance Eq Bool where
    True == True = True
    False == False = True
    _ == _ = False

-- Derived instances
data Color = Red | Green | Blue deriving (Eq, Show)
```

### 1.6.2.2 Ord Type Class

```haskell
class Eq a => Ord a where
    compare :: a -> a -> Ordering
    (<) :: a -> a -> Bool
    (<=) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    max :: a -> a -> a
    min :: a -> a -> a
    
    -- Default implementations
    compare x y
        | x == y = EQ
        | x <= y = LT
        | otherwise = GT
    
    x < y = compare x y == LT
    x <= y = compare x y /= GT
    x > y = compare x y == GT
    x >= y = compare x y /= LT
    max x y = if x <= y then y else x
    min x y = if x <= y then x else y

-- Example instance
instance Ord Color where
    compare Red Red = EQ
    compare Red _ = LT
    compare Green Red = GT
    compare Green Green = EQ
    compare Green _ = LT
    compare Blue _ = GT
```

### 1.6.2.3 Show Type Class

```haskell
class Show a where
    showsPrec :: Int -> a -> ShowS
    show :: a -> String
    showList :: [a] -> ShowS
    
    -- Default implementations
    show x = showsPrec 0 x ""
    showList = showList__ shows

-- Helper function
showList__ :: (a -> String) -> [a] -> String
showList__ _ [] = "[]"
showList__ f (x:xs) = "[" ++ f x ++ showListTail xs
  where
    showListTail [] = "]"
    showListTail (y:ys) = "," ++ f y ++ showListTail ys

-- Example instance
instance Show Color where
    showsPrec _ Red = showString "Red"
    showsPrec _ Green = showString "Green"
    showsPrec _ Blue = showString "Blue"
```

### 1.6.2.4 Read Type Class

```haskell
class Read a where
    readsPrec :: Int -> ReadS a
    readList :: ReadS [a]
    
    -- Default implementation
    readList = readList__ readsPrec

-- Helper function
readList__ :: (Int -> ReadS a) -> ReadS [a]
readList__ _ = readParen False (\r -> [pr | ("[]",s) <- lex r, pr <- [(s,[])]])
    ++ readParen False (\r -> [pr | ("[",s1) <- lex r,
                                   (x,s2) <- readsPrec 0 s1,
                                   (xs,s3) <- readList__ readsPrec s2,
                                   ("]",s4) <- lex s3,
                                   pr <- [(s4,x:xs)]])

-- Example instance
instance Read Color where
    readsPrec _ s = case s of
        "Red" -> [(Red, "")]
        "Green" -> [(Green, "")]
        "Blue" -> [(Blue, "")]
        _ -> []
```

## 1.6.3 Numeric Type Classes

### 1.6.3.1 Num Type Class

```haskell
class (Eq a, Show a) => Num a where
    (+), (-), (*) :: a -> a -> a
    negate :: a -> a
    abs :: a -> a
    signum :: a -> a
    fromInteger :: Integer -> a
    
    -- Default implementation
    x - y = x + negate y

-- Example instance for custom number type
data Complex = Complex Double Double deriving (Eq, Show)

instance Num Complex where
    Complex a b + Complex c d = Complex (a + c) (b + d)
    Complex a b - Complex c d = Complex (a - c) (b - d)
    Complex a b * Complex c d = Complex (a*c - b*d) (a*d + b*c)
    negate (Complex a b) = Complex (-a) (-b)
    abs (Complex a b) = Complex (sqrt (a*a + b*b)) 0
    signum (Complex a b) = Complex (a/r) (b/r) where r = sqrt (a*a + b*b)
    fromInteger n = Complex (fromInteger n) 0
```

### 1.6.3.2 Fractional Type Class

```haskell
class Num a => Fractional a where
    (/) :: a -> a -> a
    recip :: a -> a
    fromRational :: Rational -> a
    
    -- Default implementation
    recip x = 1 / x

instance Fractional Complex where
    Complex a b / Complex c d = Complex ((a*c + b*d)/denom) ((b*c - a*d)/denom)
        where denom = c*c + d*d
    fromRational r = Complex (fromRational r) 0
```

### 1.6.3.3 Floating Type Class

```haskell
class Fractional a => Floating a where
    pi :: a
    exp :: a -> a
    log :: a -> a
    sqrt :: a -> a
    (**) :: a -> a -> a
    logBase :: a -> a -> a
    sin :: a -> a
    cos :: a -> a
    tan :: a -> a
    asin :: a -> a
    acos :: a -> a
    atan :: a -> a
    sinh :: a -> a
    cosh :: a -> a
    tanh :: a -> a
    asinh :: a -> a
    acosh :: a -> a
    atanh :: a -> a
    
    -- Default implementations
    x ** y = exp (log x * y)
    logBase x y = log y / log x
```

## 1.6.4 Functor Type Class

### 1.6.4.1 Functor Definition

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
    
    -- Infix operator
    (<$>) :: (a -> b) -> f a -> f b
    (<$>) = fmap

-- Functor laws
-- 1. fmap id = id
-- 2. fmap (g . f) = fmap g . fmap f

-- Example instances
instance Functor Maybe where
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

instance Functor [] where
    fmap = map

instance Functor (Either e) where
    fmap _ (Left e) = Left e
    fmap f (Right x) = Right (f x)
```

### 1.6.4.2 Applicative Type Class

```haskell
class Functor f => Applicative f where
    pure :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b
    
    -- Derived operations
    liftA2 :: (a -> b -> c) -> f a -> f b -> f c
    liftA2 f x y = f <$> x <*> y
    
    (*>) :: f a -> f b -> f b
    u *> v = pure (const id) <*> u <*> v
    
    (<*) :: f a -> f b -> f a
    u <* v = pure const <*> u <*> v

-- Applicative laws
-- 1. pure id <*> v = v
-- 2. pure f <*> pure x = pure (f x)
-- 3. u <*> pure y = pure ($ y) <*> u
-- 4. u <*> (v <*> w) = pure (.) <*> u <*> v <*> w

instance Applicative Maybe where
    pure = Just
    Nothing <*> _ = Nothing
    Just f <*> x = fmap f x

instance Applicative [] where
    pure x = [x]
    fs <*> xs = [f x | f <- fs, x <- xs]
```

## 1.6.5 Monoid Type Class

### 1.6.5.1 Monoid Definition

```haskell
class Monoid a where
    mempty :: a
    mappend :: a -> a -> a
    
    -- Infix operator
    (<>) :: a -> a -> a
    (<>) = mappend
    
    -- Derived operation
    mconcat :: [a] -> a
    mconcat = foldr mappend mempty

-- Monoid laws
-- 1. mempty <> x = x
-- 2. x <> mempty = x
-- 3. (x <> y) <> z = x <> (y <> z)

-- Example instances
instance Monoid [a] where
    mempty = []
    mappend = (++)

instance Monoid (Sum a) where
    mempty = Sum 0
    mappend (Sum x) (Sum y) = Sum (x + y)

instance Monoid (Product a) where
    mempty = Product 1
    mappend (Product x) (Product y) = Product (x * y)
```

## 1.6.6 Custom Type Classes

### 1.6.6.1 Defining Custom Type Classes

```haskell
-- Type class for types that can be converted to/from strings
class StringConvertible a where
    toString :: a -> String
    fromString :: String -> Maybe a
    
    -- Default implementation
    fromString _ = Nothing

-- Example instance
instance StringConvertible Color where
    toString Red = "red"
    toString Green = "green"
    toString Blue = "blue"
    
    fromString "red" = Just Red
    fromString "green" = Just Green
    fromString "blue" = Just Blue
    fromString _ = Nothing
```

### 1.6.6.2 Multi-Parameter Type Classes

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}

-- Type class for converting between types
class Convert a b where
    convert :: a -> b

instance Convert Int Double where
    convert = fromIntegral

instance Convert Double Int where
    convert = round

instance Convert String Int where
    convert = read

instance Convert Int String where
    convert = show
```

### 1.6.6.3 Functional Dependencies

```haskell
{-# LANGUAGE FunctionalDependencies #-}

-- Type class with functional dependency
class Collection c e | c -> e where
    empty :: c
    insert :: e -> c -> c
    member :: e -> c -> Bool

-- The functional dependency | c -> e means that
-- the collection type c uniquely determines the element type e

instance Eq a => Collection [a] a where
    empty = []
    insert x xs = x : xs
    member x xs = x `elem` xs
```

## 1.6.7 Type Class Deriving

### 1.6.7.1 Automatic Deriving

```haskell
-- Automatically derive common type classes
data Person = Person
    { name :: String
    , age :: Int
    , email :: String
    } deriving (Eq, Ord, Show, Read)

-- Custom deriving
data Tree a = Leaf a | Node (Tree a) (Tree a)
    deriving (Show, Read)

-- Manual instance for custom behavior
instance Eq a => Eq (Tree a) where
    Leaf x == Leaf y = x == y
    Node l1 r1 == Node l2 r2 = l1 == l2 && r1 == r2
    _ == _ = False
```

### 1.6.7.2 Generalized Newtype Deriving

```haskell
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- Derive type classes for newtypes
newtype Age = Age Int
    deriving (Eq, Ord, Show, Read, Num, Integral)

-- This allows Age to inherit all the operations from Int
-- while maintaining type safety
```

## 1.6.8 Type Class Laws and Testing

### 1.6.8.1 Property-Based Testing

```haskell
import Test.QuickCheck

-- Test monoid laws
prop_monoid_left_identity :: (Monoid a, Eq a) => a -> Bool
prop_monoid_left_identity x = mempty <> x == x

prop_monoid_right_identity :: (Monoid a, Eq a) => a -> Bool
prop_monoid_right_identity x = x <> mempty == x

prop_monoid_associativity :: (Monoid a, Eq a) => a -> a -> a -> Bool
prop_monoid_associativity x y z = (x <> y) <> z == x <> (y <> z)

-- Test functor laws
prop_functor_identity :: (Functor f, Eq (f Int)) => f Int -> Bool
prop_functor_identity x = fmap id x == x

prop_functor_composition :: (Functor f, Eq (f Int)) => f Int -> Bool
prop_functor_composition x = fmap (succ . succ) x == fmap succ (fmap succ x)
```

## 1.6.9 References

- [1.5 Monads](05-Monads.md)
- [2.1 Type System Overview](../02-Type-System/01-Type-System-Overview.md)
- [2.2 Algebraic Data Types](../02-Type-System/02-Algebraic-Data-Types.md)
- [3.1 Data Structures Overview](../03-Data-Structures/01-Data-Structures-Overview.md)

---

**Next:** [2.1 Type System Overview](../02-Type-System/01-Type-System-Overview.md)
