# 2.3 Type Classes and Instances

## 2.3.1 Mathematical Foundation

### 2.3.1.1 Type Class Definition

A **type class** is a collection of types that share a common interface. Mathematically, a type class $C$ defines:

- A set of types $\mathcal{T}_C$
- A set of operations $\mathcal{O}_C = \{f_1, f_2, \ldots, f_n\}$
- A set of laws $\mathcal{L}_C$ that must be satisfied

### 2.3.1.2 Type Class Hierarchy

A **type class hierarchy** forms a partial order $(\mathcal{C}, \leq)$ where:

- $C_1 \leq C_2$ means $C_1$ is a subclass of $C_2$
- $\mathcal{T}_{C_1} \subseteq \mathcal{T}_{C_2}$
- $\mathcal{O}_{C_2} \subseteq \mathcal{O}_{C_1}$

### 2.3.1.3 Constraint Satisfaction

A type $T$ satisfies a type class $C$ if:

- $T \in \mathcal{T}_C$
- All operations in $\mathcal{O}_C$ are implemented for $T$
- All laws in $\mathcal{L}_C$ are satisfied

## 2.3.2 Core Type Classes

### 2.3.2.1 Eq Type Class

```haskell
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    
    -- Default implementation
    x /= y = not (x == y)
    x == y = not (x /= y)

-- Example instances
instance Eq Bool where
    True == True = True
    False == False = True
    _ == _ = False

instance Eq Int where
    (==) = (==)  -- Use built-in equality

-- Derived instances
data Color = Red | Green | Blue deriving (Eq, Show)

-- Custom instance
data Complex = Complex Double Double deriving Show

instance Eq Complex where
    Complex a b == Complex c d = abs (a - c) < epsilon && abs (b - d) < epsilon
        where epsilon = 1e-10
```

### 2.3.2.2 Ord Type Class

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

-- Example instances
instance Ord Color where
    compare Red Red = EQ
    compare Red _ = LT
    compare Green Red = GT
    compare Green Green = EQ
    compare Green _ = LT
    compare Blue _ = GT

instance Ord Complex where
    compare (Complex a b) (Complex c d) = compare (a*a + b*b) (c*c + d*d)
```

### 2.3.2.3 Show and Read Type Classes

```haskell
class Show a where
    showsPrec :: Int -> a -> ShowS
    show :: a -> String
    showList :: [a] -> ShowS
    
    -- Default implementations
    show x = showsPrec 0 x ""
    showList = showList__ shows

class Read a where
    readsPrec :: Int -> ReadS a
    readList :: ReadS [a]
    
    -- Default implementation
    readList = readList__ readsPrec

-- Example instances
instance Show Color where
    showsPrec _ Red = showString "Red"
    showsPrec _ Green = showString "Green"
    showsPrec _ Blue = showString "Blue"

instance Read Color where
    readsPrec _ s = case s of
        "Red" -> [(Red, "")]
        "Green" -> [(Green, "")]
        "Blue" -> [(Blue, "")]
        _ -> []

-- Custom show instance
instance Show Complex where
    show (Complex a b)
        | b >= 0 = show a ++ "+" ++ show b ++ "i"
        | otherwise = show a ++ show b ++ "i"
```

## 2.3.3 Numeric Type Classes

### 2.3.3.1 Num Type Class

```haskell
class (Eq a, Show a) => Num a where
    (+), (-), (*) :: a -> a -> a
    negate :: a -> a
    abs :: a -> a
    signum :: a -> a
    fromInteger :: Integer -> a
    
    -- Default implementation
    x - y = x + negate y

-- Example instance for Complex numbers
instance Num Complex where
    Complex a b + Complex c d = Complex (a + c) (b + d)
    Complex a b - Complex c d = Complex (a - c) (b - d)
    Complex a b * Complex c d = Complex (a*c - b*d) (a*d + b*c)
    negate (Complex a b) = Complex (-a) (-b)
    abs (Complex a b) = Complex (sqrt (a*a + b*b)) 0
    signum (Complex a b) = Complex (a/r) (b/r) where r = sqrt (a*a + b*b)
    fromInteger n = Complex (fromInteger n) 0
```

### 2.3.3.2 Fractional and Floating Type Classes

```haskell
class Num a => Fractional a where
    (/) :: a -> a -> a
    recip :: a -> a
    fromRational :: Rational -> a
    
    -- Default implementation
    recip x = 1 / x

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

-- Example instances
instance Fractional Complex where
    Complex a b / Complex c d = Complex ((a*c + b*d)/denom) ((b*c - a*d)/denom)
        where denom = c*c + d*d
    fromRational r = Complex (fromRational r) 0

instance Floating Complex where
    pi = Complex pi 0
    exp (Complex a b) = Complex (exp a * cos b) (exp a * sin b)
    log (Complex a b) = Complex (log (sqrt (a*a + b*b))) (atan2 b a)
    sqrt (Complex a b) = Complex (sqrt ((a + r)/2)) (signum b * sqrt ((r - a)/2))
        where r = sqrt (a*a + b*b)
```

## 2.3.4 Functor and Applicative Type Classes

### 2.3.4.1 Functor Type Class

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

instance Functor ((->) r) where
    fmap = (.)

-- Custom functor instance
data Tree a = Leaf a | Node (Tree a) (Tree a)

instance Functor Tree where
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Node left right) = Node (fmap f left) (fmap f right)
```

### 2.3.4.2 Applicative Type Class

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

instance Applicative ((->) r) where
    pure = const
    f <*> g = \x -> f x (g x)

-- Custom applicative instance
instance Applicative Tree where
    pure x = Leaf x
    Leaf f <*> Leaf x = Leaf (f x)
    Leaf f <*> Node left right = Node (fmap f left) (fmap f right)
    Node left right <*> Leaf x = Node (left <*> pure x) (right <*> pure x)
    Node left right <*> Node left' right' = Node (left <*> left') (right <*> right')
```

## 2.3.5 Monad Type Class

### 2.3.5.1 Monad Definition

```haskell
class Applicative m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b
    
    -- Derived operations
    (>>) :: m a -> m b -> m b
    m >> n = m >>= \_ -> n
    
    fail :: String -> m a
    fail msg = error msg

-- Monad laws
-- 1. return a >>= f ≡ f a (left identity)
-- 2. m >>= return ≡ m (right identity)
-- 3. (m >>= f) >>= g ≡ m >>= (\x -> f x >>= g) (associativity)

-- Example instances
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= f = f x

instance Monad [] where
    return x = [x]
    xs >>= f = concat (map f xs)

instance Monad (Either e) where
    return = Right
    Left e >>= _ = Left e
    Right x >>= f = f x

-- Custom monad instance
instance Monad Tree where
    return = Leaf
    Leaf x >>= f = f x
    Node left right >>= f = Node (left >>= f) (right >>= f)
```

### 2.3.5.2 Monad Transformers

```haskell
-- MaybeT transformer
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Monad (MaybeT m) where
    return = MaybeT . return . Just
    MaybeT m >>= f = MaybeT $ do
        maybeVal <- m
        case maybeVal of
            Nothing -> return Nothing
            Just x -> runMaybeT (f x)

-- StateT transformer
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance Monad m => Monad (StateT s m) where
    return a = StateT $ \s -> return (a, s)
    StateT f >>= g = StateT $ \s -> do
        (a, s') <- f s
        runStateT (g a) s'

-- Lifting operations
lift :: Monad m => m a -> MaybeT m a
lift m = MaybeT $ do
    a <- m
    return (Just a)

liftState :: Monad m => m a -> StateT s m a
liftState m = StateT $ \s -> do
    a <- m
    return (a, s)
```

## 2.3.6 Custom Type Classes

### 2.3.6.1 Defining Custom Type Classes

```haskell
-- Type class for types that can be converted to/from strings
class StringConvertible a where
    toString :: a -> String
    fromString :: String -> Maybe a
    
    -- Default implementation
    fromString _ = Nothing

-- Type class for types that can be serialized
class Serializable a where
    serialize :: a -> String
    deserialize :: String -> Maybe a
    
    -- Default implementation using Show/Read
    serialize = show
    deserialize = readMaybe

-- Type class for types that have a default value
class Default a where
    def :: a

-- Example instances
instance StringConvertible Color where
    toString Red = "red"
    toString Green = "green"
    toString Blue = "blue"
    
    fromString "red" = Just Red
    fromString "green" = Just Green
    fromString "blue" = Just Blue
    fromString _ = Nothing

instance Serializable Color where
    serialize = toString
    deserialize = fromString

instance Default Color where
    def = Red
```

### 2.3.6.2 Multi-Parameter Type Classes

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

-- Type class for comparing different types
class Comparable a b where
    compare' :: a -> b -> Ordering

instance Comparable Int Double where
    compare' i d = compare (fromIntegral i) d

instance Comparable Double Int where
    compare' d i = compare d (fromIntegral i)
```

### 2.3.6.3 Functional Dependencies

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

-- Type class with multiple functional dependencies
class Map k v m | m -> k, m -> v where
    emptyMap :: m
    insertMap :: k -> v -> m -> m
    lookupMap :: k -> m -> Maybe v

instance (Eq k, Ord k) => Map k v (Data.Map.Map k v) where
    emptyMap = Data.Map.empty
    insertMap = Data.Map.insert
    lookupMap = Data.Map.lookup
```

## 2.3.7 Type Class Deriving

### 2.3.7.1 Automatic Deriving

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

-- Deriving with custom behavior
data CustomList a = Empty | Cons a (CustomList a)
    deriving (Show, Read)

instance Eq a => Eq (CustomList a) where
    Empty == Empty = True
    Cons x xs == Cons y ys = x == y && xs == ys
    _ == _ = False
```

### 2.3.7.2 Generalized Newtype Deriving

```haskell
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- Derive type classes for newtypes
newtype Age = Age Int
    deriving (Eq, Ord, Show, Read, Num, Integral)

-- This allows Age to inherit all the operations from Int
-- while maintaining type safety

newtype SafeString = SafeString String
    deriving (Show, Read, Monoid)

-- Derive with constraints
newtype NonEmpty a = NonEmpty [a]
    deriving (Show, Read)

instance Eq a => Eq (NonEmpty a) where
    NonEmpty xs == NonEmpty ys = xs == ys
```

### 2.3.7.3 Standalone Deriving

```haskell
{-# LANGUAGE StandaloneDeriving #-}

-- Standalone deriving declarations
data Complex a = Complex a a

deriving instance (Show a) => Show (Complex a)
deriving instance (Eq a) => Eq (Complex a)
deriving instance (Num a) => Num (Complex a)

-- Deriving with custom context
data Wrapper a = Wrapper a

deriving instance (Show a, Ord a) => Show (Wrapper a)
deriving instance (Eq a, Ord a) => Eq (Wrapper a)
```

## 2.3.8 Type Class Laws and Testing

### 2.3.8.1 Law Verification

```haskell
import Test.QuickCheck

-- Functor laws
prop_functor_identity :: (Functor f, Eq (f Int)) => f Int -> Bool
prop_functor_identity x = fmap id x == x

prop_functor_composition :: (Functor f, Eq (f Int)) => f Int -> Bool
prop_functor_composition x = fmap (succ . succ) x == fmap succ (fmap succ x)

-- Applicative laws
prop_applicative_identity :: (Applicative f, Eq (f Int)) => f Int -> Bool
prop_applicative_identity v = (pure id <*> v) == v

prop_applicative_homomorphism :: (Applicative f, Eq (f Int)) => Int -> Bool
prop_applicative_homomorphism x = (pure succ <*> pure x) == pure (succ x)

-- Monad laws
prop_monad_left_identity :: (Monad m, Eq (m Int)) => Int -> (Int -> m Int) -> Bool
prop_monad_left_identity a f = (return a >>= f) == f a

prop_monad_right_identity :: (Monad m, Eq (m Int)) => m Int -> Bool
prop_monad_right_identity m = (m >>= return) == m

prop_monad_associativity :: (Monad m, Eq (m Int)) => m Int -> (Int -> m Int) -> (Int -> m Int) -> Bool
prop_monad_associativity m f g = ((m >>= f) >>= g) == (m >>= (\x -> f x >>= g))
```

### 2.3.8.2 Custom Law Testing

```haskell
-- Custom type class laws
class MyClass a where
    operation :: a -> a -> a
    identity :: a

-- Law: operation x identity == x
prop_myclass_identity :: (MyClass a, Eq a) => a -> Bool
prop_myclass_identity x = operation x identity == x

-- Law: operation x y == operation y x (commutativity)
prop_myclass_commutativity :: (MyClass a, Eq a) => a -> a -> Bool
prop_myclass_commutativity x y = operation x y == operation y x

-- Law: operation (operation x y) z == operation x (operation y z) (associativity)
prop_myclass_associativity :: (MyClass a, Eq a) => a -> a -> a -> Bool
prop_myclass_associativity x y z = operation (operation x y) z == operation x (operation y z)
```

## 2.3.9 Advanced Type Class Patterns

### 2.3.9.1 Type Class Families

```haskell
{-# LANGUAGE TypeFamilies #-}

-- Associated type family
class Collection c where
    type Element c
    empty :: c
    insert :: Element c -> c -> c

instance Collection [a] where
    type Element [a] = a
    empty = []
    insert x xs = x : xs

-- Type family with constraints
class Indexed c where
    type Index c
    type Value c
    lookup :: Index c -> c -> Maybe (Value c)

instance Indexed (Data.Map.Map k v) where
    type Index (Data.Map.Map k v) = k
    type Value (Data.Map.Map k v) = v
    lookup = Data.Map.lookup
```

### 2.3.9.2 Default Method Signatures

```haskell
{-# LANGUAGE DefaultSignatures #-}

-- Type class with default method signatures
class MyShow a where
    myShow :: a -> String
    default myShow :: Show a => a -> String
    myShow = show

-- Instance can use default or provide custom implementation
instance MyShow Int  -- Uses default
instance MyShow Bool -- Uses default

-- Custom instance
data CustomType = CustomType Int

instance MyShow CustomType where
    myShow (CustomType n) = "Custom(" ++ show n ++ ")"
```

### 2.3.9.3 Type Class Instances with Overlapping

```haskell
{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}

-- Overlapping instances
instance Show (a -> b) where
    show _ = "<function>"

instance {-# OVERLAPPABLE #-} Show a where
    show = showDefault

-- Instance with specific type
instance Show (Int -> Int) where
    show _ = "<int function>"
```

## 2.3.10 References

- [2.1 Type System Overview](01-Type-System-Overview.md)
- [2.2 Algebraic Data Types](02-Algebraic-Data-Types.md)
- [1.5 Monads](../01-Basic-Concepts/05-Monads.md)
- [4.1 Advanced Type System Features](../04-Advanced-Concepts/01-Advanced-Type-System-Features.md)

---

**Next:** [3.1 Data Structures Overview](../03-Data-Structures/01-Data-Structures-Overview.md)
