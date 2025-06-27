# 1.5 Monads

## 1.5.1 Definition and Mathematical Foundation

### 1.5.1.1 Monad Definition

A **monad** is a triple $(M, \eta, \mu)$ where:

- $M : \mathcal{C} \to \mathcal{C}$ is an endofunctor
- $\eta : 1_{\mathcal{C}} \Rightarrow M$ (unit/return)
- $\mu : M \circ M \Rightarrow M$ (join/bind)

**Monad Laws:**

1. **Left Identity:** $\mu \circ (\eta \otimes M) = 1_M$
2. **Right Identity:** $\mu \circ (M \otimes \eta) = 1_M$
3. **Associativity:** $\mu \circ (M \otimes \mu) = \mu \circ (\mu \otimes M)$

### 1.5.1.2 Kleisli Composition

For a monad $M$, the **Kleisli category** $\mathcal{C}_M$ has:

- Objects: same as $\mathcal{C}$
- Morphisms: $A \to M B$
- Composition: $g \circ_K f = \mu \circ M g \circ f$

## 1.5.2 Haskell Monad Implementation

### 1.5.2.1 Monad Typeclass

```haskell
class Monad m where
    return :: a -> m a
    (>>=)  :: m a -> (a -> m b) -> m b
    
    -- Derived operations
    (>>)   :: m a -> m b -> m b
    m >> n = m >>= \_ -> n
    
    fail   :: String -> m a
    fail msg = error msg
```

### 1.5.2.2 Monad Laws in Haskell

```haskell
-- Left identity: return a >>= f ≡ f a
leftIdentity :: (Monad m, Eq (m b)) => a -> (a -> m b) -> Bool
leftIdentity a f = (return a >>= f) == f a

-- Right identity: m >>= return ≡ m
rightIdentity :: (Monad m, Eq (m a)) => m a -> Bool
rightIdentity m = (m >>= return) == m

-- Associativity: (m >>= f) >>= g ≡ m >>= (\x -> f x >>= g)
associativity :: (Monad m, Eq (m c)) => m a -> (a -> m b) -> (b -> m c) -> Bool
associativity m f g = ((m >>= f) >>= g) == (m >>= (\x -> f x >>= g))
```

## 1.5.3 Common Monads

### 1.5.3.1 Maybe Monad

```haskell
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= f = f x

-- Example usage
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

safeSqrt :: Double -> Maybe Double
safeSqrt x
    | x < 0 = Nothing
    | otherwise = Just (sqrt x)

-- Chaining operations
safeCalculation :: Double -> Double -> Maybe Double
safeCalculation x y = do
    quotient <- safeDivide x y
    result <- safeSqrt quotient
    return result
```

### 1.5.3.2 List Monad

```haskell
instance Monad [] where
    return x = [x]
    xs >>= f = concat (map f xs)

-- Example: Cartesian product
cartesianProduct :: [a] -> [b] -> [(a, b)]
cartesianProduct xs ys = do
    x <- xs
    y <- ys
    return (x, y)

-- List comprehension equivalent
cartesianProduct' :: [a] -> [b] -> [(a, b)]
cartesianProduct' xs ys = [(x, y) | x <- xs, y <- ys]
```

### 1.5.3.3 State Monad

```haskell
newtype State s a = State { runState :: s -> (a, s) }

instance Monad (State s) where
    return a = State $ \s -> (a, s)
    State f >>= g = State $ \s ->
        let (a, s') = f s
            State h = g a
        in h s'

-- State operations
get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((), f s)

-- Example: Counter
type Counter = State Int

increment :: Counter ()
increment = modify (+1)

decrement :: Counter ()
decrement = modify (subtract 1)

getCount :: Counter Int
getCount = get

-- Usage
counterExample :: (Int, Int)
counterExample = runState (do
    increment
    increment
    increment
    getCount) 0
```

## 1.5.4 Monad Transformers

### 1.5.4.1 Transformer Definition

A **monad transformer** is a type constructor $T$ that takes a monad $M$ and produces a new monad $T M$.

### 1.5.4.2 MaybeT Transformer

```haskell
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Monad (MaybeT m) where
    return = MaybeT . return . Just
    MaybeT m >>= f = MaybeT $ do
        maybeVal <- m
        case maybeVal of
            Nothing -> return Nothing
            Just x -> runMaybeT (f x)

-- Lifting operations
lift :: Monad m => m a -> MaybeT m a
lift m = MaybeT $ do
    a <- m
    return (Just a)
```

### 1.5.4.3 StateT Transformer

```haskell
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance Monad m => Monad (StateT s m) where
    return a = StateT $ \s -> return (a, s)
    StateT f >>= g = StateT $ \s -> do
        (a, s') <- f s
        runStateT (g a) s'

-- Lifting
lift :: Monad m => m a -> StateT s m a
lift m = StateT $ \s -> do
    a <- m
    return (a, s)
```

## 1.5.5 Monad Laws Verification

### 1.5.5.1 Property-Based Testing

```haskell
import Test.QuickCheck

-- QuickCheck properties for monad laws
prop_leftIdentity :: (Monad m, Eq (m Int)) => Int -> (Int -> m Int) -> Property
prop_leftIdentity a f = (return a >>= f) === f a

prop_rightIdentity :: (Monad m, Eq (m Int)) => m Int -> Property
prop_rightIdentity m = (m >>= return) === m

prop_associativity :: (Monad m, Eq (m Int)) => m Int -> (Int -> m Int) -> (Int -> m Int) -> Property
prop_associativity m f g = ((m >>= f) >>= g) === (m >>= (\x -> f x >>= g))
```

## 1.5.6 Advanced Monad Concepts

### 1.5.6.1 MonadPlus

```haskell
class Monad m => MonadPlus m where
    mzero :: m a
    mplus :: m a -> m a -> m a

instance MonadPlus Maybe where
    mzero = Nothing
    mplus Nothing y = y
    mplus x _ = x

instance MonadPlus [] where
    mzero = []
    mplus = (++)
```

### 1.5.6.2 Monad Comprehensions

```haskell
-- List comprehension syntax for monads
monadComprehension :: [Int] -> [Int] -> [(Int, Int)]
monadComprehension xs ys = do
    x <- xs
    y <- ys
    guard (x + y > 5)
    return (x, y)

-- Using MonadComprehensions extension
{-# LANGUAGE MonadComprehensions #-}
monadComprehension' :: Maybe Int -> Maybe Int -> Maybe (Int, Int)
monadComprehension' mx my = [(x, y) | x <- mx, y <- my]
```

## 1.5.7 References

- [1.4 Higher-Order Functions](04-Higher-Order-Functions.md)
- [2.1 Type Classes](../02-Type-System/01-Type-Classes.md)
- [3.1 Algebraic Data Types](../03-Data-Structures/01-Algebraic-Data-Types.md)
- [4.1 Error Handling](../04-Advanced-Concepts/01-Error-Handling.md)

---

**Next:** [1.6 Type Classes](06-Type-Classes.md)
