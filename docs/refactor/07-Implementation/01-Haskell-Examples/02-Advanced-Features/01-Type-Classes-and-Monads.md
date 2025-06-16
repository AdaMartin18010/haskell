# 类型类与单子 - 高级特性

## 概述

本文档介绍Haskell中的高级特性，包括类型类、单子、函子等核心概念，以及它们在形式化编程中的应用。

## 类型类基础

### 类型类定义

类型类是Haskell中实现多态性的核心机制，它允许我们为不同类型定义相同的行为。

```haskell
-- 基本类型类定义
class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
    
    -- 默认实现
    x /= y = not (x == y)

-- 实例化类型类
instance Eq Bool where
    True == True = True
    False == False = True
    _ == _ = False

-- 派生实例
data Color = Red | Green | Blue deriving (Eq, Show)
```

### 数学形式化

类型类可以形式化为：

$$\text{Class}(C) = \{ \text{methods}_1, \text{methods}_2, \ldots, \text{methods}_n \}$$

其中每个方法都有类型签名：

$$\text{method}_i : \tau_1 \rightarrow \tau_2 \rightarrow \ldots \rightarrow \tau_n$$

### 类型类层次结构

```haskell
-- 基本类型类层次
class Eq a => Ord a where
    compare :: a -> a -> Ordering
    (<) :: a -> a -> Bool
    (<=) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    max :: a -> a -> a
    min :: a -> a -> a

-- 数值类型类
class (Eq a, Show a) => Num a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    negate :: a -> a
    abs :: a -> a
    signum :: a -> a
    fromInteger :: Integer -> a
```

## 函子 (Functor)

### 函子定义

函子是范畴论中的重要概念，在Haskell中用于表示可以被映射的类型构造器。

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
    
    -- 函子定律
    -- fmap id = id
    -- fmap (g . h) = fmap g . fmap h

-- Maybe函子实例
instance Functor Maybe where
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

-- 列表函子实例
instance Functor [] where
    fmap = map
```

### 数学形式化

函子满足以下定律：

1. **单位律**: $F(id_A) = id_{F(A)}$
2. **复合律**: $F(g \circ h) = F(g) \circ F(h)$

### 应用示例

```haskell
-- 使用函子进行数据转换
data Point = Point { x :: Double, y :: Double } deriving Show

-- 转换坐标
transformPoint :: (Double -> Double) -> Point -> Point
transformPoint f (Point x y) = Point (f x) (f y)

-- 使用函子处理Maybe值
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- 应用函数到Maybe值
result1 = fmap (*2) (Just 5)  -- Just 10
result2 = fmap (*2) Nothing   -- Nothing
```

## 应用函子 (Applicative)

### 应用函子定义

应用函子扩展了函子的概念，允许将包装在上下文中的函数应用到包装的值上。

```haskell
class Functor f => Applicative f where
    pure :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b
    
    -- 应用函子定律
    -- pure id <*> v = v
    -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    -- pure f <*> pure x = pure (f x)
    -- u <*> pure y = pure ($ y) <*> u

-- Maybe应用函子实例
instance Applicative Maybe where
    pure = Just
    Nothing <*> _ = Nothing
    _ <*> Nothing = Nothing
    Just f <*> Just x = Just (f x)
```

### 数学形式化

应用函子是一个幺半群函子，满足：

$$\text{pure} : A \rightarrow F(A)$$
$$\text{ap} : F(A \rightarrow B) \times F(A) \rightarrow F(B)$$

### 应用示例

```haskell
-- 组合多个Maybe值
combineMaybe :: Maybe Int -> Maybe Int -> Maybe Int
combineMaybe x y = (+) <$> x <*> y

-- 使用应用函子进行验证
data Person = Person { name :: String, age :: Int } deriving Show

validateName :: String -> Maybe String
validateName "" = Nothing
validateName name = Just name

validateAge :: Int -> Maybe Int
validateAge age | age < 0 || age > 150 = Nothing
                | otherwise = Just age

createPerson :: String -> Int -> Maybe Person
createPerson name age = Person <$> validateName name <*> validateAge age
```

## 单子 (Monad)

### 单子定义

单子是Haskell中最强大的抽象之一，用于处理顺序计算和副作用。

```haskell
class Applicative m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b
    
    -- 单子定律
    -- return a >>= k = k a
    -- m >>= return = m
    -- m >>= (\x -> k x >>= h) = (m >>= k) >>= h

-- Maybe单子实例
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= k = k x
```

### 数学形式化

单子是一个三元组 $(T, \eta, \mu)$，其中：

- $T$ 是函子
- $\eta : 1_C \rightarrow T$ 是单位自然变换
- $\mu : T^2 \rightarrow T$ 是乘法自然变换

满足以下定律：

1. **左单位律**: $\mu \circ \eta T = 1_T$
2. **右单位律**: $\mu \circ T\eta = 1_T$
3. **结合律**: $\mu \circ \mu T = \mu \circ T\mu$

### 单子变换器

```haskell
-- 单子变换器基础
class MonadTrans t where
    lift :: Monad m => m a -> t m a

-- ReaderT单子变换器
newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

instance MonadTrans (ReaderT r) where
    lift m = ReaderT $ \_ -> m

instance Monad m => Monad (ReaderT r m) where
    return a = ReaderT $ \_ -> return a
    m >>= k = ReaderT $ \r -> do
        a <- runReaderT m r
        runReaderT (k a) r
```

### 应用示例

```haskell
-- 错误处理单子
data Result a = Success a | Error String deriving Show

instance Monad Result where
    return = Success
    Success x >>= k = k x
    Error msg >>= _ = Error msg

-- 使用单子进行链式计算
safeDivide :: Double -> Double -> Result Double
safeDivide _ 0 = Error "Division by zero"
safeDivide x y = Success (x / y)

safeSqrt :: Double -> Result Double
safeSqrt x | x < 0 = Error "Negative number"
           | otherwise = Success (sqrt x)

-- 链式计算
calculation :: Double -> Double -> Result Double
calculation x y = do
    quotient <- safeDivide x y
    result <- safeSqrt quotient
    return result
```

## 高级类型类

### 遍历 (Traversable)

```haskell
class (Functor t, Foldable t) => Traversable t where
    traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
    sequenceA :: Applicative f => t (f a) -> f (t a)
    
    traverse f = sequenceA . fmap f
    sequenceA = traverse id

-- 列表Traversable实例
instance Traversable [] where
    traverse f [] = pure []
    traverse f (x:xs) = (:) <$> f x <*> traverse f xs
```

### 可折叠 (Foldable)

```haskell
class Foldable t where
    foldMap :: Monoid m => (a -> m) -> t a -> m
    foldr :: (a -> b -> b) -> b -> t a -> b
    
    foldMap f = foldr (mappend . f) mempty

-- 列表Foldable实例
instance Foldable [] where
    foldr _ z [] = z
    foldr f z (x:xs) = f x (foldr f z xs)
```

## 实际应用

### 解析器组合子

```haskell
-- 基本解析器类型
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

instance Functor Parser where
    fmap f (Parser p) = Parser $ \input -> do
        (result, rest) <- p input
        return (f result, rest)

instance Applicative Parser where
    pure a = Parser $ \input -> Just (a, input)
    Parser f <*> Parser p = Parser $ \input -> do
        (g, rest1) <- f input
        (a, rest2) <- p rest1
        return (g a, rest2)

instance Monad Parser where
    return = pure
    Parser p >>= k = Parser $ \input -> do
        (a, rest) <- p input
        runParser (k a) rest

-- 基本解析器
char :: Char -> Parser Char
char c = Parser $ \input -> case input of
    (x:xs) | x == c -> Just (c, xs)
    _ -> Nothing

-- 组合解析器
parseTwoChars :: Parser (Char, Char)
parseTwoChars = do
    c1 <- char 'a'
    c2 <- char 'b'
    return (c1, c2)
```

### 状态单子

```haskell
-- 状态单子
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
    fmap f (State g) = State $ \s -> let (a, s') = g s in (f a, s')

instance Applicative (State s) where
    pure a = State $ \s -> (a, s)
    State f <*> State g = State $ \s -> let
        (h, s') = f s
        (a, s'') = g s'
        in (h a, s'')

instance Monad (State s) where
    return = pure
    State f >>= k = State $ \s -> let
        (a, s') = f s
        in runState (k a) s'

-- 状态操作
get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((), f s)
```

## 形式化验证

### 单子定律验证

```haskell
-- 验证Maybe单子的左单位律
leftIdentity :: a -> (a -> Maybe b) -> Bool
leftIdentity a k = (return a >>= k) == k a

-- 验证Maybe单子的右单位律
rightIdentity :: Maybe a -> Bool
rightIdentity m = (m >>= return) == m

-- 验证Maybe单子的结合律
associativity :: Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Bool
associativity m k h = ((m >>= k) >>= h) == (m >>= (\x -> k x >>= h))
```

## 总结

类型类、函子、应用函子和单子是Haskell函数式编程的核心概念，它们提供了强大的抽象能力，使得代码更加模块化、可复用和类型安全。通过理解这些概念的形式化定义和实际应用，我们可以构建更加健壮和优雅的程序。

---

**相关链接**:
- [函数式编程基础](../01-Basic-Examples/01-Functional-Programming-Basics.md)
- [算法实现](../03-Algorithm-Implementation/README.md)
- [形式化证明](../04-Formal-Proofs/README.md)
