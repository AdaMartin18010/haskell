# Haskell函数式设计模式 (Haskell Functional Design Patterns)

## 📚 快速导航

### 相关理论

- [函数式编程理论](../../02-Formal-Science/09-Functional-Programming/001-Lambda-Calculus.md)
- [类型系统基础](../02-Type-System/001-Type-System-Foundation.md)
- [控制流基础](../03-Control-Flow/001-Control-Flow-Foundation.md)

### 实现示例

- [Monad模式](../002-Monad-Patterns.md)
- [Applicative模式](../003-Applicative-Patterns.md)
- [Functor模式](../004-Functor-Patterns.md)

### 应用领域

- [软件架构](../../../haskell/10-Software-Architecture/001-Architecture-Foundation.md)
- [数据处理](../../../haskell/09-Data-Processing/001-Data-Processing-Foundation.md)

---

## 🎯 概述

函数式设计模式是Haskell中解决常见编程问题的标准化解决方案。本文档详细介绍了Haskell中的核心设计模式，包括Functor、Applicative、Monad等类型类模式，以及函数式编程中的常见模式。

## 1. 类型类设计模式

### 1.1 Functor模式

**定义 1.1 (Functor)**
Functor是支持映射操作的容器类型。

**数学定义：**
Functor是一个类型构造函数 $F$ 和函数 $fmap$，满足：
$$fmap: (A \rightarrow B) \rightarrow F(A) \rightarrow F(B)$$

**定理 1.1 (Functor定律)**
Functor必须满足以下定律：

1. **恒等律**：$fmap\ id = id$
2. **结合律**：$fmap\ (f \circ g) = fmap\ f \circ fmap\ g$

**Haskell实现：**

```haskell
-- Functor类型类
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- Maybe Functor实例
instance Functor Maybe where
  fmap f Nothing = Nothing
  fmap f (Just x) = Just (f x)

-- 列表Functor实例
instance Functor [] where
  fmap = map

-- Either Functor实例
instance Functor (Either a) where
  fmap f (Left x) = Left x
  fmap f (Right y) = Right (f y)

-- 元组Functor实例
instance Functor ((,) a) where
  fmap f (x, y) = (x, f y)

-- Functor模式应用
functorPattern :: [Int] -> [String]
functorPattern = fmap show

-- Functor组合
functorComposition :: [Int] -> [String]
functorComposition = fmap (show . (* 2))

-- Functor与错误处理
safeFunctor :: Maybe Int -> Maybe String
safeFunctor = fmap (\x -> "Value: " ++ show x)

-- Functor与条件处理
conditionalFunctor :: [Int] -> [String]
conditionalFunctor = fmap (\x -> 
  if x > 0 then "Positive: " ++ show x else "Non-positive: " ++ show x)

-- 自定义Functor
data Tree a = Leaf a | Node (Tree a) (Tree a)

instance Functor Tree where
  fmap f (Leaf x) = Leaf (f x)
  fmap f (Node left right) = Node (fmap f left) (fmap f right)

-- Functor模式示例
treeFunctorPattern :: Tree Int -> Tree String
treeFunctorPattern = fmap show
```

### 1.2 Applicative模式

**定义 1.2 (Applicative)**
Applicative是支持函数应用的Functor。

**数学定义：**
Applicative是一个类型构造函数 $F$ 和函数：

- $pure: A \rightarrow F(A)$
- $<*>: F(A \rightarrow B) \rightarrow F(A) \rightarrow F(B)$

**定理 1.2 (Applicative定律)**
Applicative必须满足以下定律：

1. **恒等律**：$pure\ id <*> v = v$
2. **同态律**：$pure\ f <*> pure\ x = pure\ (f\ x)$
3. **交换律**：$u <*> pure\ y = pure\ (\lambda f \rightarrow f\ y) <*> u$
4. **结合律**：$u <*> (v <*> w) = pure\ (.) <*> u <*> v <*> w$

**Haskell实现：**

```haskell
-- Applicative类型类
class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

-- Maybe Applicative实例
instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  Just f <*> x = fmap f x

-- 列表Applicative实例
instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]

-- Either Applicative实例
instance Applicative (Either e) where
  pure = Right
  Left e <*> _ = Left e
  Right f <*> x = fmap f x

-- Applicative模式应用
applicativePattern :: Maybe Int -> Maybe Int -> Maybe Int
applicativePattern x y = (+) <$> x <*> y

-- Applicative与函数应用
functionApplication :: Maybe (Int -> Int -> Int) -> Maybe Int -> Maybe Int -> Maybe Int
functionApplication f x y = f <*> x <*> y

-- Applicative与列表处理
listApplicativePattern :: [Int] -> [Int] -> [Int]
listApplicativePattern xs ys = (+) <$> xs <*> ys

-- Applicative与错误处理
safeApplicative :: Either String Int -> Either String Int -> Either String Int
safeApplicative x y = (+) <$> x <*> y

-- Applicative与条件处理
conditionalApplicative :: [Int] -> [Int] -> [Int]
conditionalApplicative xs ys = 
  filter (> 0) <$> xs <*> ys

-- 自定义Applicative
data Validation e a = Success a | Failure e

instance Functor (Validation e) where
  fmap f (Success x) = Success (f x)
  fmap _ (Failure e) = Failure e

instance Applicative (Validation e) where
  pure = Success
  Success f <*> Success x = Success (f x)
  Failure e <*> _ = Failure e
  _ <*> Failure e = Failure e

-- Applicative模式示例
validationPattern :: Validation String Int -> Validation String Int -> Validation String Int
validationPattern x y = (+) <$> x <*> y
```

### 1.3 Monad模式

**定义 1.3 (Monad)**
Monad是支持顺序计算的Applicative。

**数学定义：**
Monad是一个类型构造函数 $M$ 和函数：

- $return: A \rightarrow M(A)$
- $>>=: M(A) \rightarrow (A \rightarrow M(B)) \rightarrow M(B)$

**定理 1.3 (Monad定律)**
Monad必须满足以下定律：

1. **左单位律**：$return\ a >>= f = f\ a$
2. **右单位律**：$m >>= return = m$
3. **结合律**：$(m >>= f) >>= g = m >>= (\lambda x \rightarrow f\ x >>= g)$

**Haskell实现：**

```haskell
-- Monad类型类
class Applicative m => Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- Maybe Monad实例
instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just x >>= f = f x

-- 列表Monad实例
instance Monad [] where
  return x = [x]
  xs >>= f = concat (map f xs)

-- Either Monad实例
instance Monad (Either e) where
  return = Right
  Left e >>= _ = Left e
  Right x >>= f = f x

-- Monad模式应用
monadPattern :: Maybe Int -> Maybe String
monadPattern mx = mx >>= \x -> 
  if x > 0 then Just ("Positive: " ++ show x) else Nothing

-- Monad与错误处理
safeMonad :: Either String Int -> Either String String
safeMonad mx = mx >>= \x -> 
  if x > 0 then Right ("Value: " ++ show x) else Left "Non-positive value"

-- Monad与列表处理
listMonadPattern :: [Int] -> [String]
listMonadPattern xs = xs >>= \x -> 
  if x > 0 then [show x] else []

-- Monad与状态处理
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap f (State g) = State $ \s -> 
    let (a, s') = g s in (f a, s')

instance Applicative (State s) where
  pure a = State $ \s -> (a, s)
  State f <*> State g = State $ \s ->
    let (h, s') = f s
        (a, s'') = g s'
    in (h a, s'')

instance Monad (State s) where
  State f >>= g = State $ \s ->
    let (a, s') = f s
        State h = g a
    in h s'

-- Monad模式示例
stateMonadPattern :: State Int Int
stateMonadPattern = do
  x <- get
  put (x + 1)
  return (x * 2)

-- Monad与IO
ioMonadPattern :: IO String
ioMonadPattern = do
  putStrLn "Enter a number:"
  input <- getLine
  let number = read input :: Int
  return ("You entered: " ++ show number)
```

## 2. 函数式编程模式

### 2.1 高阶函数模式

**定义 2.1 (高阶函数模式)**
高阶函数模式是使用函数作为参数或返回值的模式。

**数学定义：**
高阶函数可以表示为：
$$f: (A \rightarrow B) \rightarrow C$$
或
$$f: A \rightarrow (B \rightarrow C)$$

**Haskell实现：**

```haskell
-- 高阶函数模式
-- Map模式
mapPattern :: (a -> b) -> [a] -> [b]
mapPattern f = map f

-- Filter模式
filterPattern :: (a -> Bool) -> [a] -> [a]
filterPattern p = filter p

-- Fold模式
foldPattern :: (a -> b -> b) -> b -> [a] -> b
foldPattern f z = foldr f z

-- 函数组合模式
composePattern :: (b -> c) -> (a -> b) -> a -> c
composePattern f g = f . g

-- 部分应用模式
partialApplicationPattern :: (a -> b -> c) -> a -> b -> c
partialApplicationPattern f x = f x

-- 柯里化模式
curryPattern :: ((a, b) -> c) -> a -> b -> c
curryPattern f a b = f (a, b)

-- 高阶函数组合
higherOrderPattern :: [Int] -> [String]
higherOrderPattern = 
  map show 
  . filter (> 0) 
  . map (* 2)

-- 高阶函数与错误处理
safeHigherOrderPattern :: [String] -> [Int]
safeHigherOrderPattern = 
  concatMap (\s -> case reads s of
    [(n, "")] -> [n]
    _ -> [])
  . filter (not . null)

-- 高阶函数与条件处理
conditionalHigherOrderPattern :: [Int] -> [String]
conditionalHigherOrderPattern = 
  map (\x -> if x > 0 then "Positive" else "Non-positive")
  . filter (/= 0)
```

### 2.2 不可变数据结构模式

**定义 2.2 (不可变数据结构模式)**
不可变数据结构模式是使用不可变数据结构的模式。

**定理 2.1 (不可变性优势)**
不可变数据结构具有以下优势：

1. **线程安全**：天然支持并发
2. **简化推理**：值不会意外改变
3. **优化机会**：编译器可以进行更多优化
4. **调试简化**：问题更容易追踪

**Haskell实现：**

```haskell
-- 不可变数据结构模式
-- 不可变列表
immutableListPattern :: [Int] -> [Int]
immutableListPattern xs = 
  let filtered = filter (> 0) xs
      doubled = map (* 2) filtered
      sorted = sort doubled
  in sorted

-- 不可变树
data Tree a = Leaf a | Node (Tree a) (Tree a)

immutableTreePattern :: Tree Int -> Tree String
immutableTreePattern (Leaf x) = Leaf (show x)
immutableTreePattern (Node left right) = 
  Node (immutableTreePattern left) (immutableTreePattern right)

-- 不可变映射
immutableMapPattern :: [(String, Int)] -> [(String, Int)]
immutableMapPattern pairs = 
  let filtered = filter (\(_, v) -> v > 0) pairs
      doubled = map (\(k, v) -> (k, v * 2)) filtered
      sorted = sortBy (comparing snd) doubled
  in sorted

-- 不可变栈
data Stack a = Empty | Push a (Stack a)

immutableStackPattern :: Stack Int -> Stack String
immutableStackPattern Empty = Empty
immutableStackPattern (Push x s) = Push (show x) (immutableStackPattern s)

-- 不可变队列
data Queue a = Queue [a] [a]

immutableQueuePattern :: Queue Int -> Queue String
immutableQueuePattern (Queue front back) = 
  Queue (map show front) (map show back)

-- 不可变集合
immutableSetPattern :: [Int] -> [Int]
immutableSetPattern = 
  nub 
  . sort 
  . filter (> 0)

-- 不可变记录
data Person = Person {
  name :: String,
  age :: Int,
  email :: String
}

immutableRecordPattern :: Person -> Person
immutableRecordPattern person = 
  person { age = age person + 1 }
```

### 2.3 惰性求值模式

**定义 2.3 (惰性求值模式)**
惰性求值模式是使用惰性求值的模式。

**数学定义：**
惰性求值可以表示为：
$$eval_{lazy}(expr) = \begin{cases}
eval(expr) & \text{if } needed(expr) \\
\bot & \text{otherwise}
\end{cases}$$

**Haskell实现：**

```haskell
-- 惰性求值模式
-- 无限列表模式
infiniteListPattern :: [Integer]
infiniteListPattern = [1..]

-- 惰性计算模式
lazyComputationPattern :: [Integer] -> [Integer]
lazyComputationPattern =
  take 10
  . map (* 2)
  . filter even

-- 惰性斐波那契模式
lazyFibonacciPattern :: [Integer]
lazyFibonacciPattern = 0 : 1 : zipWith (+) lazyFibonacciPattern (tail lazyFibonacciPattern)

-- 惰性素数模式
lazyPrimePattern :: [Integer]
lazyPrimePattern = 2 : [n | n <- [3..], all (\p -> n `mod` p /= 0) (takeWhile (\p -> p * p <= n) lazyPrimePattern)]

-- 惰性流处理模式
lazyStreamPattern :: [Integer] -> [Integer]
lazyStreamPattern =
  map (* 2)
  . filter (> 0)
  . take 100

-- 惰性记忆化模式
lazyMemoizationPattern :: Integer -> Integer
lazyMemoizationPattern = (map factorial [0..] !!)
  where
    factorial 0 = 1
    factorial n = n * factorial (n - 1)

-- 惰性条件模式
lazyConditionalPattern :: [Integer] -> [Integer]
lazyConditionalPattern xs =
  let positive = filter (> 0) xs
      negative = filter (< 0) xs
  in if length positive > length negative
     then take 10 positive
     else take 10 (map abs negative)

-- 惰性错误处理模式
lazyErrorHandlingPattern :: [String] -> [Int]
lazyErrorHandlingPattern =
  take 100
  . concatMap (\s -> case reads s of
      [(n, "")] -> [n]
      _ -> [])
  . filter (not . null)
```

## 3. 错误处理模式

### 3.1 Maybe模式

**定义 3.1 (Maybe模式)**
Maybe模式是处理可能失败的计算的模式。

**数学定义：**
Maybe类型可以表示为：
$$Maybe(A) = \{Nothing\} \cup \{Just(a) \mid a \in A\}$$

**Haskell实现：**

```haskell
-- Maybe模式
-- 基本Maybe模式
maybePattern :: Maybe Int -> Maybe String
maybePattern Nothing = Nothing
maybePattern (Just x) = Just (show x)

-- Maybe与模式匹配
maybePatternMatching :: Maybe Int -> String
maybePatternMatching Nothing = "No value"
maybePatternMatching (Just x) = "Value: " ++ show x

-- Maybe与函数组合
maybeCompositionPattern :: Maybe Int -> Maybe Int -> Maybe Int
maybeCompositionPattern mx my = do
  x <- mx
  y <- my
  return (x + y)

-- Maybe与错误处理
maybeErrorHandlingPattern :: String -> Maybe Int
maybeErrorHandlingPattern s =
  case reads s of
    [(n, "")] -> Just n
    _ -> Nothing

-- Maybe与条件处理
maybeConditionalPattern :: Int -> Maybe String
maybeConditionalPattern x
  | x > 0 = Just ("Positive: " ++ show x)
  | x == 0 = Just "Zero"
  | otherwise = Nothing

-- Maybe与列表处理
maybeListPattern :: [Maybe Int] -> [Int]
maybeListPattern =
  concatMap (\m -> case m of
    Just x -> [x]
    Nothing -> [])

-- Maybe与默认值
maybeDefaultPattern :: Maybe Int -> Int
maybeDefaultPattern Nothing = 0
maybeDefaultPattern (Just x) = x

-- Maybe与转换
maybeTransformPattern :: Maybe Int -> Maybe String
maybeTransformPattern = fmap show
```

### 3.2 Either模式

**定义 3.2 (Either模式)**
Either模式是处理可能失败的计算并提供错误信息的模式。

**数学定义：**
Either类型可以表示为：
$$Either(E, A) = \{Left(e) \mid e \in E\} \cup \{Right(a) \mid a \in A\}$$

**Haskell实现：**

```haskell
-- Either模式
-- 基本Either模式
eitherPattern :: Either String Int -> Either String String
eitherPattern (Left e) = Left e
eitherPattern (Right x) = Right (show x)

-- Either与模式匹配
eitherPatternMatching :: Either String Int -> String
eitherPatternMatching (Left e) = "Error: " ++ e
eitherPatternMatching (Right x) = "Success: " ++ show x

-- Either与函数组合
eitherCompositionPattern :: Either String Int -> Either String Int -> Either String Int
eitherCompositionPattern ex ey = do
  x <- ex
  y <- ey
  return (x + y)

-- Either与错误处理
eitherErrorHandlingPattern :: String -> Either String Int
eitherErrorHandlingPattern s =
  case reads s of
    [(n, "")] -> Right n
    _ -> Left ("Invalid number: " ++ s)

-- Either与条件处理
eitherConditionalPattern :: Int -> Either String String
eitherConditionalPattern x
  | x > 0 = Right ("Positive: " ++ show x)
  | x == 0 = Right "Zero"
  | otherwise = Left ("Negative number: " ++ show x)

-- Either与列表处理
eitherListPattern :: [Either String Int] -> Either String [Int]
eitherListPattern =
  foldr (\e acc -> do
    x <- e
    xs <- acc
    return (x:xs)) (Right [])

-- Either与转换
eitherTransformPattern :: Either String Int -> Either String String
eitherTransformPattern = fmap show

-- Either与错误聚合
eitherErrorAggregationPattern :: [Either String Int] -> (String, [Int])
eitherErrorAggregationPattern =
  foldr (\e (errors, values) ->
    case e of
      Left err -> (err : errors, values)
      Right val -> (errors, val : values)) ([], [])
```

### 3.3 异常处理模式

**定义 3.3 (异常处理模式)**
异常处理模式是使用异常处理机制的模式。

**Haskell实现：**

```haskell
-- 异常处理模式
-- 基本异常处理
exceptionPattern :: IO String
exceptionPattern = do
  result <- try (readFile "nonexistent.txt")
  case result of
    Left e -> return ("Error: " ++ show (e :: IOError))
    Right content -> return ("Content: " ++ content)

-- 异常处理与Maybe
exceptionMaybePattern :: IO (Maybe String)
exceptionMaybePattern = do
  result <- try (readFile "file.txt")
  case result of
    Left _ -> return Nothing
    Right content -> return (Just content)

-- 异常处理与Either
exceptionEitherPattern :: IO (Either String String)
exceptionEitherPattern = do
  result <- try (readFile "file.txt")
  case result of
    Left e -> return (Left ("IO Error: " ++ show (e :: IOError)))
    Right content -> return (Right content)

-- 异常处理与恢复
exceptionRecoveryPattern :: IO String
exceptionRecoveryPattern = do
  result <- try (readFile "primary.txt")
  case result of
    Left _ -> do
      backupResult <- try (readFile "backup.txt")
      case backupResult of
        Left _ -> return "No file available"
        Right content -> return content
    Right content -> return content

-- 异常处理与清理
exceptionCleanupPattern :: IO String
exceptionCleanupPattern = do
  handle <- openFile "file.txt" ReadMode
  result <- try (hGetContents handle)
  hClose handle
  case result of
    Left e -> return ("Error: " ++ show (e :: IOError))
    Right content -> return content

-- 异常处理与重试
exceptionRetryPattern :: Int -> IO String
exceptionRetryPattern 0 = return "Max retries exceeded"
exceptionRetryPattern n = do
  result <- try (readFile "file.txt")
  case result of
    Left _ -> exceptionRetryPattern (n - 1)
    Right content -> return content
```

## 4. 总结

Haskell函数式设计模式提供了强大而灵活的问题解决方案，基于数学理论和类型安全。

### 关键模式

1. **类型类模式**：Functor、Applicative、Monad
2. **函数式模式**：高阶函数、不可变数据结构、惰性求值
3. **错误处理模式**：Maybe、Either、异常处理

### 优势

1. **类型安全**：编译时保证正确性
2. **可组合性**：模式可以安全组合
3. **可重用性**：提高代码重用性
4. **表达力**：强大的抽象能力

### 应用领域

1. **数据处理**：ETL和数据转换
2. **错误处理**：安全的错误管理
3. **并发编程**：线程安全的数据处理
4. **系统编程**：类型安全的系统开发

---

**相关文档**：
- [Monad模式](../002-Monad-Patterns.md)
- [Applicative模式](../003-Applicative-Patterns.md)
- [Functor模式](../004-Functor-Patterns.md)
