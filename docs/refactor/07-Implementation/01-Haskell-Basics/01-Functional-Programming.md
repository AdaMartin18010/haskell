# 函数式编程基础 (Functional Programming Fundamentals)

## 概述

函数式编程是一种编程范式，强调使用纯函数、不可变数据和函数组合来构建程序。Haskell是函数式编程的典型代表语言。

## 1. 纯函数

### 1.1 纯函数定义

**定义 1.1 (纯函数)**
纯函数是满足以下条件的函数：
- 相同输入总是产生相同输出
- 没有副作用
- 不依赖外部状态

```haskell
-- 纯函数示例
add :: Int -> Int -> Int
add x y = x + y

multiply :: Int -> Int -> Int
multiply x y = x * y

-- 非纯函数示例（有副作用）
impureAdd :: Int -> Int -> IO Int
impureAdd x y = do
  putStrLn "Adding numbers..."
  return (x + y)
```

### 1.2 函数纯度检查

```haskell
-- 函数纯度类型类
class Pure f where
  isPure :: f -> Bool

-- 纯函数实例
instance Pure (Int -> Int -> Int) where
  isPure _ = True

-- 非纯函数实例
instance Pure (Int -> Int -> IO Int) where
  isPure _ = False

-- 函数纯度测试
testPurity :: IO ()
testPurity = do
  putStrLn "Testing function purity..."
  putStrLn $ "add is pure: " ++ show (isPure add)
  putStrLn $ "impureAdd is pure: " ++ show (isPure impureAdd)
```

## 2. 高阶函数

### 2.1 函数作为参数

```haskell
-- 高阶函数：接受函数作为参数
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- 函数组合
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- 部分应用
partialApply :: (a -> b -> c) -> a -> b -> c
partialApply f x y = f x y

-- 柯里化
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

-- 反柯里化
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (x, y) = f x y
```

### 2.2 常用高阶函数

```haskell
-- map函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- filter函数
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs

-- foldr函数
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

-- foldl函数
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ z [] = z
foldl f z (x:xs) = foldl f (f z x) xs

-- 函数应用
($) :: (a -> b) -> a -> b
f $ x = f x

-- 函数组合
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)
```

## 3. 类型系统

### 3.1 基本类型

```haskell
-- 基本数据类型
data Bool = True | False
data Int = -- 整数类型
data Double = -- 浮点数类型
data Char = -- 字符类型
data String = [Char]

-- 列表类型
data List a = Nil | Cons a (List a)

-- Maybe类型
data Maybe a = Nothing | Just a

-- Either类型
data Either a b = Left a | Right b

-- 元组类型
data Tuple a b = Tuple a b
```

### 3.2 类型类

```haskell
-- Eq类型类
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x /= y = not (x == y)

-- Ord类型类
class (Eq a) => Ord a where
  compare :: a -> a -> Ordering
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  max :: a -> a -> a
  min :: a -> a -> a

-- Num类型类
class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a
  fromInteger :: Integer -> a

-- Show类型类
class Show a where
  show :: a -> String
  showsPrec :: Int -> a -> ShowS
  showList :: [a] -> ShowS
```

### 3.3 自定义类型类

```haskell
-- 可比较类型类
class Comparable a where
  compareTo :: a -> a -> Ordering
  isLess :: a -> a -> Bool
  isGreater :: a -> a -> Bool
  isEqual :: a -> a -> Bool

-- 可序列化类型类
class Serializable a where
  serialize :: a -> String
  deserialize :: String -> Maybe a

-- 可验证类型类
class Validatable a where
  validate :: a -> Bool
  getErrors :: a -> [String]
```

## 4. 模式匹配

### 4.1 基本模式匹配

```haskell
-- 列表模式匹配
listLength :: [a] -> Int
listLength [] = 0
listLength (_:xs) = 1 + listLength xs

-- 元组模式匹配
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- Maybe模式匹配
maybeValue :: Maybe a -> a
maybeValue (Just x) = x
maybeValue Nothing = error "No value"

-- Either模式匹配
eitherValue :: Either a b -> b
eitherValue (Right x) = x
eitherValue (Left _) = error "Left value"
```

### 4.2 高级模式匹配

```haskell
-- 守卫表达式
absolute :: Int -> Int
absolute x
  | x < 0 = -x
  | otherwise = x

-- 模式匹配与守卫结合
classifyNumber :: Int -> String
classifyNumber x
  | x < 0 = "Negative"
  | x == 0 = "Zero"
  | x > 0 = "Positive"

-- 模式匹配中的绑定
firstTwo :: [a] -> Maybe (a, a)
firstTwo (x:y:_) = Just (x, y)
firstTwo _ = Nothing

-- 模式匹配中的通配符
ignoreFirst :: [a] -> [a]
ignoreFirst (_:xs) = xs
ignoreFirst [] = []
```

## 5. 递归

### 5.1 基本递归

```haskell
-- 阶乘函数
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 斐波那契数列
fibonacci :: Integer -> Integer
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci (n - 1) + fibonacci (n - 2)

-- 列表反转
reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

-- 列表连接
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys
```

### 5.2 尾递归

```haskell
-- 尾递归阶乘
factorialTail :: Integer -> Integer
factorialTail n = factorialHelper n 1
  where
    factorialHelper 0 acc = acc
    factorialHelper n acc = factorialHelper (n - 1) (n * acc)

-- 尾递归斐波那契
fibonacciTail :: Integer -> Integer
fibonacciTail n = fibonacciHelper n 0 1
  where
    fibonacciHelper 0 a _ = a
    fibonacciHelper 1 _ b = b
    fibonacciHelper n a b = fibonacciHelper (n - 1) b (a + b)

-- 尾递归列表反转
reverseTail :: [a] -> [a]
reverseTail xs = reverseHelper xs []
  where
    reverseHelper [] acc = acc
    reverseHelper (x:xs) acc = reverseHelper xs (x:acc)
```

## 6. 惰性求值

### 6.1 惰性列表

```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 无限斐波那契数列
fibonacciList :: [Integer]
fibonacciList = 0 : 1 : zipWith (+) fibonacciList (tail fibonacciList)

-- 素数筛选
primes :: [Integer]
primes = sieve [2..]
  where
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

-- 惰性求值示例
takeFirst :: Int -> [a] -> [a]
takeFirst 0 _ = []
takeFirst _ [] = []
takeFirst n (x:xs) = x : takeFirst (n - 1) xs
```

### 6.2 惰性求值优化

```haskell
-- 记忆化
memoize :: (Integer -> a) -> Integer -> a
memoize f = (map f [0..] !!)

-- 记忆化斐波那契
fibonacciMemo :: Integer -> Integer
fibonacciMemo = memoize fib
  where
    fib 0 = 0
    fib 1 = 1
    fib n = fibonacciMemo (n - 1) + fibonacciMemo (n - 2)

-- 惰性求值测试
lazyEvaluationTest :: IO ()
lazyEvaluationTest = do
  putStrLn "Testing lazy evaluation..."
  let infinite = [1..]
  putStrLn $ "First 5 elements: " ++ show (take 5 infinite)
  putStrLn $ "Fibonacci first 10: " ++ show (take 10 fibonacciList)
  putStrLn $ "Primes first 10: " ++ show (take 10 primes)
```

## 7. 函数组合

### 7.1 函数组合操作

```haskell
-- 基本函数组合
composeBasic :: (b -> c) -> (a -> b) -> a -> c
composeBasic f g x = f (g x)

-- 多函数组合
composeMany :: [a -> a] -> a -> a
composeMany [] x = x
composeMany (f:fs) x = composeMany fs (f x)

-- 管道操作
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 反向管道
(<|) :: (a -> b) -> a -> b
f <| x = f x

-- 函数组合示例
exampleComposition :: [Int] -> Int
exampleComposition = 
  filter (> 0) .>
  map (* 2) .>
  sum

-- 管道操作符
(.>) :: (a -> b) -> (b -> c) -> a -> c
f .> g = g . f
```

### 7.2 高级函数组合

```haskell
-- 函数应用
apply :: (a -> b) -> a -> b
apply f x = f x

-- 函数提升
liftA2 :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
liftA2 f (Just x) (Just y) = Just (f x y)
liftA2 _ _ _ = Nothing

-- 函数映射
fmap :: Functor f => (a -> b) -> f a -> f b
fmap f (Just x) = Just (f x)
fmap _ Nothing = Nothing

-- 函数绑定
bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind (Just x) f = f x
bind Nothing _ = Nothing

-- 函数组合测试
compositionTest :: IO ()
compositionTest = do
  putStrLn "Testing function composition..."
  let numbers = [-2, -1, 0, 1, 2, 3]
  let result = exampleComposition numbers
  putStrLn $ "Input: " ++ show numbers
  putStrLn $ "Result: " ++ show result
```

## 8. 结论

函数式编程基础为Haskell编程提供了坚实的理论基础：

1. **纯函数**：确保程序的可预测性和可测试性
2. **高阶函数**：提供强大的抽象能力
3. **类型系统**：在编译时捕获错误
4. **模式匹配**：优雅地处理数据结构
5. **递归**：自然地表达算法
6. **惰性求值**：优化内存使用和计算效率
7. **函数组合**：构建复杂的程序逻辑

这些概念构成了函数式编程的核心，为构建可靠、高效和优雅的程序提供了强大的工具。

## 参考文献

1. Bird, R. (1998). Introduction to functional programming using Haskell. Prentice Hall.
2. Hutton, G. (2016). Programming in Haskell. Cambridge University Press.
3. Thompson, S. (2011). Haskell: the craft of functional programming. Pearson Education.
4. Peyton Jones, S. (2003). The Haskell 98 language and libraries: the revised report. Journal of functional programming, 13(1), 0-255. 