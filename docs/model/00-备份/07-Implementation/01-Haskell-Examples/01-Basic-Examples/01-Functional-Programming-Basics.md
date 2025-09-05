# 函数式编程基础 (Functional Programming Basics)

## 概述

函数式编程是一种编程范式，强调使用纯函数和不可变数据。Haskell作为纯函数式编程语言的代表，完美体现了函数式编程的核心概念。

## 1. 纯函数 (Pure Functions)

### 数学定义

纯函数满足以下性质：

- **确定性**：相同输入总是产生相同输出
- **无副作用**：不修改外部状态
- **引用透明性**：函数调用可以被其返回值替换

$$\forall x, y \in \text{Domain}(f): x = y \implies f(x) = f(y)$$

### Haskell实现

```haskell
-- 纯函数示例
add :: Num a => a -> a -> a
add x y = x + y

-- 非纯函数示例（在IO中）
getCurrentTime :: IO UTCTime
getCurrentTime = getCurrentTime

-- 引用透明性验证
-- add 2 3 总是等于 5，可以安全替换
```

## 2. 高阶函数 (Higher-Order Functions)

### 数学定义

高阶函数是接受函数作为参数或返回函数的函数：

$$H: (A \to B) \to (C \to D)$$

### Haskell实现

```haskell
-- 高阶函数：接受函数作为参数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- 高阶函数：返回函数
const :: a -> b -> a
const x _ = x

-- 函数组合
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 实际应用
doubleList :: [Int] -> [Int]
doubleList = map (*2)

-- 使用函数组合
processData :: [Int] -> [Int]
processData = map (*2) . filter (>0) . map (+1)
```

## 3. 不可变数据 (Immutable Data)

### 概念定义

不可变数据一旦创建就不能修改，所有操作都返回新的数据结构。

### Haskell实现

```haskell
-- 不可变列表操作
data List a = Nil | Cons a (List a)

-- 添加元素（返回新列表）
append :: List a -> a -> List a
append Nil x = Cons x Nil
append (Cons y ys) x = Cons y (append ys x)

-- 删除元素（返回新列表）
delete :: Eq a => a -> List a -> List a
delete _ Nil = Nil
delete x (Cons y ys)
  | x == y = ys
  | otherwise = Cons y (delete x ys)

-- 标准库中的不可变操作
exampleList :: [Int]
exampleList = [1, 2, 3, 4, 5]

-- 这些操作都返回新列表，原列表不变
newList1 = 0 : exampleList  -- [0,1,2,3,4,5]
newList2 = tail exampleList -- [2,3,4,5]
newList3 = init exampleList -- [1,2,3,4]
```

## 4. 模式匹配 (Pattern Matching)

### 概念定义

模式匹配是函数式编程中解构数据结构的核心机制。

### Haskell实现

```haskell
-- 基本模式匹配
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

-- 复杂模式匹配
data Tree a = Leaf a | Node (Tree a) (Tree a)

treeDepth :: Tree a -> Int
treeDepth (Leaf _) = 0
treeDepth (Node left right) = 1 + max (treeDepth left) (treeDepth right)

-- 模式匹配与守卫
classify :: Int -> String
classify n
  | n < 0 = "Negative"
  | n == 0 = "Zero"
  | n <= 10 = "Small"
  | n <= 100 = "Medium"
  | otherwise = "Large"

-- 记录模式匹配
data Person = Person { name :: String, age :: Int }

greet :: Person -> String
greet (Person { name = n, age = a })
  | a < 18 = "Hello young " ++ n
  | a < 65 = "Hello " ++ n
  | otherwise = "Hello senior " ++ n
```

## 5. 递归 (Recursion)

### 数学定义

递归是函数调用自身的机制，是函数式编程中实现循环的主要方式。

### Haskell实现

```haskell
-- 基本递归
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 尾递归优化
factorialTail :: Integer -> Integer
factorialTail n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)

-- 列表递归
reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

-- 尾递归版本的reverse
reverseTail :: [a] -> [a]
reverseTail xs = go xs []
  where
    go [] acc = acc
    go (x:xs) acc = go xs (x:acc)

-- 树递归
data BinaryTree a = Empty | Node a (BinaryTree a) (BinaryTree a)

treeSize :: BinaryTree a -> Int
treeSize Empty = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

-- 深度优先遍历
inorder :: BinaryTree a -> [a]
inorder Empty = []
inorder (Node x left right) = inorder left ++ [x] ++ inorder right
```

## 6. 惰性求值 (Lazy Evaluation)

### 概念定义

惰性求值是指表达式只在需要时才被计算，这是Haskell的重要特性。

### Haskell实现

```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 只取前10个元素
firstTen :: [Integer]
firstTen = take 10 infiniteList

-- 惰性求值示例
expensive :: Int -> Int
expensive n = trace ("Computing " ++ show n) (n * n)

-- 只有在需要时才计算
lazyExample :: Int
lazyExample = head (map expensive [1..1000])

-- 无限流处理
fibonacci :: [Integer]
fibonacci = 0 : 1 : zipWith (+) fibonacci (tail fibonacci)

-- 只计算需要的斐波那契数
fibN :: Int -> Integer
fibN n = fibonacci !! n
```

## 7. 类型系统 (Type System)

### 概念定义

Haskell的类型系统提供了编译时安全保障，确保程序的正确性。

### Haskell实现

```haskell
-- 基本类型
data Bool = True | False
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b

-- 类型类
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x /= y = not (x == y)

-- 实例定义
instance Eq Bool where
  True == True = True
  False == False = True
  _ == _ = False

-- 多态函数
id :: a -> a
id x = x

-- 类型约束
maximum :: Ord a => [a] -> a
maximum [] = error "Empty list"
maximum [x] = x
maximum (x:xs) = max x (maximum xs)
```

## 8. 函数式编程最佳实践

### 1. 使用纯函数

```haskell
-- 好的做法：纯函数
pureAdd :: Int -> Int -> Int
pureAdd x y = x + y

-- 避免的做法：有副作用
impureAdd :: Int -> Int -> IO Int
impureAdd x y = do
  putStrLn "Adding numbers"
  return (x + y)
```

### 2. 使用高阶函数

```haskell
-- 使用map而不是显式递归
doubleAll :: [Int] -> [Int]
doubleAll = map (*2)

-- 使用filter进行过滤
evens :: [Int] -> [Int]
evens = filter even

-- 使用fold进行归约
sumList :: [Int] -> Int
sumList = foldl (+) 0
```

### 3. 避免可变状态

```haskell
-- 好的做法：不可变数据
data Point = Point { x :: Double, y :: Double }

movePoint :: Point -> Double -> Double -> Point
movePoint (Point x y) dx dy = Point (x + dx) (y + dy)

-- 避免的做法：可变状态
-- 在Haskell中通常通过IO或ST monad处理
```

## 9. 性能考虑

### 1. 尾递归优化

```haskell
-- 尾递归版本
sumTail :: [Int] -> Int
sumTail = go 0
  where
    go acc [] = acc
    go acc (x:xs) = go (acc + x) xs

-- 非尾递归版本
sumRec :: [Int] -> Int
sumRec [] = 0
sumRec (x:xs) = x + sumRec xs
```

### 2. 惰性求值优化

```haskell
-- 利用惰性求值
primes :: [Integer]
primes = sieve [2..]
  where
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

-- 只计算需要的素数
nthPrime :: Int -> Integer
nthPrime n = primes !! (n - 1)
```

## 10. 实际应用示例

### 1. 数据处理管道

```haskell
-- 数据处理管道
processData :: [String] -> [Int]
processData = map read
            . filter (not . null)
            . map (filter isDigit)
            . map (takeWhile (/= ' '))

-- 使用函数组合
processData' :: [String] -> [Int]
processData' = map read . filter (not . null) . map (filter isDigit) . map (takeWhile (/= ' '))
```

### 2. 配置解析

```haskell
data Config = Config
  { host :: String
  , port :: Int
  , debug :: Bool
  }

parseConfig :: String -> Maybe Config
parseConfig input = do
  let lines = map words (lines input)
  host <- lookup "host" (map parsePair lines)
  port <- lookup "port" (map parsePair lines) >>= readMaybe
  debug <- lookup "debug" (map parsePair lines) >>= readMaybe
  return Config { host = host, port = port, debug = debug }
  where
    parsePair [key, value] = (key, value)
    parsePair _ = ("", "")
```

## 总结

函数式编程基础为Haskell编程提供了坚实的理论基础。通过纯函数、高阶函数、不可变数据、模式匹配、递归、惰性求值和类型系统等核心概念，我们可以构建出安全、可靠、易于理解和维护的程序。

这些概念不仅适用于Haskell，也为其他函数式编程语言和函数式编程范式提供了重要的理论基础。

---

**相关链接**：

- [Haskell基础](../README.md)
- [高级特性](../02-Advanced-Features/README.md)
- [算法实现](../03-Algorithm-Implementation/README.md)
- [形式化证明](../04-Formal-Proofs/README.md)
