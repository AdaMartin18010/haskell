# Haskell递归和列表处理

## 📚 快速导航

### 相关理论

- [函数式编程基础](./001-Functional-Programming-Foundation.md)
- [模式匹配](./002-Pattern-Matching.md)
- [类型理论基础](./03-Theory/04-Type-Theory/001-Simple-Type-Theory.md)

### 实现示例

- [高阶函数](./004-Higher-Order-Functions.md)
- [数据结构](./06-Data-Structures/001-Basic-Data-Structures.md)
- [算法实现](./07-Algorithms/001-Sorting-Algorithms.md)

### 应用领域

- [Web开发](./11-Web-Development/001-Web-Development-Foundation.md)
- [科学计算](./14-Real-World-Applications/002-Scientific-Computing.md)
- [数据处理](./14-Real-World-Applications/003-Data-Processing.md)

## 🎯 概述

递归是函数式编程的核心概念，它允许函数调用自身来解决问题。在Haskell中，递归与列表处理紧密结合，提供了强大而优雅的数据处理能力。

## 📖 1. 递归理论基础

### 1.1 递归定义

**定义 1.1 (递归函数)**
递归函数是调用自身的函数，通常包含：

1. **基础情况**：停止递归的条件
2. **递归情况**：调用自身的条件

**数学基础：**
$$f(n) = \begin{cases}
\text{base}(n) & \text{if } \text{condition}(n) \\
\text{combine}(n, f(\text{reduce}(n))) & \text{otherwise}
\end{cases}$$

**Haskell实现：**
```haskell
-- 基本递归函数结构
recursiveFunction :: Int -> Int
recursiveFunction n
  | n <= 0 = 0  -- 基础情况
  | otherwise = n + recursiveFunction (n - 1)  -- 递归情况

-- 斐波那契数列
fibonacci :: Int -> Integer
fibonacci 0 = 0  -- 基础情况
fibonacci 1 = 1  -- 基础情况
fibonacci n = fibonacci (n - 1) + fibonacci (n - 2)  -- 递归情况

-- 阶乘函数
factorial :: Integer -> Integer
factorial 0 = 1  -- 基础情况
factorial n = n * factorial (n - 1)  -- 递归情况
```

### 1.2 递归类型

**定义 1.2 (递归类型)**
递归类型包含自身的引用。

**数学定义：**
$$\text{RecursiveType} = \text{BaseType} + \text{RecursiveType}$$

**Haskell实现：**
```haskell
-- 递归列表类型
data List a
  = Nil
  | Cons a (List a)
  deriving (Show, Eq)

-- 递归树类型
data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

-- 递归表达式类型
data Expr
  = Number Int
  | Add Expr Expr
  | Multiply Expr Expr
  deriving (Show, Eq)

-- 递归函数类型
newtype Fix f = Fix { unFix :: f (Fix f) }

-- 列表函子
data ListF a r
  = NilF
  | ConsF a r
  deriving (Show, Eq)

instance Functor (ListF a) where
  fmap _ NilF = NilF
  fmap f (ConsF a r) = ConsF a (f r)

-- 从Fix构造列表
type List' a = Fix (ListF a)
```

### 1.3 递归终止性

**定理 1.1 (递归终止性)**
如果递归函数满足以下条件，则保证终止：
1. 存在基础情况
2. 每次递归调用都向基础情况收敛

**证明：** 通过结构归纳法证明。

**Haskell实现：**
```haskell
-- 保证终止的递归函数
terminatingFunction :: Int -> Int
terminatingFunction 0 = 0  -- 基础情况
terminatingFunction n = n + terminatingFunction (n - 1)  -- 向0收敛

-- 不保证终止的递归函数（示例）
-- nonTerminating :: Int -> Int
-- nonTerminating n = nonTerminating n  -- 不会终止

-- 使用累加器确保终止
terminatingWithAcc :: Int -> Int
terminatingWithAcc n = go n 0
  where
    go 0 acc = acc  -- 基础情况
    go n acc = go (n - 1) (acc + n)  -- 尾递归
```

## 🔧 2. 列表处理基础

### 2.1 列表类型

**定义 2.1 (列表类型)**
Haskell的列表是递归定义的数据类型。

**数学定义：**
$$[a] = \text{Nil} + a \times [a]$$

**Haskell实现：**
```haskell
-- 列表类型定义（内置）
-- data [a] = [] | a : [a]

-- 列表构造
emptyList :: [a]
emptyList = []

singleElement :: a -> [a]
singleElement x = [x]

multipleElements :: [a]
multipleElements = [1, 2, 3, 4, 5]

-- 列表范围
rangeList :: [Int]
rangeList = [1..10]

infiniteList :: [Integer]
infiniteList = [1..]

-- 列表推导式
squares :: [Int]
squares = [x^2 | x <- [1..10]]

evenSquares :: [Int]
evenSquares = [x^2 | x <- [1..10], even x]
```

### 2.2 基本列表操作

**定义 2.2 (列表操作)**
基本的列表操作包括构造、分解和转换。

**Haskell实现：**
```haskell
-- 列表构造
cons :: a -> [a] -> [a]
cons x xs = x : xs

-- 列表分解
head' :: [a] -> Maybe a
head' [] = Nothing
head' (x:_) = Just x

tail' :: [a] -> Maybe [a]
tail' [] = Nothing
tail' (_:xs) = Just xs

-- 列表长度
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

-- 列表连接
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

-- 列表反转
reverse' :: [a] -> [a]
reverse' [] = []
reverse' (x:xs) = reverse' xs ++ [x]

-- 高效反转（使用累加器）
reverseEfficient :: [a] -> [a]
reverseEfficient xs = go xs []
  where
    go [] acc = acc
    go (x:xs) acc = go xs (x:acc)
```

### 2.3 递归列表处理

**定义 2.3 (递归列表处理)**
使用递归处理列表的各种操作。

**Haskell实现：**
```haskell
-- 列表求和
sumList :: Num a => [a] -> a
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 列表乘积
productList :: Num a => [a] -> a
productList [] = 1
productList (x:xs) = x * productList xs

-- 列表最大值
maximumList :: Ord a => [a] -> Maybe a
maximumList [] = Nothing
maximumList [x] = Just x
maximumList (x:xs) =
  case maximumList xs of
    Nothing -> Just x
    Just maxTail -> Just (max x maxTail)

-- 列表最小值
minimumList :: Ord a => [a] -> Maybe a
minimumList [] = Nothing
minimumList [x] = Just x
minimumList (x:xs) =
  case minimumList xs of
    Nothing -> Just x
    Just minTail -> Just (min x minTail)

-- 列表查找
findElement :: Eq a => a -> [a] -> Bool
findElement _ [] = False
findElement x (y:ys)
  | x == y = True
  | otherwise = findElement x ys

-- 列表过滤
filterList :: (a -> Bool) -> [a] -> [a]
filterList _ [] = []
filterList p (x:xs)
  | p x = x : filterList p xs
  | otherwise = filterList p xs

-- 列表映射
mapList :: (a -> b) -> [a] -> [b]
mapList _ [] = []
mapList f (x:xs) = f x : mapList f xs
```

## 📊 3. 高级递归技术

### 3.1 尾递归

**定义 3.1 (尾递归)**
尾递归是递归调用在函数最后位置的递归。

**数学定义：**
$$\text{TailRecursive}(f) = f(x) = \text{helper}(x, \text{initial})$$

**Haskell实现：**
```haskell
-- 尾递归求和
sumTailRecursive :: Num a => [a] -> a
sumTailRecursive xs = go xs 0
  where
    go [] acc = acc
    go (x:xs) acc = go xs (acc + x)

-- 尾递归阶乘
factorialTailRecursive :: Integer -> Integer
factorialTailRecursive n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (acc * n)

-- 尾递归斐波那契
fibonacciTailRecursive :: Int -> Integer
fibonacciTailRecursive n = go n 0 1
  where
    go 0 a _ = a
    go 1 _ b = b
    go n a b = go (n - 1) b (a + b)

-- 尾递归列表反转
reverseTailRecursive :: [a] -> [a]
reverseTailRecursive xs = go xs []
  where
    go [] acc = acc
    go (x:xs) acc = go xs (x:acc)

-- 尾递归列表长度
lengthTailRecursive :: [a] -> Int
lengthTailRecursive xs = go xs 0
  where
    go [] acc = acc
    go (_:xs) acc = go xs (acc + 1)
```

### 3.2 相互递归

**定义 3.2 (相互递归)**
相互递归是多个函数相互调用的递归模式。

**数学定义：**
$$f(x) = g(x) \quad g(x) = f(x)$$

**Haskell实现：**
```haskell
-- 相互递归的奇偶判断
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd :: Int -> Bool
isOdd 0 = False
isOdd n = isEven (n - 1)

-- 相互递归的列表处理
takeEven :: [a] -> [a]
takeEven [] = []
takeEven [x] = [x]
takeEven (x:_:xs) = x : takeEven xs

takeOdd :: [a] -> [a]
takeOdd [] = []
takeOdd [_] = []
takeOdd (_:x:xs) = x : takeOdd xs

-- 相互递归的树处理
data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)
  deriving (Show, Eq)

-- 交替处理树的左右子树
processTreeAlternating :: Tree a -> [a]
processTreeAlternating Leaf = []
processTreeAlternating (Node x left right) =
  x : processTreeAlternatingRight left right

processTreeAlternatingRight :: Tree a -> Tree a -> [a]
processTreeAlternatingRight Leaf right = processTreeAlternating right
processTreeAlternatingRight (Node x left' right') right =
  x : processTreeAlternating left' right'
```

### 3.3 递归模式

**定义 3.3 (递归模式)**
常见的递归模式包括映射、折叠和展开。

**Haskell实现：**
```haskell
-- 映射模式
mapPattern :: (a -> b) -> [a] -> [b]
mapPattern _ [] = []
mapPattern f (x:xs) = f x : mapPattern f xs

-- 折叠模式
foldPattern :: (a -> b -> b) -> b -> [a] -> b
foldPattern _ acc [] = acc
foldPattern f acc (x:xs) = f x (foldPattern f acc xs)

-- 展开模式
unfoldPattern :: (b -> Maybe (a, b)) -> b -> [a]
unfoldPattern f seed =
  case f seed of
    Nothing -> []
    Just (a, newSeed) -> a : unfoldPattern f newSeed

-- 递归模式组合
mapFoldPattern :: (a -> b) -> [a] -> [b]
mapFoldPattern f = foldPattern (\x acc -> f x : acc) []

-- 使用展开模式生成列表
rangeUnfold :: Int -> Int -> [Int]
rangeUnfold start end = unfoldPattern next start
  where
    next current
      | current > end = Nothing
      | otherwise = Just (current, current + 1)

-- 斐波那契数列展开
fibonacciUnfold :: [Integer]
fibonacciUnfold = unfoldPattern nextFib (0, 1)
  where
    nextFib (a, b) = Just (a, (b, a + b))
```

## 🎯 4. 列表高级操作

### 4.1 列表推导式

**定义 4.1 (列表推导式)**
列表推导式是生成列表的简洁语法。

**数学基础：**
$$\{f(x) \mid x \in S, P(x)\}$$

**Haskell实现：**
```haskell
-- 基本列表推导式
basicComprehension :: [Int]
basicComprehension = [x | x <- [1..10]]

-- 带条件的列表推导式
filteredComprehension :: [Int]
filteredComprehension = [x | x <- [1..20], even x]

-- 多生成器的列表推导式
multiGenerator :: [(Int, Int)]
multiGenerator = [(x, y) | x <- [1..3], y <- [1..3]]

-- 嵌套列表推导式
nestedComprehension :: [Int]
nestedComprehension = [x*y | x <- [1..5], y <- [1..5], x*y < 20]

-- 字符串列表推导式
stringComprehension :: [String]
stringComprehension = [show x | x <- [1..10], x `mod` 2 == 0]

-- 复杂列表推导式
complexComprehension :: [(Int, Int)]
complexComprehension =
  [(x, y) | x <- [1..10], y <- [1..10], x + y == 10, x < y]
```

### 4.2 列表函数组合

**定义 4.2 (函数组合)**
将多个列表函数组合成复杂的数据处理管道。

**Haskell实现：**
```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 管道操作符
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 复杂数据处理管道
dataProcessingPipeline :: [String] -> [Int]
dataProcessingPipeline =
  filter (not . null)  -- 过滤空字符串
  . map read           -- 转换为数字
  . filter (> 0)       -- 过滤正数
  . map (* 2)          -- 乘以2

-- 使用管道操作符
dataProcessingPipeline' :: [String] -> [Int]
dataProcessingPipeline' xs =
  xs |> filter (not . null)
     |> map read
     |> filter (> 0)
     |> map (* 2)

-- 错误处理管道
safeDataProcessing :: [String] -> [Int]
safeDataProcessing =
  mapMaybe safeRead    -- 安全读取
  . filter (not . null) -- 过滤空字符串
  . filter (> 0)        -- 过滤正数

-- 安全读取函数
safeRead :: String -> Maybe Int
safeRead str = case reads str of
  [(n, "")] -> Just n
  _ -> Nothing
```

### 4.3 惰性列表

**定义 4.3 (惰性列表)**
惰性列表只在需要时才计算元素。

**数学基础：**
$$\text{LazyList} = \text{Thunk}(\text{ListComputation})$$

**Haskell实现：**
```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 只取需要的部分
takeFromInfinite :: Int -> [Integer]
takeFromInfinite n = take n infiniteList

-- 惰性斐波那契数列
lazyFibonacci :: [Integer]
lazyFibonacci = 0 : 1 : zipWith (+) lazyFibonacci (tail lazyFibonacci)

-- 惰性素数筛选
lazyPrimes :: [Integer]
lazyPrimes = sieve [2..]
  where
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

-- 惰性文件读取
lazyFileRead :: FilePath -> IO [String]
lazyFileRead path = do
  content <- readFile path
  return (lines content)

-- 惰性处理大文件
processLargeFile :: FilePath -> IO [String]
processLargeFile path = do
  lines <- lazyFileRead path
  return (take 100 (filter (not . null) lines))
```

## 🚀 5. 实际应用

### 5.1 数据处理

```haskell
-- CSV数据处理
data CSVRow = CSVRow
  { name :: String
  , age :: Int
  , salary :: Double
  } deriving (Show, Eq)

-- 解析CSV数据
parseCSV :: [String] -> [CSVRow]
parseCSV [] = []
parseCSV (line:lines) =
  case parseCSVRow line of
    Just row -> row : parseCSV lines
    Nothing -> parseCSV lines

parseCSVRow :: String -> Maybe CSVRow
parseCSVRow line =
  case words (map replaceComma line) of
    [name, ageStr, salaryStr] ->
      case (reads ageStr, reads salaryStr) of
        ([(age, "")], [(salary, "")]) ->
          Just (CSVRow name age salary)
        _ -> Nothing
    _ -> Nothing
  where
    replaceComma ',' = ' '
    replaceComma c = c

-- 数据统计
dataStats :: [Double] -> (Double, Double, Double)
dataStats xs = (mean, median, stdDev)
  where
    mean = sum xs / fromIntegral (length xs)
    median = sorted !! (length sorted `div` 2)
    stdDev = sqrt (sum (map (\x -> (x - mean)^2) xs) / fromIntegral (length xs))
    sorted = sort xs
```

### 5.2 算法实现

```haskell
-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) =
  quicksort (filter (< x) xs) ++
  [x] ++
  quicksort (filter (>= x) xs)

-- 归并排序
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs =
  merge (mergesort left) (mergesort right)
  where
    (left, right) = splitAt (length xs `div` 2) xs

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 深度优先搜索
dfs :: Eq a => (a -> [a]) -> a -> [a]
dfs neighbors start = go [start] []
  where
    go [] visited = reverse visited
    go (x:xs) visited
      | x `elem` visited = go xs visited
      | otherwise = go (neighbors x ++ xs) (x:visited)
```

### 5.3 函数式编程模式

```haskell
-- 函数式状态机
data State = S0 | S1 | S2 deriving (Show, Eq)
data Input = A | B deriving (Show, Eq)

-- 状态转换函数
transition :: State -> Input -> State
transition S0 A = S1
transition S0 B = S2
transition S1 A = S1
transition S1 B = S2
transition S2 A = S0
transition S2 B = S2

-- 状态机执行
runStateMachine :: [Input] -> State -> [State]
runStateMachine [] state = [state]
runStateMachine (input:inputs) state =
  state : runStateMachine inputs (transition state input)

-- 函数式解析器
data Parser a = Parser { runParser :: String -> Maybe (a, String) }

-- 基本解析器
char :: Char -> Parser Char
char c = Parser $ \s ->
  case s of
    (x:xs) | x == c -> Just (c, xs)
    _ -> Nothing

-- 解析器组合
(<|>) :: Parser a -> Parser a -> Parser a
p1 <|> p2 = Parser $ \s ->
  case runParser p1 s of
    Just result -> Just result
    Nothing -> runParser p2 s

-- 解析器应用
(<*>) :: Parser (a -> b) -> Parser a -> Parser b
pf <*> pa = Parser $ \s ->
  case runParser pf s of
    Just (f, s') ->
      case runParser pa s' of
        Just (a, s'') -> Just (f a, s'')
        Nothing -> Nothing
    Nothing -> Nothing
```

## 📈 6. 性能优化

### 6.1 递归优化

```haskell
-- 使用严格求值
{-# LANGUAGE BangPatterns #-}

strictSum :: [Int] -> Int
strictSum = go 0
  where
    go !acc [] = acc
    go !acc (x:xs) = go (acc + x) xs

-- 使用foldl'进行严格折叠
import Data.List (foldl')

strictFoldSum :: [Int] -> Int
strictFoldSum = foldl' (+) 0

-- 避免重复计算
memoizedFibonacci :: Int -> Integer
memoizedFibonacci = (map fib [0..] !!)
  where
    fib 0 = 0
    fib 1 = 1
    fib n = memoizedFibonacci (n-1) + memoizedFibonacci (n-2)
```

### 6.2 列表优化

```haskell
-- 使用Data.List的优化函数
import Data.List (sort, nub, group)

-- 高效去重
efficientNub :: Eq a => [a] -> [a]
efficientNub = nub

-- 高效排序
efficientSort :: Ord a => [a] -> [a]
efficientSort = sort

-- 使用Data.Vector进行高效操作
import qualified Data.Vector as V

vectorSum :: V.Vector Int -> Int
vectorSum = V.sum

vectorMap :: (a -> b) -> V.Vector a -> V.Vector b
vectorMap = V.map
```

## 🎯 总结

Haskell的递归和列表处理提供了：

1. **强大的递归能力**：支持各种递归模式
2. **惰性求值**：提高程序效率
3. **类型安全**：编译时检查
4. **函数组合**：构建复杂的数据处理管道
5. **性能优化**：支持各种优化技术

递归和列表处理是Haskell函数式编程的基础，它们使得代码更加简洁、安全和高效。

---

**相关文档**:
- [函数式编程基础](./001-Functional-Programming-Foundation.md)
- [模式匹配](./002-Pattern-Matching.md)
- [高阶函数](./004-Higher-Order-Functions.md)

**实现示例**:
- [数据结构](./06-Data-Structures/001-Basic-Data-Structures.md)
- [算法实现](./07-Algorithms/001-Sorting-Algorithms.md)
