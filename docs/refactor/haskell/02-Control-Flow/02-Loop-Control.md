# Haskell 循环控制

## 概述

Haskell作为纯函数式语言，不提供传统的命令式循环结构，而是通过递归、高阶函数和列表推导来实现循环控制。本文档详细介绍这些函数式循环控制机制。

## 1. 递归循环

### 1.1 基本递归

```haskell
-- 基本递归函数
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 尾递归优化
factorialTail :: Integer -> Integer
factorialTail n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)

-- 列表递归处理
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs
```

### 1.2 相互递归

```haskell
-- 相互递归函数
isEven :: Int -> Bool
isEven 0 = True
isEven n = isOdd (n - 1)

isOdd :: Int -> Bool
isOdd 0 = False
isOdd n = isEven (n - 1)

-- 复杂相互递归
ackermann :: Int -> Int -> Int
ackermann 0 n = n + 1
ackermann m 0 = ackermann (m - 1) 1
ackermann m n = ackermann (m - 1) (ackermann m (n - 1))
```

## 2. 高阶函数循环

### 2.1 map函数

```haskell
-- map函数实现
map' :: (a -> b) -> [a] -> [b]
map' _ [] = []
map' f (x:xs) = f x : map' f xs

-- 使用map
doubleList :: [Int] -> [Int]
doubleList = map (*2)

stringLengths :: [String] -> [Int]
stringLengths = map length

-- 多参数map
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' _ [] _ = []
zipWith' _ _ [] = []
zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
```

### 2.2 filter函数

```haskell
-- filter函数实现
filter' :: (a -> Bool) -> [a] -> [a]
filter' _ [] = []
filter' p (x:xs)
  | p x = x : filter' p xs
  | otherwise = filter' p xs

-- 使用filter
evens :: [Int] -> [Int]
evens = filter even

primes :: [Int] -> [Int]
primes = filter isPrime
  where
    isPrime n = n > 1 && all (\x -> n `mod` x /= 0) [2..floor (sqrt (fromIntegral n))]
```

### 2.3 fold函数

```haskell
-- foldl实现
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' _ acc [] = acc
foldl' f acc (x:xs) = foldl' f (f acc x) xs

-- foldr实现
foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' _ acc [] = acc
foldr' f acc (x:xs) = f x (foldr' f acc xs)

-- 使用fold函数
sum' :: [Int] -> Int
sum' = foldl' (+) 0

product' :: [Int] -> Int
product' = foldl' (*) 1

reverse' :: [a] -> [a]
reverse' = foldl' (flip (:)) []
```

## 3. 列表推导

### 3.1 基本列表推导

```haskell
-- 基本列表推导
squares :: [Int] -> [Int]
squares xs = [x^2 | x <- xs]

-- 条件列表推导
evenSquares :: [Int] -> [Int]
evenSquares xs = [x^2 | x <- xs, even x]

-- 多生成器列表推导
pairs :: [Int] -> [Int] -> [(Int, Int)]
pairs xs ys = [(x, y) | x <- xs, y <- ys]

-- 嵌套列表推导
matrix :: Int -> Int -> [[Int]]
matrix rows cols = [[i * cols + j | j <- [0..cols-1]] | i <- [0..rows-1]]
```

### 3.2 复杂列表推导

```haskell
-- 素数生成
primesList :: [Integer]
primesList = 2 : [n | n <- [3,5..], isPrime n]
  where
    isPrime n = all (\p -> n `mod` p /= 0) (takeWhile (\p -> p^2 <= n) primesList)

-- 完美数
perfectNumbers :: [Integer]
perfectNumbers = [n | n <- [1..], isPerfect n]
  where
    isPerfect n = n == sum [d | d <- [1..n-1], n `mod` d == 0]

-- 组合生成
combinations :: Int -> [a] -> [[a]]
combinations 0 _ = [[]]
combinations n xs
  | n > length xs = []
  | otherwise = [y:ys | y:xs' <- tails xs, ys <- combinations (n-1) xs']
```

## 4. 无限循环

### 4.1 无限列表

```haskell
-- 无限自然数列表
naturals :: [Integer]
naturals = [0..]

-- 无限斐波那契数列
fibonacci :: [Integer]
fibonacci = 0 : 1 : zipWith (+) fibonacci (tail fibonacci)

-- 无限素数列表
primesInfinite :: [Integer]
primesInfinite = 2 : [n | n <- [3,5..], isPrime n]
  where
    isPrime n = all (\p -> n `mod` p /= 0) (takeWhile (\p -> p^2 <= n) primesInfinite)
```

### 4.2 惰性求值循环

```haskell
-- 惰性计算示例
expensiveComputation :: Int -> Int
expensiveComputation n = sum [1..n]

-- 条件惰性计算
conditionalLoop :: Bool -> Int -> [Int]
conditionalLoop True n = [expensiveComputation i | i <- [1..n]]
conditionalLoop False _ = []

-- 无限流处理
streamProcess :: [Int] -> [Int]
streamProcess = map (*2) . filter even
```

## 5. 循环控制的形式化语义

### 5.1 递归语义

递归函数的语义可以定义为：

$$\text{rec}(f, x) = \begin{cases}
\text{base}(x) & \text{if } \text{base-case}(x) \\
f(\text{rec}(f, \text{step}(x))) & \text{otherwise}
\end{cases}$$

### 5.2 高阶函数语义

map函数的语义：

$$\text{map}(f, [x_1, x_2, \ldots, x_n]) = [f(x_1), f(x_2), \ldots, f(x_n)]$$

fold函数的语义：

$$\text{foldl}(f, z, [x_1, x_2, \ldots, x_n]) = f(f(\ldots f(f(z, x_1), x_2), \ldots), x_n)$$

### 5.3 列表推导语义

列表推导的语义：

$$[e | x_1 \leftarrow xs_1, x_2 \leftarrow xs_2, \ldots, x_n \leftarrow xs_n, p_1, p_2, \ldots, p_m] = \{e | x_1 \in xs_1, x_2 \in xs_2, \ldots, x_n \in xs_n, p_1, p_2, \ldots, p_m\}$$

## 6. 高级循环技术

### 6.1 循环融合

```haskell
-- 循环融合优化
-- 未优化版本
inefficient :: [Int] -> Int
inefficient xs = sum (map (*2) (filter even xs))

-- 优化版本
efficient :: [Int] -> Int
efficient = foldl' (+) 0 . map (*2) . filter even

-- 进一步优化
mostEfficient :: [Int] -> Int
mostEfficient = foldl' (\acc x -> if even x then acc + 2*x else acc) 0
```

### 6.2 循环展开

```haskell
-- 循环展开
unfold :: Int -> [Int]
unfold n = take n [0..]

-- 自定义展开
unfoldr' :: (b -> Maybe (a, b)) -> b -> [a]
unfoldr' f b = case f b of
  Nothing -> []
  Just (a, b') -> a : unfoldr' f b'

-- 使用展开
range :: Int -> Int -> [Int]
range start end = unfoldr' (\n -> if n > end then Nothing else Just (n, n+1)) start
```

### 6.3 循环并行化

```haskell
-- 并行map
import Control.Parallel.Strategies

parallelMap :: (a -> b) -> [a] -> [b]
parallelMap f xs = map f xs `using` parList rseq

-- 并行fold
parallelSum :: [Int] -> Int
parallelSum xs = sum xs `using` parList rseq

-- 分块并行处理
chunkedParallel :: Int -> (a -> b) -> [a] -> [b]
chunkedParallel chunkSize f xs = 
  concat $ map (map f) (chunksOf chunkSize xs) `using` parList rseq
  where
    chunksOf n [] = []
    chunksOf n xs = take n xs : chunksOf n (drop n xs)
```

## 7. 实践示例

### 7.1 数值计算循环

```haskell
-- 数值积分
integrate :: (Double -> Double) -> Double -> Double -> Double -> Double
integrate f a b n = 
  let h = (b - a) / n
      xs = [a + i * h | i <- [0..n]]
  in h * sum [f x | x <- xs]

-- 牛顿法求根
newtonMethod :: (Double -> Double) -> (Double -> Double) -> Double -> Double -> Double
newtonMethod f f' x0 tolerance = 
  let next x = x - f x / f' x
      iterate' x = if abs (f x) < tolerance 
                   then x 
                   else iterate' (next x)
  in iterate' x0

-- 使用示例
sqrtNewton :: Double -> Double
sqrtNewton x = newtonMethod (\y -> y^2 - x) (\y -> 2*y) 1.0 1e-10
```

### 7.2 数据处理循环

```haskell
-- 数据流处理
dataStream :: [Int] -> [Int]
dataStream = 
  filter (>0) .           -- 过滤正数
  map (*2) .              -- 翻倍
  takeWhile (<100) .      -- 限制范围
  drop 5                  -- 跳过前5个

-- 批处理
batchProcess :: Int -> [a] -> [[a]]
batchProcess size = 
  unfoldr' (\xs -> if null xs then Nothing else Just (take size xs, drop size xs))

-- 滑动窗口
slidingWindow :: Int -> [a] -> [[a]]
slidingWindow n xs = 
  [take n (drop i xs) | i <- [0..length xs - n]]
```

### 7.3 游戏循环

```haskell
-- 游戏状态
data GameState = GameState 
  { playerPos :: (Int, Int)
  , score :: Int
  , gameOver :: Bool
  }

-- 游戏循环
gameLoop :: GameState -> [String] -> GameState
gameLoop state [] = state
gameLoop state (cmd:cmds) = 
  let newState = processCommand state cmd
  in if gameOver newState 
     then newState 
     else gameLoop newState cmds

-- 命令处理
processCommand :: GameState -> String -> GameState
processCommand state "up" = state { playerPos = (x, y+1) }
  where (x, y) = playerPos state
processCommand state "down" = state { playerPos = (x, y-1) }
  where (x, y) = playerPos state
processCommand state "left" = state { playerPos = (x-1, y) }
  where (x, y) = playerPos state
processCommand state "right" = state { playerPos = (x+1, y) }
  where (x, y) = playerPos state
processCommand state _ = state
```

## 8. 性能优化

### 8.1 尾递归优化

```haskell
-- 非尾递归（可能导致栈溢出）
factorialBad :: Integer -> Integer
factorialBad 0 = 1
factorialBad n = n * factorialBad (n - 1)

-- 尾递归（优化后）
factorialGood :: Integer -> Integer
factorialGood n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)
```

### 8.2 惰性求值优化

```haskell
-- 严格求值
strictSum :: [Int] -> Int
strictSum = foldl' (+) 0

-- 惰性求值（适用于无限列表）
lazySum :: [Int] -> Int
lazySum = foldr (+) 0

-- 混合策略
hybridSum :: [Int] -> Int
hybridSum xs = 
  let finite = take 1000 xs  -- 有限部分严格求值
      infinite = drop 1000 xs -- 无限部分惰性求值
  in strictSum finite + lazySum infinite
```

## 总结

Haskell的循环控制机制包括：

1. **递归**：基本递归、尾递归、相互递归
2. **高阶函数**：map、filter、fold等
3. **列表推导**：声明式循环控制
4. **无限循环**：惰性求值支持的无限数据结构

这些机制提供了强大而高效的函数式循环控制能力，避免了命令式循环的副作用。

## 相关链接

- [条件控制](01-Conditional-Control.md)
- [执行流](../03-Execution-Flow/01-Function-Execution.md)
- [数据流](../04-Data-Flow/01-Data-Passing.md)
- [设计模式](../06-Design-Patterns/01-Functional-Patterns.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0 