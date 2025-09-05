# 算法

## 概述

本文档介绍重要的算法及其在Haskell中的实现。

## 排序算法

### 快速排序

```haskell
-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  let smaller = [a | a <- xs, a <= x]
      larger = [a | a <- xs, a > x]
  in quicksort smaller ++ [x] ++ quicksort larger

-- 优化版本：使用Data.List.partition
quicksort' :: Ord a => [a] -> [a]
quicksort' [] = []
quicksort' (x:xs) = 
  let (smaller, larger) = partition (<= x) xs
  in quicksort' smaller ++ [x] ++ quicksort' larger
```

### 归并排序

```haskell
-- 归并排序
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergesort left) (mergesort right)

-- 归并两个有序列表
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys
```

## 搜索算法

### 二分搜索

```haskell
-- 二分搜索
binarySearch :: Ord a => a -> [a] -> Maybe Int
binarySearch x xs = binarySearch' x xs 0 (length xs - 1)

binarySearch' :: Ord a => a -> [a] -> Int -> Int -> Maybe Int
binarySearch' x xs left right
  | left > right = Nothing
  | otherwise = 
      let mid = (left + right) `div` 2
          midVal = xs !! mid
      in case compare x midVal of
           LT -> binarySearch' x xs left (mid - 1)
           EQ -> Just mid
           GT -> binarySearch' x xs (mid + 1) right
```

### 深度优先搜索

```haskell
-- 图的深度优先搜索
data Graph a = Graph [(a, [a])]

dfs :: Eq a => Graph a -> a -> [a]
dfs graph start = dfs' graph start []

dfs' :: Eq a => Graph a -> a -> [a] -> [a]
dfs' graph node visited
  | node `elem` visited = visited
  | otherwise = 
      let neighbors = findNeighbors graph node
          newVisited = node : visited
      in foldr (dfs' graph) newVisited neighbors

findNeighbors :: Eq a => Graph a -> a -> [a]
findNeighbors (Graph edges) node = 
  case lookup node edges of
    Just neighbors -> neighbors
    Nothing -> []
```

## 图算法

### Dijkstra算法

```haskell
-- Dijkstra最短路径算法
data WeightedGraph a = WeightedGraph [(a, [(a, Int)])]

dijkstra :: (Eq a, Ord a) => WeightedGraph a -> a -> Map a Int
dijkstra graph start = 
  let initialDistances = Map.singleton start 0
      initialQueue = Set.singleton (0, start)
  in dijkstra' graph initialDistances initialQueue

dijkstra' :: (Eq a, Ord a) => WeightedGraph a -> Map a Int -> Set (Int, a) -> Map a Int
dijkstra' graph distances queue
  | Set.null queue = distances
  | otherwise = 
      let ((dist, node), newQueue) = Set.deleteFindMin queue
          neighbors = findWeightedNeighbors graph node
          (updatedDistances, updatedQueue) = 
            foldr (updateDistance dist node) (distances, newQueue) neighbors
      in dijkstra' graph updatedDistances updatedQueue

updateDistance :: (Eq a, Ord a) => Int -> a -> (a, Int) -> (Map a Int, Set (Int, a)) -> (Map a Int, Set (Int, a))
updateDistance currentDist current (neighbor, weight) (distances, queue) = 
  let newDist = currentDist + weight
      oldDist = Map.findWithDefault maxBound neighbor distances
  in if newDist < oldDist
     then (Map.insert neighbor newDist distances, Set.insert (newDist, neighbor) queue)
     else (distances, queue)
```

## 动态规划

### 斐波那契数列

```haskell
-- 动态规划：斐波那契数列
fibonacci :: Int -> Integer
fibonacci n = fibArray !! n
  where
    fibArray = 0 : 1 : zipWith (+) fibArray (tail fibArray)

-- 记忆化版本
fibonacciMemo :: Int -> Integer
fibonacciMemo n = fibMemo n Map.empty
  where
    fibMemo 0 memo = (0, memo)
    fibMemo 1 memo = (1, memo)
    fibMemo n memo = 
      case Map.lookup n memo of
        Just result -> (result, memo)
        Nothing -> 
          let (fib1, memo1) = fibMemo (n-1) memo
              (fib2, memo2) = fibMemo (n-2) memo1
              result = fib1 + fib2
          in (result, Map.insert n result memo2)
```

### 最长公共子序列

```haskell
-- 最长公共子序列
lcs :: Eq a => [a] -> [a] -> [a]
lcs [] _ = []
lcs _ [] = []
lcs (x:xs) (y:ys)
  | x == y = x : lcs xs ys
  | otherwise = 
      let lcs1 = lcs (x:xs) ys
          lcs2 = lcs xs (y:ys)
      in if length lcs1 > length lcs2 then lcs1 else lcs2

-- 动态规划版本
lcsDP :: Eq a => [a] -> [a] -> [[Int]]
lcsDP xs ys = 
  let m = length xs
      n = length ys
      dp = array ((0,0), (m,n)) 
           [((i,j), lcsValue i j) | i <- [0..m], j <- [0..n]]
      lcsValue 0 _ = 0
      lcsValue _ 0 = 0
      lcsValue i j
        | xs !! (i-1) == ys !! (j-1) = dp ! (i-1, j-1) + 1
        | otherwise = max (dp ! (i-1, j)) (dp ! (i, j-1))
  in dp
```

## 字符串算法

### KMP算法

```haskell
-- KMP字符串匹配算法
kmp :: String -> String -> [Int]
kmp pattern text = 
  let lps = computeLPS pattern
      matches = kmpSearch pattern text lps
  in matches

-- 计算最长前缀后缀
computeLPS :: String -> [Int]
computeLPS pattern = 
  let n = length pattern
      lps = array (0, n-1) [(i, lpsValue i) | i <- [0..n-1]]
      lpsValue 0 = 0
      lpsValue i = 
        let prev = lps ! (i-1)
        in if pattern !! i == pattern !! prev
           then prev + 1
           else if prev == 0 then 0 else lps ! (prev - 1)
  in elems lps

-- KMP搜索
kmpSearch :: String -> String -> [Int] -> [Int]
kmpSearch pattern text lps = 
  let n = length pattern
      m = length text
      matches = kmpSearch' pattern text lps 0 0 n m
  in matches

kmpSearch' :: String -> String -> [Int] -> Int -> Int -> Int -> Int -> [Int]
kmpSearch' pattern text lps i j n m
  | i >= m = []
  | j == n = (i - j) : kmpSearch' pattern text lps i (lps !! (j-1)) n m
  | pattern !! j == text !! i = kmpSearch' pattern text lps (i+1) (j+1) n m
  | j > 0 = kmpSearch' pattern text lps i (lps !! (j-1)) n m
  | otherwise = kmpSearch' pattern text lps (i+1) 0 n m
```

## 数值算法

### 素数检测

```haskell
-- 素数检测
isPrime :: Integer -> Bool
isPrime n
  | n < 2 = False
  | n == 2 = True
  | even n = False
  | otherwise = 
      let limit = floor (sqrt (fromIntegral n))
      in all (\i -> n `mod` i /= 0) [3, 5..limit]

-- 埃拉托斯特尼筛法
sieve :: Integer -> [Integer]
sieve n = 
  let limit = floor (sqrt (fromIntegral n))
      candidates = [2..n]
      sieve' [] = []
      sieve' (p:xs) = 
        p : sieve' [x | x <- xs, x `mod` p /= 0]
  in sieve' candidates
```

## 性能分析

### 时间复杂度

```haskell
-- 算法复杂度分析
data Complexity = O1 | OLogN | ON | ONLogN | ON2 | ON3 | O2N

-- 复杂度比较
complexityComparison :: Complexity -> Complexity -> Ordering
complexityComparison O1 _ = LT
complexityComparison OLogN O1 = GT
complexityComparison OLogN _ = LT
complexityComparison ON OLogN = GT
complexityComparison ON _ = LT
complexityComparison ONLogN ON = GT
complexityComparison ONLogN _ = LT
complexityComparison ON2 ONLogN = GT
complexityComparison ON2 _ = LT
complexityComparison ON3 ON2 = GT
complexityComparison ON3 _ = LT
complexityComparison O2N ON3 = GT
complexityComparison O2N _ = LT
```

---

**相关链接**：

- [数据结构](./005-Data-Structures.md)
- [性能优化](./006-Performance-Optimization.md)
