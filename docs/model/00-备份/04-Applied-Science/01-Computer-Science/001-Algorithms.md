# 算法基础 - 计算机科学应用

## 📋 概述

本文档介绍计算机科学中的核心算法理论，包括算法分析、设计模式、复杂度理论，以及Haskell中的算法实现。

## 🎯 快速导航

### 相关理论
- [计算复杂性理论](./../03-Theory/15-Computational-Complexity.md)
- [形式化方法](./../03-Theory/04-Formal-Methods/001-Model-Checking.md)
- [类型系统理论](./../03-Theory/01-Programming-Language-Theory/004-Type-System-Theory.md)

### 实现示例
- [Haskell算法实现](./../../haskell/07-Algorithms/001-Sorting-Algorithms.md)
- [数据结构实现](./../../haskell/06-Data-Structures/001-Basic-Data-Structures.md)

## 📚 理论基础

### 算法定义

**定义 1.1 (算法)**
算法是一个有限的、明确的、可执行的指令序列，用于解决特定问题：

$$\text{Algorithm} = (I, O, P, T)$$

其中：
- $I$ 是输入集合
- $O$ 是输出集合  
- $P$ 是处理步骤
- $T$ 是终止条件

### 算法复杂度

**定义 1.2 (时间复杂度)**
算法的时间复杂度 $T(n)$ 表示输入规模为 $n$ 时的执行时间：

$$T(n) = O(f(n)) \iff \exists c, n_0 > 0: \forall n \geq n_0, T(n) \leq c \cdot f(n)$$

**定义 1.3 (空间复杂度)**
算法的空间复杂度 $S(n)$ 表示输入规模为 $n$ 时的内存使用：

$$S(n) = O(f(n)) \iff \exists c, n_0 > 0: \forall n \geq n_0, S(n) \leq c \cdot f(n)$$

## 🔍 核心算法类别

### 1. 排序算法

#### 快速排序 (QuickSort)

**算法描述**:
1. 选择基准元素 (pivot)
2. 分区：将小于基准的元素放在左边，大于基准的元素放在右边
3. 递归排序左右两个子数组

**复杂度分析**:
- 平均时间复杂度: $O(n \log n)$
- 最坏时间复杂度: $O(n^2)$
- 空间复杂度: $O(\log n)$

**Haskell实现**:

```haskell
-- 快速排序实现
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
    quicksort smaller ++ [x] ++ quicksort larger
  where
    smaller = [a | a <- xs, a <= x]
    larger  = [a | a <- xs, a > x]

-- 优化版本：使用随机基准
quicksortRandom :: Ord a => [a] -> IO [a]
quicksortRandom [] = return []
quicksortRandom xs = do
    let n = length xs
    pivotIndex <- randomRIO (0, n-1)
    let pivot = xs !! pivotIndex
    let smaller = [a | a <- xs, a < pivot]
    let equal = [a | a <- xs, a == pivot]
    let larger = [a | a <- xs, a > pivot]
    smaller' <- quicksortRandom smaller
    larger' <- quicksortRandom larger
    return $ smaller' ++ equal ++ larger'

-- 性能测试
testQuicksort :: IO ()
testQuicksort = do
    let testData = [3,1,4,1,5,9,2,6,5,3,5]
    putStrLn "原始数据:"
    print testData
    sorted <- quicksortRandom testData
    putStrLn "排序结果:"
    print sorted
```

#### 归并排序 (MergeSort)

**算法描述**:
1. 将数组分成两半
2. 递归排序两半
3. 合并两个有序数组

**复杂度分析**:
- 时间复杂度: $O(n \log n)$
- 空间复杂度: $O(n)$

**Haskell实现**:

```haskell
-- 归并排序实现
mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = merge (mergeSort left) (mergeSort right)
  where
    (left, right) = splitAt (length xs `div` 2) xs

-- 合并两个有序列表
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y    = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 并行归并排序
parallelMergeSort :: Ord a => [a] -> IO [a]
parallelMergeSort [] = return []
parallelMergeSort [x] = return [x]
parallelMergeSort xs = do
    let (left, right) = splitAt (length xs `div` 2) xs
    left' <- async $ parallelMergeSort left
    right' <- async $ parallelMergeSort right
    leftResult <- wait left'
    rightResult <- wait right'
    return $ merge leftResult rightResult
```

### 2. 搜索算法

#### 二分搜索

**算法描述**:
在有序数组中查找目标值，通过比较中间元素来缩小搜索范围。

**复杂度分析**:
- 时间复杂度: $O(\log n)$
- 空间复杂度: $O(1)$

**Haskell实现**:

```haskell
-- 二分搜索实现
binarySearch :: Ord a => a -> [a] -> Maybe Int
binarySearch target xs = go 0 (length xs - 1)
  where
    go left right
      | left > right = Nothing
      | otherwise = 
          let mid = (left + right) `div` 2
              midVal = xs !! mid
          in case compare target midVal of
               LT -> go left (mid - 1)
               GT -> go (mid + 1) right
               EQ -> Just mid

-- 函数式二分搜索
binarySearchFunctional :: Ord a => a -> [a] -> Maybe Int
binarySearchFunctional target xs = 
    findIndex (== target) $ takeWhile (<= target) xs

-- 测试二分搜索
testBinarySearch :: IO ()
testBinarySearch = do
    let sortedList = [1,3,5,7,9,11,13,15,17,19]
    putStrLn "有序列表:"
    print sortedList
    putStrLn "查找元素 7:"
    print $ binarySearch 7 sortedList
    putStrLn "查找元素 10:"
    print $ binarySearch 10 sortedList
```

### 3. 图算法

#### 深度优先搜索 (DFS)

**算法描述**:
从起始节点开始，沿着图的边尽可能深入地探索，直到无法继续为止。

**复杂度分析**:
- 时间复杂度: $O(V + E)$
- 空间复杂度: $O(V)$

**Haskell实现**:

```haskell
-- 图表示
type Graph = [(Int, [Int])]

-- 深度优先搜索
dfs :: Graph -> Int -> [Int]
dfs graph start = go [start] []
  where
    go [] visited = reverse visited
    go (x:xs) visited
      | x `elem` visited = go xs visited
      | otherwise = 
          let neighbors = findNeighbors x graph
              newVisited = x : visited
              newStack = neighbors ++ xs
          in go newStack newVisited

-- 查找邻居节点
findNeighbors :: Int -> Graph -> [Int]
findNeighbors node graph = 
    case lookup node graph of
      Just neighbors -> neighbors
      Nothing -> []

-- 测试DFS
testDFS :: IO ()
testDFS = do
    let graph = [(1, [2, 3]), (2, [4, 5]), (3, [6]), (4, []), (5, []), (6, [])]
    putStrLn "图结构:"
    print graph
    putStrLn "从节点1开始的DFS遍历:"
    print $ dfs graph 1
```

#### 广度优先搜索 (BFS)

**算法描述**:
从起始节点开始，先访问所有相邻节点，然后再访问这些节点的相邻节点。

**复杂度分析**:
- 时间复杂度: $O(V + E)$
- 空间复杂度: $O(V)$

**Haskell实现**:

```haskell
-- 广度优先搜索
bfs :: Graph -> Int -> [Int]
bfs graph start = go [start] [] []
  where
    go [] visited _ = reverse visited
    go (x:xs) visited queue
      | x `elem` visited = go xs visited queue
      | otherwise = 
          let neighbors = findNeighbors x graph
              newVisited = x : visited
              newQueue = queue ++ neighbors
          in go xs newVisited newQueue

-- 带层级的BFS
bfsWithLevels :: Graph -> Int -> [(Int, Int)]
bfsWithLevels graph start = go [(start, 0)] [] []
  where
    go [] visited _ = reverse visited
    go ((node, level):xs) visited queue
      | node `elem` map fst visited = go xs visited queue
      | otherwise = 
          let neighbors = findNeighbors node graph
              newVisited = (node, level) : visited
              newQueue = queue ++ [(n, level + 1) | n <- neighbors]
          in go xs newVisited newQueue
```

### 4. 动态规划

#### 斐波那契数列

**问题描述**:
计算第n个斐波那契数：$F(n) = F(n-1) + F(n-2)$，其中 $F(0) = 0, F(1) = 1$

**动态规划解法**:
- 时间复杂度: $O(n)$
- 空间复杂度: $O(1)$

**Haskell实现**:

```haskell
-- 递归版本（指数复杂度）
fibRecursive :: Integer -> Integer
fibRecursive 0 = 0
fibRecursive 1 = 1
fibRecursive n = fibRecursive (n-1) + fibRecursive (n-2)

-- 动态规划版本
fibDP :: Integer -> Integer
fibDP n = go n 0 1
  where
    go 0 a _ = a
    go 1 _ b = b
    go n a b = go (n-1) b (a + b)

-- 记忆化版本
fibMemo :: Integer -> Integer
fibMemo n = memo !! fromIntegral n
  where
    memo = 0 : 1 : zipWith (+) memo (tail memo)

-- 性能比较
testFibPerformance :: IO ()
testFibPerformance = do
    let n = 40
    putStrLn $ "计算第 " ++ show n ++ " 个斐波那契数:"
    
    start1 <- getCurrentTime
    let result1 = fibDP n
    end1 <- getCurrentTime
    putStrLn $ "动态规划: " ++ show result1 ++ " (时间: " ++ show (diffUTCTime end1 start1) ++ ")"
    
    start2 <- getCurrentTime
    let result2 = fibMemo n
    end2 <- getCurrentTime
    putStrLn $ "记忆化: " ++ show result2 ++ " (时间: " ++ show (diffUTCTime end2 start2) ++ ")"
```

#### 最长公共子序列 (LCS)

**问题描述**:
给定两个字符串，找到它们的最长公共子序列。

**动态规划解法**:
- 时间复杂度: $O(mn)$
- 空间复杂度: $O(mn)$

**Haskell实现**:

```haskell
-- 最长公共子序列
lcs :: String -> String -> String
lcs xs ys = reverse $ go (length xs) (length ys)
  where
    dp = array ((0,0), (length xs, length ys)) 
         [((i,j), lcsLength i j) | i <- [0..length xs], j <- [0..length ys]]
    
    lcsLength 0 _ = 0
    lcsLength _ 0 = 0
    lcsLength i j
      | xs !! (i-1) == ys !! (j-1) = dp ! (i-1, j-1) + 1
      | otherwise = max (dp ! (i-1, j)) (dp ! (i, j-1))
    
    go 0 _ = ""
    go _ 0 = ""
    go i j
      | xs !! (i-1) == ys !! (j-1) = xs !! (i-1) : go (i-1) (j-1)
      | dp ! (i-1, j) >= dp ! (i, j-1) = go (i-1) j
      | otherwise = go i (j-1)

-- 测试LCS
testLCS :: IO ()
testLCS = do
    let str1 = "ABCDGH"
        str2 = "AEDFHR"
    putStrLn $ "字符串1: " ++ str1
    putStrLn $ "字符串2: " ++ str2
    putStrLn $ "最长公共子序列: " ++ lcs str1 str2
```

## 🔬 算法分析

### 复杂度类别

**定义 1.4 (P类问题)**
P类问题是可以在多项式时间内解决的问题：

$$P = \{L : \exists \text{TM } M, \exists k \in \mathbb{N}, \forall x \in L, T_M(x) = O(|x|^k)\}$$

**定义 1.5 (NP类问题)**
NP类问题是可以在多项式时间内验证解的问题：

$$NP = \{L : \exists \text{TM } M, \exists k \in \mathbb{N}, \forall x \in L, \exists y, |y| = O(|x|^k), M(x,y) = 1\}$$

### 算法优化策略

#### 1. 分治策略

**定理 1.1 (分治复杂度)**
如果分治算法将问题分成 $a$ 个子问题，每个子问题规模为 $n/b$，合并时间为 $f(n)$，则总复杂度为：

$$T(n) = aT(n/b) + f(n)$$

#### 2. 贪心策略

**定义 1.6 (贪心选择性质)**
贪心算法在每一步都选择当前看起来最优的选择，希望最终得到全局最优解。

#### 3. 动态规划

**定义 1.7 (最优子结构)**
问题的最优解包含其子问题的最优解。

## 🧪 实验验证

### 性能测试框架

```haskell
-- 性能测试框架
data BenchmarkResult = BenchmarkResult
  { algorithmName :: String
  , inputSize :: Int
  , executionTime :: Double
  , memoryUsage :: Int
  }

-- 运行基准测试
runBenchmark :: (a -> b) -> [a] -> String -> IO BenchmarkResult
runBenchmark algorithm inputs name = do
    start <- getCurrentTime
    let result = map algorithm inputs
    end <- getCurrentTime
    let time = realToFrac $ diffUTCTime end start
    return $ BenchmarkResult name (length inputs) time 0

-- 比较算法性能
compareAlgorithms :: IO ()
compareAlgorithms = do
    let testData = [1..1000] :: [Int]
    
    result1 <- runBenchmark quicksort testData "QuickSort"
    result2 <- runBenchmark mergeSort testData "MergeSort"
    
    putStrLn "算法性能比较:"
    putStrLn $ "QuickSort: " ++ show (executionTime result1) ++ "s"
    putStrLn $ "MergeSort: " ++ show (executionTime result2) ++ "s"
```

## 📊 可视化分析

### 复杂度图表

```mermaid
graph TD
    A[算法复杂度] --> B[常数时间 O(1)]
    A --> C[对数时间 O(log n)]
    A --> D[线性时间 O(n)]
    A --> E[线性对数时间 O(n log n)]
    A --> F[平方时间 O(n²)]
    A --> G[指数时间 O(2ⁿ)]
    
    B --> H[数组访问]
    C --> I[二分搜索]
    D --> J[线性搜索]
    E --> K[归并排序]
    F --> L[冒泡排序]
    G --> M[递归斐波那契]
```

## 🔗 相关链接

### 理论基础
- [计算复杂性理论](./../03-Theory/15-Computational-Complexity.md)
- [形式化方法](./../03-Theory/04-Formal-Methods/001-Model-Checking.md)
- [类型系统理论](./../03-Theory/01-Programming-Language-Theory/004-Type-System-Theory.md)

### 实现示例
- [Haskell算法实现](./../../haskell/07-Algorithms/001-Sorting-Algorithms.md)
- [数据结构实现](./../../haskell/06-Data-Structures/001-Basic-Data-Structures.md)
- [性能优化](./../../haskell/09-Performance/001-Algorithm-Optimization.md)

### 应用领域
- [软件工程算法](./002-Software-Engineering-Algorithms.md)
- [人工智能算法](./003-AI-Algorithms.md)
- [分布式算法](./004-Distributed-Algorithms.md)

---

**最后更新**: 2024年12月
**状态**: ✅ 完成
**版本**: 1.0
**作者**: 形式化知识体系团队 