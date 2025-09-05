# 排序算法 - 形式化理论与Haskell实现

## 📋 概述

排序算法是计算机科学中最基础也是最重要的算法之一。本文档从形式化理论的角度分析各种排序算法，并提供完整的Haskell实现。

## 🎯 形式化定义

### 排序问题的形式化描述

给定一个集合 $A$ 和全序关系 $\leq$，排序问题是找到一个双射函数 $f: \{1, 2, \ldots, n\} \to A$，使得：

$$\forall i, j \in \{1, 2, \ldots, n\}: i < j \implies f(i) \leq f(j)$$

### 算法复杂度理论

#### 时间复杂度

- **最好情况**：$T_{best}(n) = \min\{T(n, \sigma) : \sigma \in S_n\}$
- **最坏情况**：$T_{worst}(n) = \max\{T(n, \sigma) : \sigma \in S_n\}$
- **平均情况**：$T_{avg}(n) = \frac{1}{n!}\sum_{\sigma \in S_n} T(n, \sigma)$

#### 空间复杂度

- **原地排序**：$S(n) = O(1)$
- **非原地排序**：$S(n) = O(n)$

## 🔧 Haskell实现

### 基础类型定义

```haskell
{-# LANGUAGE TypeFamilies, FlexibleContexts #-}

-- 可比较类型类
class Ord a => Sortable a where
    type Comparison a :: *
    compare' :: a -> a -> Comparison a

-- 排序结果类型
data SortResult a = SortResult
    { sortedList :: [a]
    , comparisons :: Int
    , swaps :: Int
    , time :: Double
    }

-- 排序算法类型类
class SortingAlgorithm alg where
    type Input alg :: *
    type Output alg :: *
    sort :: alg -> Input alg -> Output alg
    name :: alg -> String
    complexity :: alg -> String
```

### 1. 冒泡排序 (Bubble Sort)

#### 形式化定义

冒泡排序通过重复遍历要排序的数组，比较相邻元素并交换它们的位置来实现排序。

**算法描述**：

1. 比较相邻的元素。如果第一个比第二个大，就交换它们两个。
2. 对每一对相邻元素做同样的工作，从开始第一对到结尾的最后一对。
3. 针对所有的元素重复以上的步骤，除了最后一个。
4. 重复步骤1~3，直到没有任何一对数字需要比较。

#### Haskell实现

```haskell
-- 冒泡排序实现
bubbleSort :: Ord a => [a] -> [a]
bubbleSort xs = bubbleSort' xs (length xs)

bubbleSort' :: Ord a => [a] -> Int -> [a]
bubbleSort' xs 0 = xs
bubbleSort' xs n = bubbleSort' (bubble xs) (n - 1)
  where
    bubble [] = []
    bubble [x] = [x]
    bubble (x:y:xs)
      | x <= y = x : bubble (y:xs)
      | otherwise = y : bubble (x:xs)

-- 带统计的冒泡排序
bubbleSortWithStats :: Ord a => [a] -> SortResult a
bubbleSortWithStats xs = SortResult
    { sortedList = result
    , comparisons = compCount
    , swaps = swapCount
    , time = 0.0  -- 实际实现中需要测量
    }
  where
    (result, compCount, swapCount) = bubbleSortStats xs

bubbleSortStats :: Ord a => [a] -> ([a], Int, Int)
bubbleSortStats xs = bubbleSortStats' xs (length xs) 0 0

bubbleSortStats' :: Ord a => [a] -> Int -> Int -> Int -> ([a], Int, Int)
bubbleSortStats' xs 0 comps swaps = (xs, comps, swaps)
bubbleSortStats' xs n comps swaps = 
    let (newXs, newComps, newSwaps) = bubbleWithStats xs comps swaps
    in bubbleSortStats' newXs (n - 1) newComps newSwaps

bubbleWithStats :: Ord a => [a] -> Int -> Int -> ([a], Int, Int)
bubbleWithStats [] comps swaps = ([], comps, swaps)
bubbleWithStats [x] comps swaps = ([x], comps, swaps)
bubbleWithStats (x:y:xs) comps swaps
  | x <= y = let (rest, comps', swaps') = bubbleWithStats (y:xs) (comps + 1) swaps
             in (x:rest, comps', swaps')
  | otherwise = let (rest, comps', swaps') = bubbleWithStats (x:xs) (comps + 1) (swaps + 1)
                in (y:rest, comps', swaps')

-- 复杂度分析
bubbleSortComplexity :: String
bubbleSortComplexity = 
    "时间复杂度: O(n²)\n" ++
    "空间复杂度: O(1)\n" ++
    "稳定性: 稳定\n" ++
    "原地排序: 是"
```

#### 性能分析

**时间复杂度**：

- 最好情况：$O(n)$ - 数组已经排序
- 最坏情况：$O(n^2)$ - 数组逆序
- 平均情况：$O(n^2)$

**空间复杂度**：$O(1)$

**稳定性**：稳定

### 2. 快速排序 (Quick Sort)

#### 形式化定义

快速排序是一种分治算法，选择一个基准元素，将数组分为两部分，左边都小于基准，右边都大于基准。

**算法描述**：

1. 选择一个基准元素（通常是最后一个元素）
2. 将数组分为两部分：小于基准的元素和大于基准的元素
3. 递归地对两个子数组进行排序
4. 合并结果

#### Haskell实现

```haskell
-- 快速排序实现
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = 
    let smaller = quickSort [a | a <- xs, a <= x]
        larger = quickSort [a | a <- xs, a > x]
    in smaller ++ [x] ++ larger

-- 优化的快速排序（原地排序）
quickSortInPlace :: Ord a => [a] -> [a]
quickSortInPlace xs = 
    let arr = listArray (0, length xs - 1) xs
        sortedArr = quickSortArray arr 0 (length xs - 1)
    in elems sortedArr

quickSortArray :: Ord a => Array Int a -> Int -> Int -> Array Int a
quickSortArray arr low high
  | low < high = 
      let pivotIndex = partition arr low high
          arr1 = quickSortArray arr low (pivotIndex - 1)
          arr2 = quickSortArray arr1 (pivotIndex + 1) high
      in arr2
  | otherwise = arr

partition :: Ord a => Array Int a -> Int -> Int -> Int
partition arr low high = 
    let pivot = arr ! high
        i = low - 1
        (newArr, pivotIndex) = partitionHelper arr low high pivot i
    in pivotIndex

partitionHelper :: Ord a => Array Int a -> Int -> Int -> a -> Int -> (Array Int a, Int)
partitionHelper arr low high pivot i
  | j > high = 
      let finalArr = arr // [(i + 1, pivot), (high, arr ! (i + 1))]
      in (finalArr, i + 1)
  | arr ! j <= pivot = 
      let newI = i + 1
          newArr = arr // [(i + 1, arr ! j), (j, arr ! newI)]
      in partitionHelper newArr low high pivot newI
  | otherwise = partitionHelper arr low high pivot i
  where j = low

-- 带统计的快速排序
quickSortWithStats :: Ord a => [a] -> SortResult a
quickSortWithStats xs = SortResult
    { sortedList = result
    , comparisons = compCount
    , swaps = swapCount
    , time = 0.0
    }
  where
    (result, compCount, swapCount) = quickSortStats xs

quickSortStats :: Ord a => [a] -> ([a], Int, Int)
quickSortStats [] = ([], 0, 0)
quickSortStats (x:xs) = 
    let (smaller, comps1, swaps1) = quickSortStats [a | a <- xs, a <= x]
        (larger, comps2, swaps2) = quickSortStats [a | a <- xs, a > x]
        totalComps = comps1 + comps2 + length xs
        totalSwaps = swaps1 + swaps2
    in (smaller ++ [x] ++ larger, totalComps, totalSwaps)

-- 复杂度分析
quickSortComplexity :: String
quickSortComplexity = 
    "时间复杂度: O(n log n) 平均, O(n²) 最坏\n" ++
    "空间复杂度: O(log n) 平均, O(n) 最坏\n" ++
    "稳定性: 不稳定\n" ++
    "原地排序: 是"
```

#### 性能分析

**时间复杂度**：

- 最好情况：$O(n \log n)$
- 最坏情况：$O(n^2)$ - 已排序或逆序数组
- 平均情况：$O(n \log n)$

**空间复杂度**：

- 平均：$O(\log n)$
- 最坏：$O(n)$

**稳定性**：不稳定

### 3. 归并排序 (Merge Sort)

#### 形式化定义

归并排序是一种分治算法，将数组分成两半，递归排序，然后合并。

**算法描述**：

1. 将数组分成两半
2. 递归地对两半进行排序
3. 合并两个已排序的子数组

#### Haskell实现

```haskell
-- 归并排序实现
mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
        sortedLeft = mergeSort left
        sortedRight = mergeSort right
    in merge sortedLeft sortedRight

-- 合并两个已排序的列表
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 优化的归并排序（原地排序）
mergeSortInPlace :: Ord a => [a] -> [a]
mergeSortInPlace xs = 
    let arr = listArray (0, length xs - 1) xs
        sortedArr = mergeSortArray arr 0 (length xs - 1)
    in elems sortedArr

mergeSortArray :: Ord a => Array Int a -> Int -> Int -> Array Int a
mergeSortArray arr low high
  | low < high = 
      let mid = (low + high) `div` 2
          arr1 = mergeSortArray arr low mid
          arr2 = mergeSortArray arr1 (mid + 1) high
          arr3 = mergeArrays arr2 low mid high
      in arr3
  | otherwise = arr

mergeArrays :: Ord a => Array Int a -> Int -> Int -> Int -> Array Int a
mergeArrays arr low mid high = 
    let left = [arr ! i | i <- [low..mid]]
        right = [arr ! i | i <- [mid+1..high]]
        merged = merge left right
        indices = [low..high]
    in arr // zip indices merged

-- 带统计的归并排序
mergeSortWithStats :: Ord a => [a] -> SortResult a
mergeSortWithStats xs = SortResult
    { sortedList = result
    , comparisons = compCount
    , swaps = swapCount
    , time = 0.0
    }
  where
    (result, compCount, swapCount) = mergeSortStats xs

mergeSortStats :: Ord a => [a] -> ([a], Int, Int)
mergeSortStats [] = ([], 0, 0)
mergeSortStats [x] = ([x], 0, 0)
mergeSortStats xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
        (sortedLeft, comps1, swaps1) = mergeSortStats left
        (sortedRight, comps2, swaps2) = mergeSortStats right
        (merged, mergeComps, mergeSwaps) = mergeWithStats sortedLeft sortedRight
    in (merged, comps1 + comps2 + mergeComps, swaps1 + swaps2 + mergeSwaps)

mergeWithStats :: Ord a => [a] -> [a] -> ([a], Int, Int)
mergeWithStats [] ys = (ys, 0, 0)
mergeWithStats xs [] = (xs, 0, 0)
mergeWithStats (x:xs) (y:ys)
  | x <= y = let (rest, comps, swaps) = mergeWithStats xs (y:ys)
             in (x:rest, comps + 1, swaps)
  | otherwise = let (rest, comps, swaps) = mergeWithStats (x:xs) ys
                in (y:rest, comps + 1, swaps)

-- 复杂度分析
mergeSortComplexity :: String
mergeSortComplexity = 
    "时间复杂度: O(n log n)\n" ++
    "空间复杂度: O(n)\n" ++
    "稳定性: 稳定\n" ++
    "原地排序: 否"
```

#### 性能分析

**时间复杂度**：$O(n \log n)$（所有情况）

**空间复杂度**：$O(n)$

**稳定性**：稳定

### 4. 堆排序 (Heap Sort)

#### 形式化定义

堆排序利用堆这种数据结构所设计的排序算法。堆是一个近似完全二叉树的结构。

**算法描述**：

1. 建立最大堆
2. 重复从堆中取出最大元素并放到数组末尾
3. 调整堆结构

#### Haskell实现

```haskell
-- 堆排序实现
heapSort :: Ord a => [a] -> [a]
heapSort xs = 
    let heap = buildMaxHeap xs
        sorted = heapSort' heap (length xs)
    in sorted

buildMaxHeap :: Ord a => [a] -> [a]
buildMaxHeap xs = 
    let n = length xs
        indices = [n `div` 2 - 1, n `div` 2 - 2 .. 0]
    in foldl heapify xs indices

heapify :: Ord a => [a] -> Int -> [a]
heapify xs i = 
    let n = length xs
        largest = heapify' xs i n
    in if largest /= i 
       then heapify (swap xs i largest) largest
       else xs

heapify' :: Ord a => [a] -> Int -> Int -> Int
heapify' xs i n = 
    let left = 2 * i + 1
        right = 2 * i + 2
        largest = if left < n && xs !! left > xs !! i then left else i
        largest' = if right < n && xs !! right > xs !! largest then right else largest
    in largest'

swap :: [a] -> Int -> Int -> [a]
swap xs i j = 
    let xi = xs !! i
        xj = xs !! j
    in take i xs ++ [xj] ++ drop (i + 1) (take j xs) ++ [xi] ++ drop (j + 1) xs

heapSort' :: Ord a => [a] -> Int -> [a]
heapSort' xs 0 = []
heapSort' xs n = 
    let xs' = swap xs 0 (n - 1)
        heapified = heapify (take (n - 1) xs') 0
        rest = heapSort' heapified (n - 1)
    in [xs' !! (n - 1)] ++ rest

-- 复杂度分析
heapSortComplexity :: String
heapSortComplexity = 
    "时间复杂度: O(n log n)\n" ++
    "空间复杂度: O(1)\n" ++
    "稳定性: 不稳定\n" ++
    "原地排序: 是"
```

#### 性能分析

**时间复杂度**：$O(n \log n)$（所有情况）

**空间复杂度**：$O(1)$

**稳定性**：不稳定

## 📊 算法比较

### 性能对比表

| 算法 | 最好情况 | 平均情况 | 最坏情况 | 空间复杂度 | 稳定性 | 原地排序 |
|------|----------|----------|----------|------------|--------|----------|
| 冒泡排序 | O(n) | O(n²) | O(n²) | O(1) | 稳定 | 是 |
| 快速排序 | O(n log n) | O(n log n) | O(n²) | O(log n) | 不稳定 | 是 |
| 归并排序 | O(n log n) | O(n log n) | O(n log n) | O(n) | 稳定 | 否 |
| 堆排序 | O(n log n) | O(n log n) | O(n log n) | O(1) | 不稳定 | 是 |

### 选择指南

```haskell
-- 算法选择函数
chooseSortingAlgorithm :: Ord a => [a] -> String -> [a]
chooseSortingAlgorithm xs "bubble" = bubbleSort xs
chooseSortingAlgorithm xs "quick" = quickSort xs
chooseSortingAlgorithm xs "merge" = mergeSort xs
chooseSortingAlgorithm xs "heap" = heapSort xs
chooseSortingAlgorithm xs _ = quickSort xs  -- 默认使用快速排序

-- 智能算法选择
smartSort :: Ord a => [a] -> [a]
smartSort xs
  | length xs <= 10 = bubbleSort xs  -- 小数组使用冒泡排序
  | length xs <= 100 = quickSort xs  -- 中等数组使用快速排序
  | otherwise = mergeSort xs         -- 大数组使用归并排序
```

## 🔬 形式化验证

### 正确性证明

#### 冒泡排序正确性

**定理**：冒泡排序算法能够正确排序任何有限列表。

**证明**：

1. **基础情况**：空列表和单元素列表显然正确
2. **归纳假设**：假设对长度为 $n-1$ 的列表正确
3. **归纳步骤**：经过一次冒泡操作，最大元素到达正确位置，剩余 $n-1$ 个元素通过归纳假设正确排序

#### 快速排序正确性

**定理**：快速排序算法能够正确排序任何有限列表。

**证明**：

1. **基础情况**：空列表和单元素列表显然正确
2. **归纳假设**：假设对长度小于 $n$ 的列表正确
3. **归纳步骤**：分区操作确保基准元素在正确位置，两个子列表通过归纳假设正确排序

### 复杂度证明

#### 归并排序复杂度

**定理**：归并排序的时间复杂度为 $O(n \log n)$。

**证明**：
设 $T(n)$ 为归并排序的时间复杂度，则：
$$T(n) = 2T(n/2) + O(n)$$

根据主定理，$a = 2, b = 2, f(n) = O(n)$，且 $f(n) = O(n^{\log_b a}) = O(n)$，因此：
$$T(n) = O(n \log n)$$

## 🎯 实际应用

### 性能测试

```haskell
-- 性能测试函数
testSortingPerformance :: [Int] -> IO ()
testSortingPerformance testData = do
    putStrLn "排序算法性能测试"
    putStrLn "=================="
    
    let testSort name sortFunc = do
            start <- getCurrentTime
            let result = sortFunc testData
            end <- getCurrentTime
            let duration = diffUTCTime end start
            putStrLn $ name ++ ": " ++ show duration
    
    testSort "冒泡排序" bubbleSort
    testSort "快速排序" quickSort
    testSort "归并排序" mergeSort
    testSort "堆排序" heapSort

-- 生成测试数据
generateTestData :: Int -> IO [Int]
generateTestData n = do
    gen <- newStdGen
    return $ take n $ randomRs (1, 1000) gen :: [Int]
```

### 实际应用场景

1. **数据库排序**：SQL ORDER BY 子句的实现
2. **文件系统**：文件和目录的排序显示
3. **数据分析**：统计数据的排序分析
4. **游戏开发**：排行榜和分数排序
5. **图形渲染**：深度排序和Z-buffer

## 📚 扩展阅读

### 高级排序算法

1. **基数排序**：适用于整数和字符串
2. **计数排序**：适用于小范围整数
3. **桶排序**：适用于均匀分布的数据
4. **希尔排序**：插入排序的改进版本
5. **Tim排序**：Python和Java的默认排序算法

### 并行排序

```haskell
-- 并行归并排序
parallelMergeSort :: Ord a => [a] -> [a]
parallelMergeSort xs
  | length xs <= 1000 = mergeSort xs  -- 小数组使用串行排序
  | otherwise = 
      let (left, right) = splitAt (length xs `div` 2) xs
          (sortedLeft, sortedRight) = 
              runEval $ do
                  leftVar <- rpar (parallelMergeSort left)
                  rightVar <- rpar (parallelMergeSort right)
                  leftResult <- rseq leftVar
                  rightResult <- rseq rightVar
                  return (leftResult, rightResult)
      in merge sortedLeft sortedRight
```

## 🔗 相关链接

- [基础数据结构](../01-Haskell-Basics/01-Language-Features.md)
- [高级数据结构](../03-Data-Structures/01-Advanced-Data-Structures.md)
- [形式化证明](../04-Formal-Proofs/01-Theorem-Proving.md)
- [性能优化](../05-Performance-Optimization/01-Memory-Optimization.md)

---

*本文档提供了排序算法的完整形式化理论和Haskell实现，包括性能分析和实际应用指导。*
