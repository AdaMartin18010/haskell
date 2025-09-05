# Haskell排序算法

## 📚 快速导航

### 相关理论

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [数据结构基础](../06-Data-Structures/001-Basic-Data-Structures.md)

### 实现示例

- [搜索算法](./002-Search-Algorithms.md)
- [图算法](./003-Graph-Algorithms.md)
- [动态规划](./004-Dynamic-Programming.md)

### 应用领域

- [性能优化](../09-Performance/001-Performance-Analysis.md)
- [科学计算](../09-Scientific-Computing/001-Numerical-Computation.md)
- [系统编程](../12-System-Programming/001-System-Programming-Foundation.md)

## 🎯 概述

排序算法是计算机科学的基础，在Haskell中，排序算法的实现充分利用了函数式编程的特性。本文档介绍各种排序算法的Haskell实现，包括基本排序、高级排序以及性能分析。

## 📖 1. 基本排序算法

### 1.1 冒泡排序

**定义 1.1 (冒泡排序)**
冒泡排序通过重复遍历列表，比较相邻元素并交换它们的位置。

**算法复杂度：**

- 时间复杂度：$O(n^2)$
- 空间复杂度：$O(1)$

**Haskell实现：**

```haskell
-- 冒泡排序
bubbleSort :: Ord a => [a] -> [a]
bubbleSort [] = []
bubbleSort xs = bubbleSortHelper xs (length xs)
  where
    bubbleSortHelper xs 0 = xs
    bubbleSortHelper xs n = bubbleSortHelper (bubblePass xs) (n - 1)
    
    bubblePass [] = []
    bubblePass [x] = [x]
    bubblePass (x:y:xs)
      | x > y = y : bubblePass (x:xs)
      | otherwise = x : bubblePass (y:xs)

-- 冒泡排序示例
bubbleSortExample :: IO ()
bubbleSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = bubbleSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Bubble sorted: " ++ show sorted
  putStrLn "Bubble sort complexity: O(n²)"
```

### 1.2 选择排序

**定义 1.2 (选择排序)**
选择排序通过找到最小元素并将其放在正确位置来排序。

**算法复杂度：**

- 时间复杂度：$O(n^2)$
- 空间复杂度：$O(1)$

**Haskell实现：**

```haskell
-- 选择排序
selectionSort :: Ord a => [a] -> [a]
selectionSort [] = []
selectionSort xs = 
  let minElement = minimum xs
      rest = filter (/= minElement) xs
  in minElement : selectionSort rest

-- 更高效的选择排序实现
selectionSortEfficient :: Ord a => [a] -> [a]
selectionSortEfficient [] = []
selectionSortEfficient xs = 
  let (min, rest) = findMin xs
  in min : selectionSortEfficient rest
  where
    findMin [x] = (x, [])
    findMin (x:xs) = 
      let (min, rest) = findMin xs
      in if x <= min 
         then (x, min:rest)
         else (min, x:rest)

-- 选择排序示例
selectionSortExample :: IO ()
selectionSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = selectionSortEfficient numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Selection sorted: " ++ show sorted
  putStrLn "Selection sort complexity: O(n²)"
```

### 1.3 插入排序

**定义 1.3 (插入排序)**
插入排序通过构建有序序列，对于未排序数据，在已排序序列中从后向前扫描，找到相应位置并插入。

**算法复杂度：**

- 时间复杂度：$O(n^2)$
- 空间复杂度：$O(1)$

**Haskell实现：**

```haskell
-- 插入排序
insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []
  where
    insert x [] = [x]
    insert x (y:ys)
      | x <= y = x : y : ys
      | otherwise = y : insert x ys

-- 插入排序示例
insertionSortExample :: IO ()
insertionSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = insertionSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Insertion sorted: " ++ show sorted
  putStrLn "Insertion sort complexity: O(n²)"
```

## 🔧 2. 高级排序算法

### 2.1 快速排序

**定义 2.1 (快速排序)**
快速排序使用分治策略，选择一个基准元素，将数组分为两部分，递归排序。

**算法复杂度：**

- 平均时间复杂度：$O(n \log n)$
- 最坏时间复杂度：$O(n^2)$
- 空间复杂度：$O(\log n)$

**Haskell实现：**

```haskell
-- 快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  quicksort [y | y <- xs, y <= x] ++ 
  [x] ++ 
  quicksort [y | y <- xs, y > x]

-- 优化的快速排序
quicksortOptimized :: Ord a => [a] -> [a]
quicksortOptimized [] = []
quicksortOptimized [x] = [x]
quicksortOptimized xs = 
  let pivot = head xs
      (smaller, larger) = partition (< pivot) (tail xs)
  in quicksortOptimized smaller ++ [pivot] ++ quicksortOptimized larger

-- 快速排序示例
quicksortExample :: IO ()
quicksortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = quicksort numbers
      sortedOpt = quicksortOptimized numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Quicksort: " ++ show sorted
  putStrLn $ "Optimized quicksort: " ++ show sortedOpt
  putStrLn "Quicksort complexity: O(n log n) average"
```

### 2.2 归并排序

**定义 2.2 (归并排序)**
归并排序使用分治策略，将数组分成两半，递归排序，然后合并。

**算法复杂度：**

- 时间复杂度：$O(n \log n)$
- 空间复杂度：$O(n)$

**Haskell实现：**

```haskell
-- 归并排序
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergesort left) (mergesort right)

-- 合并函数
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 归并排序示例
mergesortExample :: IO ()
mergesortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = mergesort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Mergesort: " ++ show sorted
  putStrLn "Mergesort complexity: O(n log n)"
```

### 2.3 堆排序

**定义 2.3 (堆排序)**
堆排序使用堆数据结构进行排序，首先构建最大堆，然后逐个提取最大元素。

**算法复杂度：**

- 时间复杂度：$O(n \log n)$
- 空间复杂度：$O(1)$

**Haskell实现：**

```haskell
-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = heapSortHelper (buildHeap xs)
  where
    buildHeap = foldr heapInsert []
    
    heapInsert x [] = [x]
    heapInsert x (y:ys)
      | x > y = x : y : ys
      | otherwise = y : heapInsert x ys
    
    heapSortHelper [] = []
    heapSortHelper heap = 
      let (max, rest) = extractMax heap
      in max : heapSortHelper rest
    
    extractMax [x] = (x, [])
    extractMax (x:xs) = 
      let (max, rest) = extractMax xs
      in if x > max 
         then (x, max:rest)
         else (max, x:rest)

-- 堆排序示例
heapSortExample :: IO ()
heapSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = heapSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Heap sort: " ++ show sorted
  putStrLn "Heap sort complexity: O(n log n)"
```

## 💾 3. 特殊排序算法

### 3.1 计数排序

**定义 3.1 (计数排序)**
计数排序适用于已知范围的整数排序，通过计数每个元素出现的次数来排序。

**算法复杂度：**

- 时间复杂度：$O(n + k)$，其中k是范围大小
- 空间复杂度：$O(k)$

**Haskell实现：**

```haskell
-- 计数排序
countingSort :: [Int] -> [Int]
countingSort [] = []
countingSort xs = 
  let minVal = minimum xs
      maxVal = maximum xs
      range = maxVal - minVal + 1
      counts = replicate range 0
      updatedCounts = foldr (\x acc -> 
                              let index = x - minVal
                              in take index acc ++ [acc !! index + 1] ++ drop (index + 1) acc) 
                            counts xs
      sorted = concatMap (\(count, val) -> replicate count val) 
                        (zip updatedCounts [minVal..maxVal])
  in sorted

-- 计数排序示例
countingSortExample :: IO ()
countingSortExample = do
  let numbers = [4, 2, 1, 4, 1, 2, 3, 1]
      sorted = countingSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Counting sort: " ++ show sorted
  putStrLn "Counting sort complexity: O(n + k)"
```

### 3.2 基数排序

**定义 3.2 (基数排序)**
基数排序按照数字的每一位进行排序，从最低位到最高位。

**算法复杂度：**

- 时间复杂度：$O(d(n + k))$，其中d是位数，k是基数
- 空间复杂度：$O(n + k)$

**Haskell实现：**

```haskell
-- 基数排序
radixSort :: [Int] -> [Int]
radixSort [] = []
radixSort xs = 
  let maxDigits = maximum (map (length . show) xs)
  in foldr (\digit sorted -> sortByDigit digit sorted) xs [0..maxDigits-1]

-- 按位排序
sortByDigit :: Int -> [Int] -> [Int]
sortByDigit _ [] = []
sortByDigit digit xs = 
  let buckets = replicate 10 []
      updatedBuckets = foldr (\x acc -> 
                                let d = getDigit x digit
                                in take d acc ++ [x : (acc !! d)] ++ drop (d + 1) acc) 
                              buckets xs
  in concat updatedBuckets

-- 获取指定位的数字
getDigit :: Int -> Int -> Int
getDigit x digit = (x `div` (10 ^ digit)) `mod` 10

-- 基数排序示例
radixSortExample :: IO ()
radixSortExample = do
  let numbers = [170, 45, 75, 90, 802, 24, 2, 66]
      sorted = radixSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Radix sort: " ++ show sorted
  putStrLn "Radix sort complexity: O(d(n + k))"
```

### 3.3 桶排序

**定义 3.3 (桶排序)**
桶排序将数据分到有限数量的桶中，每个桶再单独进行排序。

**算法复杂度：**

- 平均时间复杂度：$O(n + k)$
- 最坏时间复杂度：$O(n^2)$
- 空间复杂度：$O(n + k)$

**Haskell实现：**

```haskell
-- 桶排序
bucketSort :: [Double] -> [Double]
bucketSort [] = []
bucketSort xs = 
  let n = length xs
      buckets = replicate n []
      minVal = minimum xs
      maxVal = maximum xs
      range = maxVal - minVal
      updatedBuckets = foldr (\x acc -> 
                                let index = min (n - 1) (floor ((x - minVal) / range * fromIntegral n))
                                in take index acc ++ [x : (acc !! index)] ++ drop (index + 1) acc) 
                              buckets xs
      sortedBuckets = map insertionSort updatedBuckets
  in concat sortedBuckets

-- 桶排序示例
bucketSortExample :: IO ()
bucketSortExample = do
  let numbers = [0.897, 0.565, 0.656, 0.1234, 0.665, 0.3434]
      sorted = bucketSort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Bucket sort: " ++ show sorted
  putStrLn "Bucket sort complexity: O(n + k) average"
```

## 🎭 4. 函数式排序算法

### 4.1 函数式快速排序

**定义 4.1 (函数式快速排序)**
利用Haskell的函数式特性实现的快速排序。

**Haskell实现：**

```haskell
-- 函数式快速排序
functionalQuicksort :: Ord a => [a] -> [a]
functionalQuicksort [] = []
functionalQuicksort (x:xs) = 
  let smaller = filter (<= x) xs
      larger = filter (> x) xs
  in functionalQuicksort smaller ++ [x] ++ functionalQuicksort larger

-- 使用列表推导式的快速排序
quicksortComprehension :: Ord a => [a] -> [a]
quicksortComprehension [] = []
quicksortComprehension (x:xs) = 
  quicksortComprehension [y | y <- xs, y <= x] ++ 
  [x] ++ 
  quicksortComprehension [y | y <- xs, y > x]

-- 函数式快速排序示例
functionalQuicksortExample :: IO ()
functionalQuicksortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted1 = functionalQuicksort numbers
      sorted2 = quicksortComprehension numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Functional quicksort: " ++ show sorted1
  putStrLn $ "Comprehension quicksort: " ++ show sorted2
```

### 4.2 惰性排序

**定义 4.2 (惰性排序)**
利用Haskell的惰性求值特性实现的排序算法。

**Haskell实现：**

```haskell
-- 惰性归并排序
lazyMergesort :: Ord a => [a] -> [a]
lazyMergesort [] = []
lazyMergesort [x] = [x]
lazyMergesort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in lazyMerge (lazyMergesort left) (lazyMergesort right)

-- 惰性合并
lazyMerge :: Ord a => [a] -> [a] -> [a]
lazyMerge [] ys = ys
lazyMerge xs [] = xs
lazyMerge (x:xs) (y:ys)
  | x <= y = x : lazyMerge xs (y:ys)
  | otherwise = y : lazyMerge (x:xs) ys

-- 惰性排序示例
lazySortExample :: IO ()
lazySortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90]
      sorted = lazyMergesort numbers
      firstFive = take 5 sorted
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Lazy mergesort: " ++ show sorted
  putStrLn $ "First 5 elements: " ++ show firstFive
  putStrLn "Only necessary elements are computed!"
```

## ⚡ 5. 排序算法比较

### 5.1 性能比较

**定义 5.1 (性能比较)**
比较不同排序算法的性能特征。

**Haskell实现：**

```haskell
-- 性能比较函数
performanceComparison :: IO ()
performanceComparison = do
  let smallList = [3, 1, 4, 1, 5, 9, 2, 6]
      largeList = [1..1000]
      
      -- 测试不同排序算法
      bubbleResult = bubbleSort smallList
      selectionResult = selectionSortEfficient smallList
      insertionResult = insertionSort smallList
      quickResult = quicksort smallList
      mergeResult = mergesort smallList
      heapResult = heapSort smallList
  putStrLn "Sorting Algorithm Performance Comparison:"
  putStrLn $ "Bubble sort: " ++ show bubbleResult
  putStrLn $ "Selection sort: " ++ show selectionResult
  putStrLn $ "Insertion sort: " ++ show insertionResult
  putStrLn $ "Quicksort: " ++ show quickResult
  putStrLn $ "Mergesort: " ++ show mergeResult
  putStrLn $ "Heap sort: " ++ show heapResult
  putStrLn "\nTime Complexity:"
  putStrLn "Bubble/Selection/Insertion: O(n²)"
  putStrLn "Quicksort/Mergesort/Heap: O(n log n)"
```

### 5.2 稳定性比较

**定义 5.2 (稳定性)**
排序算法的稳定性是指相等元素的相对位置是否保持不变。

**Haskell实现：**

```haskell
-- 稳定性测试
stabilityTest :: IO ()
stabilityTest = do
  let pairs = [(1, 'a'), (2, 'b'), (1, 'c'), (3, 'd')]
      
      -- 稳定排序
      stableSorted = mergesort pairs
      
      -- 不稳定排序
      unstableSorted = quicksort pairs
  putStrLn "Stability Test:"
  putStrLn $ "Original: " ++ show pairs
  putStrLn $ "Stable (mergesort): " ++ show stableSorted
  putStrLn $ "Unstable (quicksort): " ++ show unstableSorted
  putStrLn "Stable algorithms preserve relative order of equal elements"
```

## 🔄 6. 并行排序算法

### 6.1 并行归并排序

**定义 6.1 (并行归并排序)**
利用并行计算加速归并排序。

**Haskell实现：**

```haskell
-- 并行归并排序（概念实现）
parallelMergesort :: Ord a => [a] -> [a]
parallelMergesort [] = []
parallelMergesort [x] = [x]
parallelMergesort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
      -- 在实际实现中，这里会并行执行
      sortedLeft = parallelMergesort left
      sortedRight = parallelMergesort right
  in merge sortedLeft sortedRight

-- 并行排序示例
parallelSortExample :: IO ()
parallelSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90, 45, 67, 89, 23, 56, 78, 90, 12, 34]
      sorted = parallelMergesort numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Parallel mergesort: " ++ show sorted
  putStrLn "Parallel sorting can improve performance on multi-core systems"
```

### 6.2 分块排序

**定义 6.2 (分块排序)**
将数据分成块，并行排序每个块，然后合并。

**Haskell实现：**

```haskell
-- 分块排序
chunkSort :: Ord a => Int -> [a] -> [a]
chunkSort chunkSize xs = 
  let chunks = splitIntoChunks chunkSize xs
      sortedChunks = map mergesort chunks
  in mergeAll sortedChunks

-- 分块函数
splitIntoChunks :: Int -> [a] -> [[a]]
splitIntoChunks _ [] = []
splitIntoChunks n xs = 
  let (chunk, rest) = splitAt n xs
  in chunk : splitIntoChunks n rest

-- 合并所有块
mergeAll :: Ord a => [[a]] -> [a]
mergeAll [] = []
mergeAll [xs] = xs
mergeAll (xs:ys:rest) = mergeAll (merge xs ys : rest)

-- 分块排序示例
chunkSortExample :: IO ()
chunkSortExample = do
  let numbers = [64, 34, 25, 12, 22, 11, 90, 45, 67, 89, 23, 56, 78, 90, 12, 34]
      sorted = chunkSort 4 numbers
  putStrLn $ "Original: " ++ show numbers
  putStrLn $ "Chunk sort: " ++ show sorted
  putStrLn "Chunk sorting enables parallel processing"
```

## 🛠️ 7. 排序算法的实际应用

### 7.1 数据库排序

**定义 7.1 (数据库排序)**
排序算法在数据库查询中的应用。

**Haskell实现：**

```haskell
-- 数据库记录类型
data Record = Record {
  id :: Int,
  name :: String,
  age :: Int,
  salary :: Double
} deriving (Show, Eq)

-- 数据库排序
sortByField :: (Record -> a) -> Ord a => [Record] -> [Record]
sortByField field = mergesort . map (\r -> (field r, r)) . map snd

-- 数据库排序示例
databaseSortExample :: IO ()
databaseSortExample = do
  let records = [
        Record 1 "Alice" 25 50000.0,
        Record 2 "Bob" 30 60000.0,
        Record 3 "Charlie" 22 45000.0,
        Record 4 "Diana" 35 70000.0
      ]
      
      sortedByName = sortByField name records
      sortedByAge = sortByField age records
      sortedBySalary = sortByField salary records
  putStrLn "Database Sorting Example:"
  putStrLn $ "Sorted by name: " ++ show sortedByName
  putStrLn $ "Sorted by age: " ++ show sortedByAge
  putStrLn $ "Sorted by salary: " ++ show sortedBySalary
```

### 7.2 文件排序

**定义 7.2 (文件排序)**
排序算法在处理大文件时的应用。

**Haskell实现：**

```haskell
-- 文件排序（概念实现）
fileSort :: [String] -> [String]
fileSort = mergesort

-- 外部排序（处理大文件）
externalSort :: [String] -> [String]
externalSort xs = 
  let chunkSize = 1000  -- 内存中能处理的最大块大小
      chunks = splitIntoChunks chunkSize xs
      sortedChunks = map fileSort chunks
  in mergeAll sortedChunks

-- 文件排序示例
fileSortExample :: IO ()
fileSortExample = do
  let lines = [
        "zebra",
        "apple",
        "banana",
        "cherry",
        "date",
        "elderberry"
      ]
      
      sortedLines = fileSort lines
      externalSortedLines = externalSort lines
  putStrLn "File Sorting Example:"
  putStrLn $ "Original lines: " ++ show lines
  putStrLn $ "Sorted lines: " ++ show sortedLines
  putStrLn $ "External sorted lines: " ++ show externalSortedLines
```

## 📊 8. 排序算法的优化

### 8.1 混合排序

**定义 8.1 (混合排序)**
结合多种排序算法的优点。

**Haskell实现：**

```haskell
-- 混合排序（插入排序 + 快速排序）
hybridSort :: Ord a => [a] -> [a]
hybridSort xs
  | length xs <= 10 = insertionSort xs  -- 小数组使用插入排序
  | otherwise = quicksort xs            -- 大数组使用快速排序

-- 混合排序示例
hybridSortExample :: IO ()
hybridSortExample = do
  let smallList = [3, 1, 4, 1, 5]
      largeList = [64, 34, 25, 12, 22, 11, 90, 45, 67, 89, 23, 56, 78, 90, 12, 34]
      
      smallSorted = hybridSort smallList
      largeSorted = hybridSort largeList
  putStrLn "Hybrid Sorting Example:"
  putStrLn $ "Small list: " ++ show smallList
  putStrLn $ "Small sorted: " ++ show smallSorted
  putStrLn $ "Large list: " ++ show largeList
  putStrLn $ "Large sorted: " ++ show largeSorted
```

### 8.2 自适应排序

**定义 8.2 (自适应排序)**
根据数据特征自动选择最优排序算法。

**Haskell实现：**

```haskell
-- 自适应排序
adaptiveSort :: Ord a => [a] -> [a]
adaptiveSort xs
  | isNearlySorted xs = insertionSort xs
  | length xs <= 50 = insertionSort xs
  | otherwise = quicksort xs

-- 检查是否接近有序
isNearlySorted :: Ord a => [a] -> Bool
isNearlySorted [] = True
isNearlySorted [_] = True
isNearlySorted (x:y:xs) = 
  x <= y && isNearlySorted (y:xs)

-- 自适应排序示例
adaptiveSortExample :: IO ()
adaptiveSortExample = do
  let nearlySorted = [1, 2, 3, 5, 4, 6, 7, 8]
      randomList = [64, 34, 25, 12, 22, 11, 90]
      
      nearlySortedResult = adaptiveSort nearlySorted
      randomResult = adaptiveSort randomList
  putStrLn "Adaptive Sorting Example:"
  putStrLn $ "Nearly sorted: " ++ show nearlySorted
  putStrLn $ "Adaptive sorted: " ++ show nearlySortedResult
  putStrLn $ "Random list: " ++ show randomList
  putStrLn $ "Adaptive sorted: " ++ show randomResult
```

## 🔗 9. 排序算法的理论分析

### 9.1 下界分析

**定理 9.1 (比较排序下界)**
任何基于比较的排序算法的最坏时间复杂度为 $\Omega(n \log n)$。

**证明：**

1. 比较树的高度至少为 $\log_2(n!)$
2. 根据斯特林公式，$n! \approx n^n e^{-n} \sqrt{2\pi n}$
3. 因此 $\log_2(n!) \approx n \log_2 n - n \log_2 e + \frac{1}{2} \log_2(2\pi n)$
4. 对于大n，主要项是 $n \log_2 n$

### 9.2 最优排序

**定义 9.2 (最优排序)**
在特定条件下达到理论下界的排序算法。

**Haskell实现：**

```haskell
-- 最优排序分析
optimalSortAnalysis :: IO ()
optimalSortAnalysis = do
  putStrLn "Optimal Sorting Analysis:"
  putStrLn "1. Comparison-based sorting: Ω(n log n)"
  putStrLn "2. Non-comparison sorting: O(n + k)"
  putStrLn "3. Parallel sorting: O(log n) with O(n) processors"
  putStrLn "4. External sorting: O(n log n) I/O operations"
```

## 📚 10. 总结与展望

### 10.1 排序算法的核心概念

1. **比较排序**：基于元素比较的排序
2. **非比较排序**：基于元素特征的排序
3. **稳定性**：相等元素相对位置保持不变
4. **适应性**：根据数据特征选择算法

### 10.2 排序算法的选择指南

1. **小数据集**：插入排序
2. **大数据集**：快速排序、归并排序
3. **稳定排序**：归并排序
4. **内存受限**：堆排序
5. **整数排序**：计数排序、基数排序

### 10.3 未来发展方向

1. **并行排序**：多核处理器优化
2. **外部排序**：大数据处理
3. **自适应排序**：智能算法选择
4. **量子排序**：量子计算排序算法

---

**相关文档**：

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [数据结构基础](../06-Data-Structures/001-Basic-Data-Structures.md)
- [搜索算法](./002-Search-Algorithms.md)

**实现示例**：

- [图算法](./003-Graph-Algorithms.md)
- [动态规划](./004-Dynamic-Programming.md)
- [性能优化](../09-Performance/001-Performance-Analysis.md)
