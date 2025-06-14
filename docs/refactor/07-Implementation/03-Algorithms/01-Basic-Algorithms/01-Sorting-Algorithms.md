# 排序算法 (Sorting Algorithms)

## 1. 概述

排序算法是计算机科学中最基础和重要的算法之一。本文档介绍各种经典排序算法在Haskell中的实现，包括算法原理、复杂度分析和形式化证明。

## 2. 算法分类

### 2.1 比较排序算法
- 冒泡排序 (Bubble Sort)
- 选择排序 (Selection Sort)
- 插入排序 (Insertion Sort)
- 归并排序 (Merge Sort)
- 快速排序 (Quick Sort)
- 堆排序 (Heap Sort)

### 2.2 非比较排序算法
- 计数排序 (Counting Sort)
- 基数排序 (Radix Sort)
- 桶排序 (Bucket Sort)

## 3. 基础排序算法

### 3.1 冒泡排序

#### 算法描述
冒泡排序通过重复遍历要排序的数组，比较相邻元素并交换它们的位置，使较大的元素"冒泡"到数组的末尾。

#### Haskell实现

```haskell
-- 冒泡排序
bubbleSort :: Ord a => [a] -> [a]
bubbleSort [] = []
bubbleSort xs = bubbleSort' xs (length xs)
  where
    bubbleSort' xs 0 = xs
    bubbleSort' xs n = bubbleSort' (bubble xs) (n - 1)
    
    bubble :: Ord a => [a] -> [a]
    bubble [] = []
    bubble [x] = [x]
    bubble (x:y:xs)
      | x > y = y : bubble (x:xs)
      | otherwise = x : bubble (y:xs)

-- 优化的冒泡排序
bubbleSortOptimized :: Ord a => [a] -> [a]
bubbleSortOptimized xs = bubbleSortOpt xs False
  where
    bubbleSortOpt xs False = xs
    bubbleSortOpt xs True = bubbleSortOpt (bubble xs) False
    
    bubble :: Ord a => [a] -> (Bool, [a])
    bubble [] = (False, [])
    bubble [x] = (False, [x])
    bubble (x:y:xs) = 
      let (swapped, rest) = bubble (y:xs)
      in if x > y 
         then (True, y : rest)
         else (swapped, x : rest)
```

#### 复杂度分析
- **时间复杂度**: O(n²) 最坏和平均情况
- **空间复杂度**: O(1)
- **稳定性**: 稳定

#### 形式化证明

**定理 3.1**: 冒泡排序算法正确性

**证明**: 通过数学归纳法证明
1. **基础情况**: 空列表和单元素列表已排序
2. **归纳假设**: 假设对长度为k的列表，算法正确排序
3. **归纳步骤**: 对于长度为k+1的列表，一次冒泡操作将最大元素移到末尾，剩余k个元素通过归纳假设正确排序

### 3.2 选择排序

#### 算法描述
选择排序每次从未排序部分选择最小元素，放到已排序部分的末尾。

#### Haskell实现

```haskell
-- 选择排序
selectionSort :: Ord a => [a] -> [a]
selectionSort [] = []
selectionSort xs = 
    let min = minimum xs
        rest = delete min xs
    in min : selectionSort rest

-- 更高效的选择排序实现
selectionSort' :: Ord a => [a] -> [a]
selectionSort' [] = []
selectionSort' xs = 
    let (min, rest) = selectMin xs
    in min : selectionSort' rest
  where
    selectMin :: Ord a => [a] -> (a, [a])
    selectMin [x] = (x, [])
    selectMin (x:xs) = 
        let (min, rest) = selectMin xs
        in if x <= min 
           then (x, min:rest)
           else (min, x:rest)

-- 使用foldr的选择排序
selectionSortFold :: Ord a => [a] -> [a]
selectionSortFold = foldr insert []
  where
    insert x [] = [x]
    insert x (y:ys) = 
        if x <= y 
        then x:y:ys 
        else y:insert x ys
```

#### 复杂度分析
- **时间复杂度**: O(n²) 所有情况
- **空间复杂度**: O(1)
- **稳定性**: 不稳定

### 3.3 插入排序

#### 算法描述
插入排序将数组分为已排序和未排序两部分，每次从未排序部分取出一个元素，插入到已排序部分的正确位置。

#### Haskell实现

```haskell
-- 插入排序
insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []
  where
    insert x [] = [x]
    insert x (y:ys) = 
        if x <= y 
        then x:y:ys 
        else y:insert x ys

-- 使用foldl的插入排序
insertionSort' :: Ord a => [a] -> [a]
insertionSort' = foldl (flip insert) []
  where
    insert x [] = [x]
    insert x (y:ys) = 
        if x <= y 
        then x:y:ys 
        else y:insert x ys

-- 优化的插入排序（使用二分查找）
insertionSortBinary :: Ord a => [a] -> [a]
insertionSortBinary = foldr insert []
  where
    insert x xs = insertAt (binarySearch x xs) x xs
    
    binarySearch :: Ord a => a -> [a] -> Int
    binarySearch x xs = binarySearch' x xs 0 (length xs - 1)
      where
        binarySearch' x xs left right
          | left > right = left
          | otherwise = 
              let mid = (left + right) `div` 2
                  midVal = xs !! mid
              in if x <= midVal 
                 then binarySearch' x xs left (mid - 1)
                 else binarySearch' x xs (mid + 1) right
    
    insertAt :: Int -> a -> [a] -> [a]
    insertAt i x xs = take i xs ++ [x] ++ drop i xs
```

#### 复杂度分析
- **时间复杂度**: O(n²) 最坏和平均情况，O(n) 最好情况
- **空间复杂度**: O(1)
- **稳定性**: 稳定

## 4. 高级排序算法

### 4.1 归并排序

#### 算法描述
归并排序采用分治策略，将数组分成两半，递归排序，然后合并两个有序数组。

#### Haskell实现

```haskell
-- 归并排序
mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
    in merge (mergeSort left) (mergeSort right)

-- 合并两个有序列表
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = 
    if x <= y 
    then x : merge xs (y:ys)
    else y : merge (x:xs) ys

-- 优化的归并排序（自底向上）
mergeSortBottomUp :: Ord a => [a] -> [a]
mergeSortBottomUp xs = 
    let n = length xs
        sorted = iterate mergePass (map (:[]) xs) !! ceiling (logBase 2 (fromIntegral n))
    in head sorted
  where
    mergePass :: Ord a => [[a]] -> [[a]]
    mergePass [] = []
    mergePass [xs] = [xs]
    mergePass (xs:ys:rest) = merge xs ys : mergePass rest
    mergePass xs = xs
    
    merge :: Ord a => [a] -> [a] -> [a]
    merge [] ys = ys
    merge xs [] = xs
    merge (x:xs) (y:ys) = 
        if x <= y 
        then x : merge xs (y:ys)
        else y : merge (x:xs) ys
```

#### 复杂度分析
- **时间复杂度**: O(n log n) 所有情况
- **空间复杂度**: O(n)
- **稳定性**: 稳定

#### 形式化证明

**定理 4.1**: 归并排序正确性

**证明**: 
1. **基础情况**: 空列表和单元素列表已排序
2. **归纳假设**: 假设对长度小于n的列表，算法正确排序
3. **归纳步骤**: 
   - 分割操作将列表分成两个子列表
   - 递归调用对子列表正确排序（归纳假设）
   - 合并操作将两个有序列表合并为有序列表

**引理 4.1**: 合并操作正确性
**证明**: 通过结构归纳法证明合并操作保持有序性。

### 4.2 快速排序

#### 算法描述
快速排序选择一个基准元素，将数组分成小于基准和大于基准的两部分，递归排序。

#### Haskell实现

```haskell
-- 快速排序
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (x:xs) = 
    let smaller = [a | a <- xs, a <= x]
        larger = [a | a <- xs, a > x]
    in quickSort smaller ++ [x] ++ quickSort larger

-- 优化的快速排序（三路划分）
quickSort3Way :: Ord a => [a] -> [a]
quickSort3Way [] = []
quickSort3Way (x:xs) = 
    let (smaller, equal, larger) = partition3 x xs
    in quickSort3Way smaller ++ equal ++ quickSort3Way larger
  where
    partition3 :: Ord a => a -> [a] -> ([a], [a], [a])
    partition3 pivot = foldr f ([], [pivot], [])
      where
        f y (smaller, equal, larger) = 
            if y < pivot 
            then (y:smaller, equal, larger)
            else if y == pivot 
                 then (smaller, y:equal, larger)
                 else (smaller, equal, y:larger)

-- 随机化快速排序
quickSortRandom :: Ord a => [a] -> IO [a]
quickSortRandom [] = return []
quickSortRandom xs = do
    let n = length xs
    pivotIndex <- randomRIO (0, n-1)
    let pivot = xs !! pivotIndex
        (smaller, equal, larger) = partition3 pivot xs
    smaller' <- quickSortRandom smaller
    larger' <- quickSortRandom larger
    return $ smaller' ++ equal ++ larger'
  where
    partition3 pivot = foldr f ([], [pivot], [])
      where
        f y (smaller, equal, larger) = 
            if y < pivot 
            then (y:smaller, equal, larger)
            else if y == pivot 
                 then (smaller, y:equal, larger)
                 else (smaller, equal, y:larger)
```

#### 复杂度分析
- **时间复杂度**: O(n log n) 平均情况，O(n²) 最坏情况
- **空间复杂度**: O(log n) 平均情况，O(n) 最坏情况
- **稳定性**: 不稳定

### 4.3 堆排序

#### 算法描述
堆排序利用堆数据结构，首先构建最大堆，然后逐个提取堆顶元素。

#### Haskell实现

```haskell
-- 堆排序
heapSort :: Ord a => [a] -> [a]
heapSort xs = heapSort' (buildMaxHeap xs)
  where
    heapSort' [] = []
    heapSort' heap = 
        let (max, rest) = extractMax heap
        in max : heapSort' rest

-- 构建最大堆
buildMaxHeap :: Ord a => [a] -> [a]
buildMaxHeap xs = 
    let n = length xs
        indices = [n `div` 2 - 1, n `div` 2 - 2 .. 0]
    in foldr heapify xs indices

-- 堆化操作
heapify :: Ord a => Int -> [a] -> [a]
heapify i xs = 
    let n = length xs
        left = 2 * i + 1
        right = 2 * i + 2
        largest = findLargest i left right xs
    in if largest /= i 
       then heapify largest (swap i largest xs)
       else xs
  where
    findLargest i left right xs
      | left < n && xs !! left > xs !! i = left
      | right < n && xs !! right > xs !! i = right
      | otherwise = i
    
    swap i j xs = 
        let xi = xs !! i
            xj = xs !! j
        in take i xs ++ [xj] ++ drop (i+1) (take j xs) ++ [xi] ++ drop (j+1) xs

-- 提取最大值
extractMax :: Ord a => [a] -> (a, [a])
extractMax [] = error "Empty heap"
extractMax (x:xs) = (x, heapify 0 xs)
```

#### 复杂度分析
- **时间复杂度**: O(n log n) 所有情况
- **空间复杂度**: O(1)
- **稳定性**: 不稳定

## 5. 非比较排序算法

### 5.1 计数排序

#### 算法描述
计数排序适用于已知范围的整数排序，通过统计每个元素出现的次数进行排序。

#### Haskell实现

```haskell
-- 计数排序
countingSort :: [Int] -> [Int]
countingSort xs = 
    let maxVal = maximum xs
        count = replicate (maxVal + 1) 0
        count' = foldr (\x acc -> acc // [(x, acc !! x + 1)]) count xs
        sorted = concatMap (\i -> replicate (count' !! i) i) [0..maxVal]
    in sorted
  where
    (//) :: [a] -> [(Int, a)] -> [a]
    xs // [] = xs
    xs // ((i, v):updates) = xs // updates // [(i, v)]
    xs // [(i, v)] = take i xs ++ [v] ++ drop (i+1) xs

-- 优化的计数排序
countingSort' :: [Int] -> [Int]
countingSort' xs = 
    let maxVal = maximum xs
        minVal = minimum xs
        range = maxVal - minVal + 1
        count = replicate range 0
        count' = foldr (\x acc -> acc // [(x - minVal, acc !! (x - minVal) + 1)]) count xs
        sorted = concatMap (\i -> replicate (count' !! i) (i + minVal)) [0..range-1]
    in sorted
  where
    (//) :: [a] -> [(Int, a)] -> [a]
    xs // [] = xs
    xs // ((i, v):updates) = xs // updates // [(i, v)]
    xs // [(i, v)] = take i xs ++ [v] ++ drop (i+1) xs
```

#### 复杂度分析
- **时间复杂度**: O(n + k) 其中k是数据范围
- **空间复杂度**: O(k)
- **稳定性**: 稳定

### 5.2 基数排序

#### 算法描述
基数排序按位进行排序，从最低位到最高位依次排序。

#### Haskell实现

```haskell
-- 基数排序
radixSort :: [Int] -> [Int]
radixSort xs = 
    let maxDigits = maximum (map (length . show . abs) xs)
    in foldr (\digit sorted -> sortByDigit digit sorted) xs [0..maxDigits-1]

-- 按指定位排序
sortByDigit :: Int -> [Int] -> [Int]
sortByDigit digit xs = 
    let buckets = replicate 10 []
        buckets' = foldr (\x acc -> 
            let d = getDigit x digit
                bucket = acc !! d
            in acc // [(d, x:bucket)]) buckets xs
    in concat buckets'
  where
    getDigit x d = (abs x `div` (10^d)) `mod` 10
    
    (//) :: [a] -> [(Int, a)] -> [a]
    xs // [] = xs
    xs // ((i, v):updates) = xs // updates // [(i, v)]
    xs // [(i, v)] = take i xs ++ [v] ++ drop (i+1) xs

-- 优化的基数排序（使用计数排序）
radixSortOptimized :: [Int] -> [Int]
radixSortOptimized xs = 
    let maxDigits = maximum (map (length . show . abs) xs)
    in foldr (\digit sorted -> countingSortByDigit digit sorted) xs [0..maxDigits-1]

-- 按位计数排序
countingSortByDigit :: Int -> [Int] -> [Int]
countingSortByDigit digit xs = 
    let count = replicate 10 0
        count' = foldr (\x acc -> 
            let d = getDigit x digit
            in acc // [(d, acc !! d + 1)]) count xs
        output = replicate (length xs) 0
        output' = foldr (\x acc -> 
            let d = getDigit x digit
                pos = count' !! d - 1
                count'' = count' // [(d, count' !! d - 1)]
            in acc // [(pos, x)]) output xs
    in output'
  where
    getDigit x d = (abs x `div` (10^d)) `mod` 10
    
    (//) :: [a] -> [(Int, a)] -> [a]
    xs // [] = xs
    xs // ((i, v):updates) = xs // updates // [(i, v)]
    xs // [(i, v)] = take i xs ++ [v] ++ drop (i+1) xs
```

#### 复杂度分析
- **时间复杂度**: O(d(n + k)) 其中d是位数，k是基数
- **空间复杂度**: O(n + k)
- **稳定性**: 稳定

## 6. 排序算法比较

### 6.1 复杂度比较表

| 算法 | 平均时间复杂度 | 最坏时间复杂度 | 空间复杂度 | 稳定性 |
|------|----------------|----------------|------------|--------|
| 冒泡排序 | O(n²) | O(n²) | O(1) | 稳定 |
| 选择排序 | O(n²) | O(n²) | O(1) | 不稳定 |
| 插入排序 | O(n²) | O(n²) | O(1) | 稳定 |
| 归并排序 | O(n log n) | O(n log n) | O(n) | 稳定 |
| 快速排序 | O(n log n) | O(n²) | O(log n) | 不稳定 |
| 堆排序 | O(n log n) | O(n log n) | O(1) | 不稳定 |
| 计数排序 | O(n + k) | O(n + k) | O(k) | 稳定 |
| 基数排序 | O(d(n + k)) | O(d(n + k)) | O(n + k) | 稳定 |

### 6.2 选择指南

1. **小数据集 (n < 50)**: 插入排序
2. **中等数据集**: 快速排序或归并排序
3. **大数据集**: 归并排序或堆排序
4. **整数数据**: 计数排序或基数排序
5. **需要稳定性**: 归并排序或插入排序
6. **内存受限**: 堆排序或插入排序

## 7. 性能测试

```haskell
-- 性能测试框架
import System.Random
import Data.Time.Clock

-- 生成测试数据
generateTestData :: Int -> IO [Int]
generateTestData n = do
    gen <- getStdGen
    return $ take n $ randomRs (1, 1000) gen

-- 测试排序算法性能
testSortingPerformance :: ([Int] -> [Int]) -> String -> [Int] -> IO ()
testSortingPerformance sortFunc name data = do
    start <- getCurrentTime
    let sorted = sortFunc data
    end <- getCurrentTime
    let diff = diffUTCTime end start
    putStrLn $ name ++ ": " ++ show diff ++ " seconds"
    putStrLn $ "Sorted: " ++ show (take 10 sorted)

-- 运行所有测试
runAllTests :: IO ()
runAllTests = do
    testData <- generateTestData 10000
    putStrLn "Sorting Algorithm Performance Test"
    putStrLn "=================================="
    testSortingPerformance bubbleSort "Bubble Sort" testData
    testSortingPerformance insertionSort "Insertion Sort" testData
    testSortingPerformance mergeSort "Merge Sort" testData
    testSortingPerformance quickSort "Quick Sort" testData
    testSortingPerformance heapSort "Heap Sort" testData
```

## 8. 总结

本文档介绍了各种经典排序算法在Haskell中的实现，包括：

1. **基础排序算法**: 冒泡排序、选择排序、插入排序
2. **高级排序算法**: 归并排序、快速排序、堆排序
3. **非比较排序**: 计数排序、基数排序

每个算法都包含：
- 详细的算法描述
- 完整的Haskell实现
- 复杂度分析
- 形式化证明
- 性能测试

这些实现展示了函数式编程在算法实现中的优势，包括：
- 简洁的代码表达
- 强类型安全
- 易于理解和维护
- 良好的模块化设计 