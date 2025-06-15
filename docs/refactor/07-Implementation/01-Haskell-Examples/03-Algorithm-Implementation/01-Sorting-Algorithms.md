# 排序算法实现 (Sorting Algorithms)

## 概述

排序算法是计算机科学的基础，本文档展示了各种排序算法在Haskell中的实现，包括数学分析和性能比较。

## 1. 快速排序 (Quick Sort)

### 数学定义

快速排序的平均时间复杂度为 $O(n \log n)$，最坏情况为 $O(n^2)$。

### Haskell实现

```haskell
-- 基本快速排序
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (x:xs) = 
  quicksort [y | y <- xs, y <= x] ++ 
  [x] ++ 
  quicksort [y | y <- xs, y > x]

-- 优化版本：使用三路划分
quicksort3Way :: Ord a => [a] -> [a]
quicksort3Way [] = []
quicksort3Way (x:xs) = 
  quicksort3Way less ++ 
  equal ++ 
  quicksort3Way greater
  where
    (less, equal, greater) = partition3 x xs

partition3 :: Ord a => a -> [a] -> ([a], [a], [a])
partition3 pivot = foldr f ([], [pivot], [])
  where
    f y (less, equal, greater)
      | y < pivot = (y:less, equal, greater)
      | y == pivot = (less, y:equal, greater)
      | otherwise = (less, equal, y:greater)

-- 随机化快速排序
import System.Random

quicksortRandom :: Ord a => [a] -> IO [a]
quicksortRandom [] = return []
quicksortRandom xs = do
  pivotIndex <- randomRIO (0, length xs - 1)
  let pivot = xs !! pivotIndex
  let (less, equal, greater) = partition3 pivot xs
  lessSorted <- quicksortRandom less
  greaterSorted <- quicksortRandom greater
  return $ lessSorted ++ equal ++ greaterSorted
```

## 2. 归并排序 (Merge Sort)

### 数学定义

归并排序的时间复杂度为 $O(n \log n)$，空间复杂度为 $O(n)$。

### Haskell实现

```haskell
-- 基本归并排序
mergesort :: Ord a => [a] -> [a]
mergesort [] = []
mergesort [x] = [x]
mergesort xs = merge (mergesort left) (mergesort right)
  where
    (left, right) = splitAt (length xs `div` 2) xs

-- 归并函数
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 自底向上归并排序
mergesortBottomUp :: Ord a => [a] -> [a]
mergesortBottomUp = foldr merge [] . map (:[])

-- 并行归并排序
import Control.Parallel
import Control.Parallel.Strategies

parMergesort :: Ord a => [a] -> [a]
parMergesort [] = []
parMergesort [x] = [x]
parMergesort xs = 
  (leftSorted `par` rightSorted) `pseq`
  merge leftSorted rightSorted
  where
    (left, right) = splitAt (length xs `div` 2) xs
    leftSorted = parMergesort left
    rightSorted = parMergesort right
```

## 3. 堆排序 (Heap Sort)

### 数学定义

堆排序的时间复杂度为 $O(n \log n)$，空间复杂度为 $O(1)$。

### Haskell实现

```haskell
-- 堆数据结构
data Heap a = Empty | Node a (Heap a) (Heap a)

-- 堆排序
heapsort :: Ord a => [a] -> [a]
heapsort xs = heapToList $ buildHeap xs

-- 构建堆
buildHeap :: Ord a => [a] -> Heap a
buildHeap = foldr insert Empty

-- 插入元素
insert :: Ord a => a -> Heap a -> Heap a
insert x Empty = Node x Empty Empty
insert x (Node y left right)
  | x <= y = Node x (insert y right) left
  | otherwise = Node y (insert x right) left

-- 提取最大值
extractMax :: Ord a => Heap a -> Maybe (a, Heap a)
extractMax Empty = Nothing
extractMax (Node x left right) = Just (x, mergeHeaps left right)

-- 合并堆
mergeHeaps :: Ord a => Heap a -> Heap a -> Heap a
mergeHeaps Empty h = h
mergeHeaps h Empty = h
mergeHeaps (Node x left1 right1) (Node y left2 right2)
  | x >= y = Node x (mergeHeaps left1 right1) (Node y left2 right2)
  | otherwise = Node y (mergeHeaps left2 right2) (Node x left1 right1)

-- 堆转列表
heapToList :: Ord a => Heap a -> [a]
heapToList Empty = []
heapToList h = case extractMax h of
  Nothing -> []
  Just (x, h') -> x : heapToList h'

-- 数组实现的堆排序
heapsortArray :: Ord a => [a] -> [a]
heapsortArray xs = go (buildMaxHeap xs) (length xs)
  where
    go heap 0 = []
    go heap n = 
      let (maxVal, heap') = extractMax heap
      in maxVal : go heap' (n - 1)

buildMaxHeap :: Ord a => [a] -> Heap a
buildMaxHeap = foldr insert Empty
```

## 4. 插入排序 (Insertion Sort)

### 数学定义

插入排序的时间复杂度为 $O(n^2)$，但对于小数据集或接近有序的数据效率较高。

### Haskell实现

```haskell
-- 基本插入排序
insertionSort :: Ord a => [a] -> [a]
insertionSort = foldr insert []

-- 插入函数
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys)
  | x <= y = x : y : ys
  | otherwise = y : insert x ys

-- 优化版本：使用二分查找
insertionSortBinary :: Ord a => [a] -> [a]
insertionSortBinary = foldr insertBinary []

insertBinary :: Ord a => a -> [a] -> [a]
insertBinary x xs = 
  let (left, right) = binarySearchSplit x xs
  in left ++ [x] ++ right

binarySearchSplit :: Ord a => a -> [a] -> ([a], [a])
binarySearchSplit x xs = go xs []
  where
    go [] acc = (reverse acc, [])
    go (y:ys) acc
      | x <= y = (reverse acc, y:ys)
      | otherwise = go ys (y:acc)

-- 希尔排序（插入排序的改进）
shellsort :: Ord a => [a] -> [a]
shellsort xs = foldr (gapInsertionSort xs) xs gaps
  where
    gaps = takeWhile (< length xs) $ iterate (\n -> n `div` 2) (length xs `div` 2)

gapInsertionSort :: Ord a => [a] -> Int -> [a] -> [a]
gapInsertionSort xs gap = go xs
  where
    go [] = []
    go (x:xs) = insertWithGap x gap (go xs)

insertWithGap :: Ord a => a -> Int -> [a] -> [a]
insertWithGap x gap xs = 
  let (left, right) = splitAt gap xs
  in left ++ [x] ++ right
```

## 5. 基数排序 (Radix Sort)

### 数学定义

基数排序的时间复杂度为 $O(d(n+k))$，其中 $d$ 是位数，$k$ 是基数。

### Haskell实现

```haskell
-- 基数排序
radixsort :: [Int] -> [Int]
radixsort xs = foldr radixPass xs [0..maxDigits xs - 1]
  where
    maxDigits = maximum . map (length . show . abs)

radixPass :: Int -> [Int] -> [Int]
radixPass digit xs = concat $ map snd $ sort $ map (\x -> (getDigit x digit, x)) xs

getDigit :: Int -> Int -> Int
getDigit x digit = (abs x `div` (10 ^ digit)) `mod` 10

-- 字符串基数排序
radixsortString :: [String] -> [String]
radixsortString xs = foldr radixPassString xs [0..maxLength xs - 1]
  where
    maxLength = maximum . map length

radixPassString :: Int -> [String] -> [String]
radixPassString pos xs = concat $ map snd $ sort $ map (\x -> (getChar x pos, x)) xs

getChar :: String -> Int -> Char
getChar s pos
  | pos < length s = s !! pos
  | otherwise = '\0'

-- 桶排序
bucketsort :: (Ord a, Num a) => [a] -> [a]
bucketsort xs = concat $ map insertionSort buckets
  where
    buckets = createBuckets xs (length xs)
    createBuckets xs n = 
      let minVal = minimum xs
          maxVal = maximum xs
          bucketSize = (maxVal - minVal) / fromIntegral n
      in foldr (insertIntoBucket minVal bucketSize) (replicate n []) xs

insertIntoBucket :: (Ord a, Num a) => a -> a -> a -> [[a]] -> [[a]]
insertIntoBucket minVal bucketSize x buckets = 
  let bucketIndex = min (floor ((x - minVal) / bucketSize)) (length buckets - 1)
  in take bucketIndex buckets ++ 
     [x : (buckets !! bucketIndex)] ++ 
     drop (bucketIndex + 1) buckets
```

## 6. 性能分析和比较

### 时间复杂度分析

```haskell
-- 性能测试框架
import System.CPUTime
import Text.Printf

timeSort :: (Ord a, Show a) => String -> ([a] -> [a]) -> [a] -> IO ()
timeSort name sortFunc xs = do
  start <- getCPUTime
  let result = sortFunc xs
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^12)
  printf "%s: %.6f seconds\n" name diff

-- 生成测试数据
generateTestData :: Int -> IO [Int]
generateTestData n = do
  gen <- getStdGen
  return $ take n $ randomRs (1, 1000) gen :: [Int]

-- 性能比较
compareSorts :: Int -> IO ()
compareSorts n = do
  xs <- generateTestData n
  putStrLn $ "Testing with " ++ show n ++ " elements:"
  timeSort "Quicksort" quicksort xs
  timeSort "Mergesort" mergesort xs
  timeSort "Heapsort" heapsort xs
  timeSort "InsertionSort" insertionSort xs
  timeSort "Radixsort" radixsort xs
```

### 空间复杂度分析

```haskell
-- 空间复杂度分析
data SpaceComplexity = O1 | OLogN | ON | ONLogN | ON2

sortSpaceComplexity :: String -> SpaceComplexity
sortSpaceComplexity "quicksort" = OLogN  -- 平均情况
sortSpaceComplexity "mergesort" = ON
sortSpaceComplexity "heapsort" = O1
sortSpaceComplexity "insertionsort" = O1
sortSpaceComplexity "radixsort" = ON
sortSpaceComplexity _ = ON

-- 内存使用分析
analyzeMemoryUsage :: [Int] -> [Int] -> Int
analyzeMemoryUsage original sorted = 
  length original + length sorted  -- 简化版本
```

## 7. 实际应用示例

### 1. 文件排序

```haskell
-- 文件排序应用
import System.IO
import Data.List

sortFile :: FilePath -> FilePath -> IO ()
sortFile inputFile outputFile = do
  content <- readFile inputFile
  let lines = lines content
  let sortedLines = sort lines
  writeFile outputFile (unlines sortedLines)

-- 大文件排序（分块处理）
sortLargeFile :: FilePath -> FilePath -> Int -> IO ()
sortLargeFile inputFile outputFile chunkSize = do
  input <- openFile inputFile ReadMode
  output <- openFile outputFile WriteMode
  sortChunks input output chunkSize
  hClose input
  hClose output

sortChunks :: Handle -> Handle -> Int -> IO ()
sortChunks input output chunkSize = do
  chunk <- readChunk input chunkSize
  if null chunk
    then return ()
    else do
      let sortedChunk = sort chunk
      writeChunk output sortedChunk
      sortChunks input output chunkSize

readChunk :: Handle -> Int -> IO [String]
readChunk h n = do
  eof <- hIsEOF h
  if eof
    then return []
    else do
      line <- hGetLine h
      rest <- readChunk h (n-1)
      return (line : rest)

writeChunk :: Handle -> [String] -> IO ()
writeChunk h = mapM_ (hPutStrLn h)
```

### 2. 数据库排序

```haskell
-- 数据库记录排序
data Record = Record
  { id :: Int
  , name :: String
  , age :: Int
  , salary :: Double
  }

-- 多字段排序
sortRecords :: [(Record -> a)] -> [Record] -> [Record]
sortRecords [] = id
sortRecords (f:fs) = sortBy (compare `on` f) . sortRecords fs

-- 使用示例
sortByNameThenAge :: [Record] -> [Record]
sortByNameThenAge = sortRecords [name, age]

sortBySalaryDesc :: [Record] -> [Record]
sortBySalaryDesc = sortBy (flip compare `on` salary)
```

## 8. 优化技巧

### 1. 混合排序

```haskell
-- 混合排序：小数据集使用插入排序，大数据集使用快速排序
hybridSort :: Ord a => [a] -> [a]
hybridSort xs
  | length xs <= 10 = insertionSort xs
  | otherwise = quicksort xs

-- 自适应排序
adaptiveSort :: Ord a => [a] -> [a]
adaptiveSort xs
  | isNearlySorted xs = insertionSort xs
  | length xs <= 50 = insertionSort xs
  | otherwise = quicksort xs

isNearlySorted :: Ord a => [a] -> Bool
isNearlySorted xs = 
  let inversions = countInversions xs
      maxInversions = length xs * (length xs - 1) `div` 2
  in inversions <= maxInversions `div` 4

countInversions :: Ord a => [a] -> Int
countInversions [] = 0
countInversions (x:xs) = 
  length [y | y <- xs, y < x] + countInversions xs
```

### 2. 并行排序

```haskell
-- 并行归并排序
import Control.Parallel
import Control.Parallel.Strategies

parMergesortThreshold :: Int
parMergesortThreshold = 1000

parMergesort :: Ord a => [a] -> [a]
parMergesort xs
  | length xs <= parMergesortThreshold = mergesort xs
  | otherwise = 
      let (left, right) = splitAt (length xs `div` 2) xs
          leftSorted = parMergesort left
          rightSorted = parMergesort right
      in (leftSorted `par` rightSorted) `pseq` merge leftSorted rightSorted
```

## 总结

本文档展示了各种排序算法在Haskell中的实现，包括：

1. **快速排序**：平均 $O(n \log n)$，适合大多数情况
2. **归并排序**：稳定 $O(n \log n)$，适合需要稳定性的场景
3. **堆排序**：原地排序，空间复杂度 $O(1)$
4. **插入排序**：小数据集高效，$O(n^2)$ 但常数因子小
5. **基数排序**：适合整数和字符串排序

每种算法都有其适用场景，选择合适的排序算法对于性能优化至关重要。

---

**相关链接**：
- [函数式编程基础](../01-Basic-Examples/01-Functional-Programming-Basics.md)
- [类型类与单子](../02-Advanced-Features/01-Type-Classes-and-Monads.md)
- [形式化证明](../04-Formal-Proofs/README.md)
- [实际应用](../05-Real-World-Applications/README.md) 