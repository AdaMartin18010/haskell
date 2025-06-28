# 性能优化

## 概述

本文档介绍Haskell程序性能优化的技术和方法。

## 编译优化

### GHC优化标志
```bash
# 基本优化
ghc -O2 Main.hs

# 高级优化
ghc -O2 -fllvm -optlo-O3 Main.hs

# 特定优化
ghc -O2 -funbox-strict-fields -fstrictness Main.hs
```

### 优化级别说明
```haskell
-- -O0: 无优化
-- -O1: 基本优化
-- -O2: 标准优化（推荐）
-- -Os: 优化大小
-- -O3: 激进优化
```

## 内存优化

### 严格求值
```haskell
-- 使用严格字段
data StrictRecord = StrictRecord 
  { field1 :: !Int      -- 严格字段
  , field2 :: !String   -- 严格字段
  , field3 :: [Int]     -- 惰性字段
  }

-- 使用seq强制求值
strictEval :: Int -> Int -> Int
strictEval x y = x `seq` y `seq` x + y

-- 使用BangPatterns
strictPattern :: !Int -> Int
strictPattern x = x * 2
```

### 内存泄漏避免
```haskell
-- 避免空间泄漏
sumList :: [Int] -> Int
sumList = go 0
  where
    go acc [] = acc
    go acc (x:xs) = go (acc + x) xs  -- 尾递归

-- 使用foldl'进行严格折叠
import Data.List (foldl')

strictSum :: [Int] -> Int
strictSum = foldl' (+) 0

-- 避免构建大列表
processLargeList :: [Int] -> Int
processLargeList = foldl' (\acc x -> acc + x * x) 0
```

### 垃圾回收调优
```haskell
-- 运行时参数
-- +RTS -H1G -A32M -RTS

-- 内存分配策略
-- +RTS -G1 -RTS  -- 单代GC
-- +RTS -G2 -RTS  -- 双代GC（默认）
```

## 算法优化

### 尾递归优化
```haskell
-- 尾递归版本
factorial :: Integer -> Integer
factorial n = go n 1
  where
    go 0 acc = acc
    go n acc = go (n - 1) (n * acc)

-- 尾递归列表处理
reverse' :: [a] -> [a]
reverse' = go []
  where
    go acc [] = acc
    go acc (x:xs) = go (x:acc) xs
```

### 惰性求值优化
```haskell
-- 使用惰性求值避免不必要计算
lazyFilter :: (a -> Bool) -> [a] -> [a]
lazyFilter p = go
  where
    go [] = []
    go (x:xs) = if p x then x : go xs else go xs

-- 使用take避免无限计算
takeFirst :: Int -> [a] -> [a]
takeFirst n = take n
```

### 缓存优化
```haskell
-- 记忆化
memoize :: (Int -> a) -> Int -> a
memoize f = (map f [0..] !!)

-- 使用Data.MemoCombinators
import Data.MemoCombinators

memoizedFib :: Integer -> Integer
memoizedFib = memo integral fib
  where
    fib 0 = 0
    fib 1 = 1
    fib n = memoizedFib (n-1) + memoizedFib (n-2)
```

## 数据结构优化

### 选择合适的数据结构
```haskell
-- 频繁查找：使用Map
import Data.Map (Map)
import qualified Data.Map as Map

lookupOptimized :: Map String Int -> String -> Maybe Int
lookupOptimized = Map.lookup

-- 频繁插入/删除：使用Set
import Data.Set (Set)
import qualified Data.Set as Set

setOperations :: Set Int -> Set Int
setOperations = Set.insert 42 . Set.delete 10

-- 频繁队列操作：使用Data.Sequence
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

queueOperations :: Seq Int -> Seq Int
queueOperations = (Seq.|> 42) . (10 Seq.<|)
```

### 字符串优化
```haskell
-- 使用Text而不是String
import Data.Text (Text)
import qualified Data.Text as T

textOperations :: Text -> Text
textOperations = T.toUpper . T.reverse

-- 使用Builder进行字符串构建
import Data.Text.Lazy.Builder

buildString :: [String] -> Text
buildString = toLazyText . mconcat . map fromString
```

## 并发优化

### 并行计算
```haskell
-- 使用par进行并行计算
import Control.Parallel

parallelSum :: [Int] -> Int
parallelSum [] = 0
parallelSum [x] = x
parallelSum xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
      leftSum = sum left
      rightSum = sum right
  in leftSum `par` rightSum `pseq` leftSum + rightSum

-- 使用parMap
import Control.Parallel.Strategies

parallelMap :: (a -> b) -> [a] -> [b]
parallelMap f = parMap rpar f
```

### 异步IO
```haskell
-- 使用async进行并发IO
import Control.Concurrent.Async

concurrentIO :: IO [String]
concurrentIO = do
  async1 <- async $ readFile "file1.txt"
  async2 <- async $ readFile "file2.txt"
  result1 <- wait async1
  result2 <- wait async2
  return [result1, result2]
```

## 性能分析

### 性能测量
```haskell
-- 使用criterion进行基准测试
import Criterion.Main

benchmarkExample :: IO ()
benchmarkExample = defaultMain
  [ bench "sum" $ whnf sum [1..1000]
  , bench "foldl'" $ whnf (foldl' (+) 0) [1..1000]
  ]

-- 使用timeit测量时间
import System.CPUTime

timeIt :: IO a -> IO (a, Double)
timeIt action = do
  start <- getCPUTime
  result <- action
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10^12)
  return (result, diff)
```

### 内存分析
```haskell
-- 使用GHC.Profiling进行内存分析
-- 编译时添加 -prof -fprof-auto
-- 运行时添加 +RTS -p -RTS

-- 使用GHC.Heap进行堆分析
import GHC.Heap

analyzeHeap :: IO ()
analyzeHeap = do
  heap <- getGCStats
  print heap
```

### 性能监控
```haskell
-- 使用GHC.Stats监控运行时统计
import GHC.Stats

monitorPerformance :: IO ()
monitorPerformance = do
  stats <- getGCStats
  putStrLn $ "Allocated: " ++ show (bytesAllocated stats)
  putStrLn $ "Copied: " ++ show (bytesCopied stats)
  putStrLn $ "GCs: " ++ show (numGcs stats)
```

## 编译时优化

### 内联优化
```haskell
-- 使用INLINE编译指示
{-# INLINE optimizedFunction #-}
optimizedFunction :: Int -> Int
optimizedFunction x = x * 2 + 1

-- 使用INLINABLE
{-# INLINABLE flexibleFunction #-}
flexibleFunction :: (Num a) => a -> a
flexibleFunction x = x * 2 + 1
```

### 特殊化
```haskell
-- 使用SPECIALIZE编译指示
{-# SPECIALIZE specializedFunction :: Int -> Int #-}
specializedFunction :: (Num a) => a -> a
specializedFunction x = x * 2 + 1
```

### 展开优化
```haskell
-- 使用UNPACK编译指示
data OptimizedRecord = OptimizedRecord
  { field1 :: {-# UNPACK #-} !Int
  , field2 :: {-# UNPACK #-} !Double
  }
```

## 运行时优化

### 线程优化
```haskell
-- 设置线程数
-- +RTS -N4 -RTS  -- 使用4个线程

-- 线程亲和性
import Control.Concurrent

setThreadAffinity :: IO ()
setThreadAffinity = do
  threadId <- myThreadId
  setThreadAffinity threadId 0  -- 绑定到CPU 0
```

### 内存分配优化
```haskell
-- 调整分配区域大小
-- +RTS -A32M -RTS  -- 32MB分配区域

-- 调整堆大小
-- +RTS -H1G -M2G -RTS  -- 1GB初始堆，2GB最大堆
```

## 最佳实践

### 代码组织
```haskell
-- 模块化设计
module OptimizedModule 
  ( exportedFunction
  , exportedType
  ) where

-- 避免不必要的导入
import qualified Data.Map as Map
import Data.Maybe (fromJust)  -- 只导入需要的函数

-- 使用类型别名提高可读性
type UserId = Int
type UserName = String
```

### 错误处理优化
```haskell
-- 使用Maybe而不是异常
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- 使用Either进行错误处理
type Result a = Either String a

safeOperation :: Int -> Result Int
safeOperation x
  | x < 0 = Left "Negative number"
  | otherwise = Right (x * 2)
```

---

**相关链接**：
- [数据结构](./005-Data-Structures.md)
- [算法](./004-Algorithms.md) 