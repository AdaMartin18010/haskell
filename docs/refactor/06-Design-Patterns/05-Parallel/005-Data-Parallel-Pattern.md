# 数据并行模式（Data Parallel Pattern）

## 概述

数据并行模式是一种并行编程模式，将相同操作应用于不同的数据元素，每个处理单元处理数据的一个子集。

## 理论基础

- **数据分割**：将数据分割为多个子集
- **并行处理**：每个子集在独立处理单元上并行处理
- **结果合并**：将各处理单元的结果合并

## Rust实现示例

```rust
use rayon::prelude::*;
use std::collections::HashMap;

// 数据并行处理器
struct DataParallelProcessor<T, R> {
    process_fn: Box<dyn Fn(&T) -> R + Send + Sync>,
    merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
}

impl<T, R> DataParallelProcessor<T, R>
where
    T: Send + Sync,
    R: Send + Sync,
{
    fn new(
        process_fn: Box<dyn Fn(&T) -> R + Send + Sync>,
        merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
    ) -> Self {
        Self { process_fn, merge_fn }
    }
    
    fn process(&self, data: Vec<T>) -> R {
        let results: Vec<R> = data.par_iter().map(|item| (self.process_fn)(item)).collect();
        (self.merge_fn)(results)
    }
}

// 并行数组操作
struct ParallelArrayProcessor;

impl ParallelArrayProcessor {
    fn map<T, R>(data: Vec<T>, f: impl Fn(&T) -> R + Send + Sync) -> Vec<R>
    where
        T: Send + Sync,
        R: Send + Sync,
    {
        data.par_iter().map(f).collect()
    }
    
    fn filter<T>(data: Vec<T>, predicate: impl Fn(&T) -> bool + Send + Sync) -> Vec<T>
    where
        T: Send + Sync,
    {
        data.into_par_iter().filter(predicate).collect()
    }
    
    fn reduce<T>(data: Vec<T>, init: T, op: impl Fn(T, T) -> T + Send + Sync) -> T
    where
        T: Send + Sync,
    {
        data.into_par_iter().reduce(|| init.clone(), op)
    }
    
    fn fold<T, R>(data: Vec<T>, init: R, op: impl Fn(R, &T) -> R + Send + Sync) -> R
    where
        T: Send + Sync,
        R: Send + Sync + Clone,
    {
        data.par_iter().fold(|| init.clone(), op)
    }
}

// 并行矩阵运算
struct ParallelMatrixOps;

impl ParallelMatrixOps {
    fn add_matrices(a: Vec<Vec<f64>>, b: Vec<Vec<f64>>) -> Vec<Vec<f64>> {
        a.par_iter()
            .zip(b.par_iter())
            .map(|(row_a, row_b)| {
                row_a.par_iter()
                    .zip(row_b.par_iter())
                    .map(|(&a, &b)| a + b)
                    .collect()
            })
            .collect()
    }
    
    fn multiply_by_scalar(matrix: Vec<Vec<f64>>, scalar: f64) -> Vec<Vec<f64>> {
        matrix
            .par_iter()
            .map(|row| row.par_iter().map(|&x| x * scalar).collect())
            .collect()
    }
    
    fn transpose(matrix: Vec<Vec<f64>>) -> Vec<Vec<f64>> {
        if matrix.is_empty() || matrix[0].is_empty() {
            return vec![];
        }
        
        let rows = matrix.len();
        let cols = matrix[0].len();
        
        (0..cols)
            .into_par_iter()
            .map(|col| {
                (0..rows)
                    .map(|row| matrix[row][col])
                    .collect()
            })
            .collect()
    }
}

// 并行图像处理
struct ParallelImageProcessor;

impl ParallelImageProcessor {
    fn apply_filter(
        pixels: Vec<u8>,
        width: usize,
        height: usize,
        filter_fn: impl Fn(u8) -> u8 + Send + Sync,
    ) -> Vec<u8> {
        pixels.par_iter().map(|&pixel| filter_fn(pixel)).collect()
    }
    
    fn brightness_adjustment(pixels: Vec<u8>, factor: f64) -> Vec<u8> {
        pixels
            .par_iter()
            .map(|&pixel| {
                let adjusted = (pixel as f64 * factor).clamp(0.0, 255.0);
                adjusted as u8
            })
            .collect()
    }
    
    fn grayscale_conversion(rgb_pixels: Vec<(u8, u8, u8)>) -> Vec<u8> {
        rgb_pixels
            .par_iter()
            .map(|&(r, g, b)| {
                let gray = (0.299 * r as f64 + 0.587 * g as f64 + 0.114 * b as f64) as u8;
                gray
            })
            .collect()
    }
}

// 并行统计计算
struct ParallelStatistics;

impl ParallelStatistics {
    fn mean(data: &[f64]) -> f64 {
        let sum: f64 = data.par_iter().sum();
        sum / data.len() as f64
    }
    
    fn variance(data: &[f64]) -> f64 {
        let mean = Self::mean(data);
        let squared_diff_sum: f64 = data
            .par_iter()
            .map(|&x| (x - mean).powi(2))
            .sum();
        squared_diff_sum / data.len() as f64
    }
    
    fn histogram(data: &[f64], bins: usize) -> Vec<usize> {
        let min = data.par_iter().fold(|| f64::INFINITY, |a, &b| a.min(b));
        let max = data.par_iter().fold(|| f64::NEG_INFINITY, |a, &b| a.max(b));
        let bin_width = (max - min) / bins as f64;
        
        let mut histogram = vec![0; bins];
        
        data.par_iter().for_each(|&value| {
            let bin_index = ((value - min) / bin_width).floor() as usize;
            let bin_index = bin_index.min(bins - 1);
            // 注意：这里需要原子操作或锁来保证线程安全
            // 简化实现，实际应用中应使用原子操作
        });
        
        histogram
    }
}

// 并行字符串处理
struct ParallelStringProcessor;

impl ParallelStringProcessor {
    fn word_count(texts: Vec<String>) -> HashMap<String, usize> {
        texts
            .par_iter()
            .flat_map(|text| {
                text.split_whitespace()
                    .map(|word| word.to_lowercase())
                    .collect::<Vec<String>>()
            })
            .fold(
                || HashMap::new(),
                |mut acc, word| {
                    *acc.entry(word).or_insert(0) += 1;
                    acc
                },
            )
            .reduce(
                || HashMap::new(),
                |mut acc, map| {
                    for (word, count) in map {
                        *acc.entry(word).or_insert(0) += count;
                    }
                    acc
                },
            )
    }
    
    fn parallel_sort_strings(strings: Vec<String>) -> Vec<String> {
        strings.into_par_iter().collect()
    }
    
    fn filter_strings(
        strings: Vec<String>,
        predicate: impl Fn(&String) -> bool + Send + Sync,
    ) -> Vec<String> {
        strings.into_par_iter().filter(predicate).collect()
    }
}

fn main() {
    // 基本数据并行示例
    let numbers: Vec<i32> = (1..1000000).collect();
    let processor = DataParallelProcessor::new(
        Box::new(|&x| x * x),
        Box::new(|results| results.iter().sum::<i32>()),
    );
    
    let result = processor.process(numbers);
    println!("平方和: {}", result);
    
    // 并行数组操作
    let doubled = ParallelArrayProcessor::map(vec![1, 2, 3, 4, 5], |&x| x * 2);
    println!("加倍结果: {:?}", doubled);
    
    let filtered = ParallelArrayProcessor::filter(vec![1, 2, 3, 4, 5], |&x| x % 2 == 0);
    println!("过滤结果: {:?}", filtered);
    
    let sum = ParallelArrayProcessor::reduce(vec![1, 2, 3, 4, 5], 0, |a, b| a + b);
    println!("求和结果: {}", sum);
    
    // 并行矩阵运算
    let matrix_a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let matrix_b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
    let matrix_sum = ParallelMatrixOps::add_matrices(matrix_a, matrix_b);
    println!("矩阵加法结果: {:?}", matrix_sum);
    
    // 并行图像处理
    let pixels: Vec<u8> = (0..1000000).map(|i| (i % 256) as u8).collect();
    let brightened = ParallelImageProcessor::brightness_adjustment(pixels, 1.5);
    println!("亮度调整完成，像素数量: {}", brightened.len());
    
    // 并行统计计算
    let data: Vec<f64> = (1..100000).map(|i| i as f64).collect();
    let mean = ParallelStatistics::mean(&data);
    let variance = ParallelStatistics::variance(&data);
    println!("均值: {}, 方差: {}", mean, variance);
    
    // 并行字符串处理
    let texts = vec![
        "hello world".to_string(),
        "hello rust".to_string(),
        "world programming".to_string(),
    ];
    let word_counts = ParallelStringProcessor::word_count(texts);
    println!("单词计数: {:?}", word_counts);
}
```

## Haskell实现示例

```haskell
import Control.Parallel
import Control.Parallel.Strategies
import Data.List
import qualified Data.Map as M

-- 数据并行处理器
data DataParallelProcessor a b = DataParallelProcessor
    { processFn :: a -> b
    , mergeFn :: [b] -> b
    }

-- 执行数据并行处理
executeDataParallel :: DataParallelProcessor a b -> [a] -> b
executeDataParallel processor data = 
    let
        results = map (processFn processor) data `using` parList rdeepseq
        finalResult = mergeFn processor results
    in finalResult

-- 并行数组操作
parallelMap :: (a -> b) -> [a] -> [b]
parallelMap f xs = map f xs `using` parList rdeepseq

parallelFilter :: (a -> Bool) -> [a] -> [a]
parallelFilter predicate xs = filter predicate xs `using` parList rdeepseq

parallelReduce :: (a -> a -> a) -> a -> [a] -> a
parallelReduce op init xs = foldr op init xs `using` parList rdeepseq

-- 并行矩阵运算
parallelMatrixAdd :: [[Double]] -> [[Double]] -> [[Double]]
parallelMatrixAdd a b = 
    zipWith (zipWith (+)) a b `using` parList (parList rdeepseq)

parallelMatrixScalarMultiply :: Double -> [[Double]] -> [[Double]]
parallelMatrixScalarMultiply scalar matrix = 
    map (map (* scalar)) matrix `using` parList (parList rdeepseq)

parallelMatrixTranspose :: [[Double]] -> [[Double]]
parallelMatrixTranspose matrix = 
    if null matrix || null (head matrix)
        then []
        else
            let cols = length (head matrix)
                rows = length matrix
            in [map (!! i) matrix | i <- [0..cols-1]] `using` parList rdeepseq

-- 并行图像处理
parallelImageFilter :: (Int -> Int) -> [Int] -> [Int]
parallelImageFilter filterFn pixels = 
    map filterFn pixels `using` parList rdeepseq

parallelBrightnessAdjustment :: Double -> [Int] -> [Int]
parallelBrightnessAdjustment factor pixels = 
    map (\pixel -> min 255 (max 0 (round (fromIntegral pixel * factor)))) pixels `using` parList rdeepseq

parallelGrayscaleConversion :: [(Int, Int, Int)] -> [Int]
parallelGrayscaleConversion rgbPixels = 
    map (\(r, g, b) -> round (0.299 * fromIntegral r + 0.587 * fromIntegral g + 0.114 * fromIntegral b)) rgbPixels `using` parList rdeepseq

-- 并行统计计算
parallelMean :: [Double] -> Double
parallelMean data = 
    let sum = sum data `using` parList rdeepseq
        count = length data
    in sum / fromIntegral count

parallelVariance :: [Double] -> Double
parallelVariance data = 
    let mean = parallelMean data
        squaredDiffs = map (\x -> (x - mean) ^ 2) data `using` parList rdeepseq
        sumSquaredDiffs = sum squaredDiffs
        count = length data
    in sumSquaredDiffs / fromIntegral count

parallelHistogram :: [Double] -> Int -> [Int]
parallelHistogram data bins = 
    let minVal = minimum data
        maxVal = maximum data
        binWidth = (maxVal - minVal) / fromIntegral bins
        binIndices = map (\x -> min (bins - 1) (floor ((x - minVal) / binWidth))) data `using` parList rdeepseq
    in foldl (\acc idx -> updateAt idx (+1) acc) (replicate bins 0) binIndices

-- 并行字符串处理
parallelWordCount :: [String] -> M.Map String Int
parallelWordCount texts = 
    let
        allWords = concatMap words texts `using` parList rdeepseq
        wordCounts = foldl (\acc word -> M.insertWith (+) word 1 acc) M.empty allWords
    in wordCounts

parallelSortStrings :: [String] -> [String]
parallelSortStrings strings = 
    sort strings `using` parList rdeepseq

parallelFilterStrings :: (String -> Bool) -> [String] -> [String]
parallelFilterStrings predicate strings = 
    filter predicate strings `using` parList rdeepseq

-- 测试函数
testBasicDataParallel :: IO ()
testBasicDataParallel = do
    let processor = DataParallelProcessor (\x -> x * x) sum
    let numbers = [1..1000000]
    let result = executeDataParallel processor numbers
    putStrLn $ "平方和: " ++ show result

testParallelArrayOps :: IO ()
testParallelArrayOps = do
    let doubled = parallelMap (*2) [1..5]
    putStrLn $ "加倍结果: " ++ show doubled
    
    let filtered = parallelFilter even [1..10]
    putStrLn $ "过滤结果: " ++ show filtered
    
    let sum = parallelReduce (+) 0 [1..100]
    putStrLn $ "求和结果: " ++ show sum

testParallelMatrixOps :: IO ()
testParallelMatrixOps = do
    let matrixA = [[1.0, 2.0], [3.0, 4.0]]
    let matrixB = [[5.0, 6.0], [7.0, 8.0]]
    let matrixSum = parallelMatrixAdd matrixA matrixB
    putStrLn $ "矩阵加法结果: " ++ show matrixSum

testParallelStatistics :: IO ()
testParallelStatistics = do
    let data = [1.0..100000.0]
    let mean = parallelMean data
    let variance = parallelVariance data
    putStrLn $ "均值: " ++ show mean ++ ", 方差: " ++ show variance

main :: IO ()
main = do
    testBasicDataParallel
    testParallelArrayOps
    testParallelMatrixOps
    testParallelStatistics
```

## Lean实现思路

```lean
-- 数据并行处理器
structure DataParallelProcessor (α β : Type) where
  processFn : α → β
  mergeFn : List β → β

-- 执行数据并行处理
def executeDataParallel (processor : DataParallelProcessor α β) (data : List α) : β :=
  let results := data.map processor.processFn
  processor.mergeFn results

-- 并行数组操作
def parallelMap (f : α → β) (xs : List α) : List β :=
  xs.map f

def parallelFilter (predicate : α → Bool) (xs : List α) : List α :=
  xs.filter predicate

def parallelReduce (op : α → α → α) (init : α) (xs : List α) : α :=
  xs.foldl op init

-- 并行矩阵运算
def parallelMatrixAdd (a b : List (List Double)) : List (List Double) :=
  List.zipWith (List.zipWith (· + ·)) a b

def parallelMatrixScalarMultiply (scalar : Double) (matrix : List (List Double)) : List (List Double) :=
  matrix.map (List.map (· * scalar))

def parallelMatrixTranspose (matrix : List (List Double)) : List (List Double) :=
  if matrix.isEmpty || matrix.head!.isEmpty then []
  else
    let cols := matrix.head!.length
    let rows := matrix.length
    List.range cols |>.map fun i => matrix.map (·.get! i)

-- 并行图像处理
def parallelImageFilter (filterFn : Nat → Nat) (pixels : List Nat) : List Nat :=
  pixels.map filterFn

def parallelBrightnessAdjustment (factor : Double) (pixels : List Nat) : List Nat :=
  pixels.map fun pixel => 
    let adjusted := (pixel.toDouble * factor).toNat
    if adjusted > 255 then 255 else if adjusted < 0 then 0 else adjusted

def parallelGrayscaleConversion (rgbPixels : List (Nat × Nat × Nat)) : List Nat :=
  rgbPixels.map fun (r, g, b) =>
    let gray := (0.299 * r.toDouble + 0.587 * g.toDouble + 0.114 * b.toDouble).toNat
    gray

-- 并行统计计算
def parallelMean (data : List Double) : Double :=
  let sum := data.sum
  let count := data.length.toDouble
  sum / count

def parallelVariance (data : List Double) : Double :=
  let mean := parallelMean data
  let squaredDiffs := data.map fun x => (x - mean) ^ 2
  let sumSquaredDiffs := squaredDiffs.sum
  let count := data.length.toDouble
  sumSquaredDiffs / count
```

## 应用场景

- 大规模数据处理
- 科学计算
- 图像和视频处理
- 机器学习算法

## 最佳实践

- 合理选择数据分块大小
- 避免数据竞争
- 优化内存访问模式
- 监控并行效率
