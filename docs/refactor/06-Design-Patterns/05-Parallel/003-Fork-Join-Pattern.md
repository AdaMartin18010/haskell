# Fork-Join模式（Fork-Join Pattern）

## 概述

Fork-Join模式是一种并行编程模式，将任务分解为多个子任务并行执行，然后等待所有子任务完成后合并结果。

## 理论基础

- **任务分解**：将大任务分解为可并行的小任务
- **并行执行**：子任务在多个线程/进程中并行执行
- **结果合并**：等待所有子任务完成后合并结果

## Rust实现示例

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// Fork-Join框架
struct ForkJoin<T, R> {
    task_fn: Box<dyn Fn(T) -> R + Send + Sync>,
    merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
}

impl<T, R> ForkJoin<T, R>
where
    T: Send + Clone + 'static,
    R: Send + 'static,
{
    fn new(
        task_fn: Box<dyn Fn(T) -> R + Send + Sync>,
        merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
    ) -> Self {
        Self { task_fn, merge_fn }
    }
    
    fn execute(&self, inputs: Vec<T>) -> R {
        let num_threads = num_cpus::get();
        let chunk_size = (inputs.len() + num_threads - 1) / num_threads;
        let chunks: Vec<Vec<T>> = inputs
            .chunks(chunk_size)
            .map(|chunk| chunk.to_vec())
            .collect();
        
        let mut handles = Vec::new();
        let results = Arc::new(Mutex::new(Vec::new()));
        
        // Fork: 启动多个线程处理子任务
        for chunk in chunks {
            let task_fn = self.task_fn.clone();
            let results_clone = Arc::clone(&results);
            
            let handle = thread::spawn(move || {
                let chunk_results: Vec<R> = chunk.iter().map(|&ref input| task_fn(input.clone())).collect();
                results_clone.lock().unwrap().extend(chunk_results);
            });
            
            handles.push(handle);
        }
        
        // Join: 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }
        
        // 合并结果
        let final_results = results.lock().unwrap().clone();
        (self.merge_fn)(final_results)
    }
}

// 并行排序示例
struct ParallelSorter;

impl ParallelSorter {
    fn sort_chunk<T: Ord + Clone>(chunk: Vec<T>) -> Vec<T> {
        let mut sorted = chunk;
        sorted.sort();
        sorted
    }
    
    fn merge_sorted<T: Ord + Clone>(sorted_chunks: Vec<Vec<T>>) -> Vec<T> {
        let mut result = Vec::new();
        let mut indices: Vec<usize> = vec![0; sorted_chunks.len()];
        
        while indices.iter().enumerate().any(|(i, &idx)| idx < sorted_chunks[i].len()) {
            let mut min_value = None;
            let mut min_index = 0;
            
            for (i, &idx) in indices.iter().enumerate() {
                if idx < sorted_chunks[i].len() {
                    let value = &sorted_chunks[i][idx];
                    if min_value.is_none() || value < min_value.as_ref().unwrap() {
                        min_value = Some(value.clone());
                        min_index = i;
                    }
                }
            }
            
            if let Some(value) = min_value {
                result.push(value);
                indices[min_index] += 1;
            }
        }
        
        result
    }
}

// 并行矩阵乘法示例
struct MatrixMultiplier;

impl MatrixMultiplier {
    fn multiply_row(
        row: &[f64],
        matrix: &[Vec<f64>],
        row_index: usize,
    ) -> Vec<f64> {
        let cols = matrix[0].len();
        let mut result = vec![0.0; cols];
        
        for j in 0..cols {
            for k in 0..row.len() {
                result[j] += row[k] * matrix[k][j];
            }
        }
        
        result
    }
    
    fn multiply_matrices(a: Vec<Vec<f64>>, b: Vec<Vec<f64>>) -> Vec<Vec<f64>> {
        let rows = a.len();
        let cols = b[0].len();
        
        let fork_join = ForkJoin::new(
            Box::new(|row_index: usize| {
                MatrixMultiplier::multiply_row(&a[row_index], &b, row_index)
            }),
            Box::new(|results: Vec<Vec<f64>>| results),
        );
        
        let row_indices: Vec<usize> = (0..rows).collect();
        let result_rows = fork_join.execute(row_indices);
        
        result_rows
    }
}

// 递归Fork-Join
struct RecursiveForkJoin<T, R> {
    task_fn: Box<dyn Fn(T) -> R + Send + Sync>,
    merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
    threshold: usize,
}

impl<T, R> RecursiveForkJoin<T, R>
where
    T: Send + Clone + 'static,
    R: Send + 'static,
{
    fn new(
        task_fn: Box<dyn Fn(T) -> R + Send + Sync>,
        merge_fn: Box<dyn Fn(Vec<R>) -> R + Send + Sync>,
        threshold: usize,
    ) -> Self {
        Self {
            task_fn,
            merge_fn,
            threshold,
        }
    }
    
    fn execute(&self, inputs: Vec<T>) -> R {
        if inputs.len() <= self.threshold {
            // 直接处理小任务
            let results: Vec<R> = inputs.iter().map(|input| (self.task_fn)(input.clone())).collect();
            (self.merge_fn)(results)
        } else {
            // 递归分解
            let mid = inputs.len() / 2;
            let (left, right) = inputs.split_at(mid);
            
            let left_clone = left.to_vec();
            let right_clone = right.to_vec();
            let self_clone = self.clone();
            
            let (left_result, right_result) = rayon::join(
                || self_clone.execute(left_clone),
                || self_clone.execute(right_clone),
            );
            
            (self.merge_fn)(vec![left_result, right_result])
        }
    }
}

fn main() {
    // 并行排序示例
    let numbers: Vec<i32> = (0..1000).rev().collect();
    let sorter = ForkJoin::new(
        Box::new(|chunk: Vec<i32>| ParallelSorter::sort_chunk(chunk)),
        Box::new(|sorted_chunks: Vec<Vec<i32>>| ParallelSorter::merge_sorted(sorted_chunks)),
    );
    
    let chunk_size = 100;
    let chunks: Vec<Vec<i32>> = numbers
        .chunks(chunk_size)
        .map(|chunk| chunk.to_vec())
        .collect();
    
    let sorted_result = sorter.execute(chunks);
    println!("排序完成，前10个元素: {:?}", &sorted_result[..10]);
    
    // 矩阵乘法示例
    let a = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
    let b = vec![vec![5.0, 6.0], vec![7.0, 8.0]];
    let result = MatrixMultiplier::multiply_matrices(a, b);
    println!("矩阵乘法结果: {:?}", result);
    
    // 递归Fork-Join示例
    let recursive_sorter = RecursiveForkJoin::new(
        Box::new(|x: i32| x),
        Box::new(|results: Vec<i32>| {
            let mut sorted = results;
            sorted.sort();
            sorted
        }),
        100, // 阈值
    );
    
    let large_numbers: Vec<i32> = (0..10000).rev().collect();
    let recursive_result = recursive_sorter.execute(large_numbers);
    println!("递归排序完成，结果数量: {}", recursive_result.len());
}
```

## Haskell实现示例

```haskell
import Control.Parallel
import Control.Parallel.Strategies
import Data.List

-- Fork-Join框架
data ForkJoin a b = ForkJoin
    { taskFn :: a -> b
    , mergeFn :: [b] -> b
    }

-- 执行Fork-Join
executeForkJoin :: ForkJoin a b -> [a] -> b
executeForkJoin fj inputs = 
    let
        results = map (taskFn fj) inputs `using` parList rdeepseq
        finalResult = mergeFn fj results
    in finalResult

-- 并行排序示例
parallelSort :: (Ord a) => [a] -> [a]
parallelSort xs = 
    let
        chunks = chunksOf 100 xs
        sortedChunks = map sort chunks `using` parList rdeepseq
        mergedResult = mergeSorted sortedChunks
    in mergedResult

-- 合并已排序的列表
mergeSorted :: (Ord a) => [[a]] -> [a]
mergeSorted [] = []
mergeSorted [xs] = xs
mergeSorted (xs:ys:rest) = mergeSorted (merge xs ys : rest)
  where
    merge [] ys = ys
    merge xs [] = xs
    merge (x:xs) (y:ys)
        | x <= y = x : merge xs (y:ys)
        | otherwise = y : merge (x:xs) ys

-- 分块函数
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

-- 并行矩阵乘法
parallelMatrixMultiply :: [[Double]] -> [[Double]] -> [[Double]]
parallelMatrixMultiply a b = 
    let
        rows = length a
        rowIndices = [0..rows-1]
        multiplyRow i = multiplyRowWithMatrix (a !! i) b
        results = map multiplyRow rowIndices `using` parList rdeepseq
    in results

multiplyRowWithMatrix :: [Double] -> [[Double]] -> [Double]
multiplyRowWithMatrix row matrix = 
    let
        cols = length (head matrix)
        multiplyCol j = sum [row !! k * (matrix !! k) !! j | k <- [0..length row-1]]
    in [multiplyCol j | j <- [0..cols-1]]

-- 递归Fork-Join
data RecursiveForkJoin a b = RecursiveForkJoin
    { rTaskFn :: a -> b
    , rMergeFn :: [b] -> b
    , threshold :: Int
    }

executeRecursiveForkJoin :: RecursiveForkJoin a b -> [a] -> b
executeRecursiveForkJoin rfj inputs
    | length inputs <= threshold rfj = 
        let results = map (rTaskFn rfj) inputs
        in rMergeFn rfj results
    | otherwise = 
        let
            mid = length inputs `div` 2
            (left, right) = splitAt mid inputs
            (leftResult, rightResult) = 
                executeRecursiveForkJoin rfj left `par` 
                executeRecursiveForkJoin rfj right
        in rMergeFn rfj [leftResult, rightResult]

-- 测试函数
testParallelSort :: IO ()
testParallelSort = do
    let numbers = reverse [1..1000]
    let sorted = parallelSort numbers
    putStrLn $ "并行排序完成，前10个元素: " ++ show (take 10 sorted)

testMatrixMultiply :: IO ()
testMatrixMultiply = do
    let a = [[1.0, 2.0], [3.0, 4.0]]
    let b = [[5.0, 6.0], [7.0, 8.0]]
    let result = parallelMatrixMultiply a b
    putStrLn $ "矩阵乘法结果: " ++ show result

testRecursiveForkJoin :: IO ()
testRecursiveForkJoin = do
    let rfj = RecursiveForkJoin id (foldr1 (+)) 100
    let numbers = [1..10000]
    let result = executeRecursiveForkJoin rfj numbers
    putStrLn $ "递归Fork-Join结果: " ++ show result

main :: IO ()
main = do
    testParallelSort
    testMatrixMultiply
    testRecursiveForkJoin
```

## Lean实现思路

```lean
-- Fork-Join框架
structure ForkJoin (α β : Type) where
  taskFn : α → β
  mergeFn : List β → β

-- 执行Fork-Join
def executeForkJoin (fj : ForkJoin α β) (inputs : List α) : β :=
  let results := inputs.map fj.taskFn
  fj.mergeFn results

-- 并行排序
def parallelSort [Ord α] (xs : List α) : List α :=
  let chunks := xs.chunks 100
  let sortedChunks := chunks.map List.sort
  mergeSorted sortedChunks

-- 合并已排序的列表
def mergeSorted [Ord α] (sortedLists : List (List α)) : List α :=
  match sortedLists with
  | [] => []
  | [xs] => xs
  | xs :: ys :: rest => mergeSorted (merge xs ys :: rest)
  where
    merge [] ys := ys
    merge xs [] := xs
    merge (x :: xs) (y :: ys) :=
      if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys

-- 递归Fork-Join
structure RecursiveForkJoin (α β : Type) where
  taskFn : α → β
  mergeFn : List β → β
  threshold : Nat

def executeRecursiveForkJoin (rfj : RecursiveForkJoin α β) (inputs : List α) : β :=
  if inputs.length ≤ rfj.threshold then
    let results := inputs.map rfj.taskFn
    rfj.mergeFn results
  else
    let mid := inputs.length / 2
    let (left, right) := inputs.splitAt mid
    let leftResult := executeRecursiveForkJoin rfj left
    let rightResult := executeRecursiveForkJoin rfj right
    rfj.mergeFn [leftResult, rightResult]
```

## 应用场景

- 并行排序算法
- 矩阵运算
- 图像处理
- 分治算法

## 最佳实践

- 合理选择任务粒度
- 避免过度并行化
- 实现负载均衡
- 监控线程开销
