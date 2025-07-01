# 性能优化

## 概述

本文档介绍在Haskell、Rust和Lean中的性能优化技术和最佳实践。性能优化是软件开发的重要环节，需要深入理解语言特性和运行时行为。

## Haskell 性能优化

### 惰性求值优化

```haskell
-- 避免内存泄漏的严格性控制
{-# LANGUAGE BangPatterns #-}

-- 严格求值
strictSum :: [Int] -> Int
strictSum = go 0
  where
    go !acc [] = acc
    go !acc (x:xs) = go (acc + x) xs

-- 使用 seq 强制求值
forceEval :: [a] -> [a] -> [a]
forceEval xs ys = xs `seq` ys `seq` xs ++ ys

-- 深度严格性
{-# LANGUAGE DeepSeq #-}
import Control.DeepSeq

strictCalculation :: NFData a => a -> a -> a
strictCalculation x y = deepseq x (deepseq y (x `combine` y))
  where
    combine = undefined  -- 实际计算函数
```

### 内存优化

```haskell
-- 使用 unboxed 向量
import qualified Data.Vector.Unboxed as U

-- 高效的数值计算
sumVector :: U.Vector Int -> Int
sumVector = U.sum

-- 避免列表中间结果
efficientMap :: (a -> b) -> [a] -> [b]
efficientMap f = foldr ((:) . f) []

-- 流式处理大数据
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Char8 as LC

processLargeFile :: FilePath -> IO Int
processLargeFile path = do
  content <- L.readFile path
  return $ length $ LC.lines content
```

### 编译器优化

```haskell
-- 内联优化
{-# INLINE fastFunction #-}
fastFunction :: Int -> Int -> Int
fastFunction x y = x * x + y * y

-- 特化优化
{-# SPECIALIZE expensiveFunction :: Int -> Int #-}
{-# SPECIALIZE expensiveFunction :: Double -> Double #-}
expensiveFunction :: Num a => a -> a
expensiveFunction x = x * x + x

-- 规则重写
{-# RULES "map/map" forall f g xs. map f (map g xs) = map (f . g) xs #-}

-- 融合优化
import qualified Data.Vector as V

vectorChain :: V.Vector Int -> V.Vector Int
vectorChain = V.map (+1) . V.filter even . V.map (*2)
```

### 并发和并行优化

```haskell
import Control.Parallel
import Control.Parallel.Strategies

-- 并行计算
parallelSum :: [Int] -> Int
parallelSum xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
      leftSum = sum left
      rightSum = sum right
  in leftSum `par` rightSum `pseq` leftSum + rightSum

-- 并行策略
parMapStrategy :: (a -> b) -> [a] -> [b]
parMapStrategy f xs = map f xs `using` parList rdeepseq

-- 并行数组操作
import qualified Data.Vector as V

parallelVectorMap :: (a -> b) -> V.Vector a -> V.Vector b
parallelVectorMap f vec = V.map f vec `using` parVector 1000
```

### STM 性能优化

```haskell
import Control.Concurrent.STM

-- 高效的 STM 操作
data Counter = Counter (TVar Int)

newCounter :: STM Counter
newCounter = Counter <$> newTVar 0

-- 批量操作减少事务冲突
batchIncrement :: Counter -> Int -> STM ()
batchIncrement (Counter tvar) n = do
  current <- readTVar tvar
  writeTVar tvar (current + n)

-- 避免长事务
optimizedSTM :: TVar Int -> TVar Int -> STM ()
optimizedSTM tv1 tv2 = do
  -- 快速读取
  val1 <- readTVar tv1
  val2 <- readTVar tv2
  -- 最小化写入操作
  when (val1 > val2) $ writeTVar tv1 (val1 - 1)
```

## Rust 性能优化

### 零成本抽象

```rust
// 迭代器优化
fn process_data(data: &[i32]) -> i32 {
    data.iter()
        .filter(|&x| *x > 0)
        .map(|x| x * x)
        .sum()
}

// 内联优化
#[inline]
fn hot_function(x: i32, y: i32) -> i32 {
    x * x + y * y
}

// 分支预测优化
fn optimized_search(data: &[i32], target: i32) -> Option<usize> {
    for (i, &item) in data.iter().enumerate() {
        if likely(item == target) {
            return Some(i);
        }
    }
    None
}

// 使用 likely/unlikely 宏
#[inline]
fn likely(b: bool) -> bool {
    std::intrinsics::likely(b)
}
```

### 内存管理优化

```rust
use std::rc::Rc;
use std::sync::Arc;

// 避免不必要的克隆
fn efficient_processing(data: &Vec<String>) -> Vec<usize> {
    data.iter().map(|s| s.len()).collect()
}

// 使用 Cow 避免不必要分配
use std::borrow::Cow;

fn process_string(input: &str) -> Cow<str> {
    if input.contains("bad") {
        Cow::Owned(input.replace("bad", "good"))
    } else {
        Cow::Borrowed(input)
    }
}

// 内存池模式
struct Pool<T> {
    items: Vec<T>,
}

impl<T: Default> Pool<T> {
    fn get(&mut self) -> T {
        self.items.pop().unwrap_or_default()
    }
    
    fn put(&mut self, item: T) {
        self.items.push(item);
    }
}
```

### 并发优化

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use crossbeam::channel;

// 使用 crossbeam 提高并发性能
fn parallel_processing(data: Vec<i32>) -> Vec<i32> {
    let (sender, receiver) = channel::unbounded();
    let num_threads = num_cpus::get();
    
    // 分发工作
    for chunk in data.chunks(data.len() / num_threads) {
        let sender = sender.clone();
        let chunk = chunk.to_vec();
        thread::spawn(move || {
            let result: Vec<i32> = chunk.iter().map(|x| x * x).collect();
            sender.send(result).unwrap();
        });
    }
    
    // 收集结果
    drop(sender);
    let mut results = Vec::new();
    while let Ok(result) = receiver.recv() {
        results.extend(result);
    }
    results
}

// 无锁数据结构
use crossbeam::queue::ArrayQueue;

fn lockfree_example() {
    let queue = Arc::new(ArrayQueue::new(100));
    
    // 生产者
    let producer = {
        let queue = queue.clone();
        thread::spawn(move || {
            for i in 0..50 {
                queue.push(i).unwrap();
            }
        })
    };
    
    // 消费者
    let consumer = {
        let queue = queue.clone();
        thread::spawn(move || {
            while let Ok(item) = queue.pop() {
                println!("消费: {}", item);
            }
        })
    };
    
    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### SIMD 优化

```rust
// 使用 SIMD 指令
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[target_feature(enable = "avx2")]
unsafe fn simd_sum(data: &[f32]) -> f32 {
    let mut sum = _mm256_setzero_ps();
    let chunks = data.chunks_exact(8);
    
    for chunk in chunks {
        let vec = _mm256_loadu_ps(chunk.as_ptr());
        sum = _mm256_add_ps(sum, vec);
    }
    
    // 提取结果
    let mut result = [0.0; 8];
    _mm256_storeu_ps(result.as_mut_ptr(), sum);
    result.iter().sum()
}

// 自动向量化
fn vectorized_operation(a: &[f32], b: &[f32]) -> Vec<f32> {
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| x * y)
        .collect()
}
```

## Lean 性能优化

### 证明性能优化

```lean
-- 高效的证明策略
theorem efficient_proof (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]

-- 避免深度递归
theorem tail_recursive_sum (xs : List ℕ) : 
  xs.sum = xs.foldl (· + ·) 0 := by
  induction xs with
  | nil => simp [List.sum, List.foldl]
  | cons h t ih => 
    simp [List.sum, List.foldl]
    exact ih

-- 使用 simp 简化证明
@[simp]
theorem simple_arithmetic (a b : ℕ) : 
  a + b + 0 = a + b := by simp

-- 计算优化
def efficient_fibonacci : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 => 
  let rec aux (a b k : ℕ) : ℕ :=
    if k = 0 then a
    else aux b (a + b) (k - 1)
  aux 0 1 (n + 2)
```

### 类型级计算优化

```lean
-- 编译时计算
def compile_time_factorial (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1) * compile_time_factorial k

-- 类型级数值
inductive Vec (α : Type) : ℕ → Type where
| nil : Vec α 0
| cons : α → Vec α n → Vec α (n + 1)

-- 高效的向量操作
def vec_map {α β : Type} {n : ℕ} (f : α → β) : 
  Vec α n → Vec β n
| Vec.nil => Vec.nil
| Vec.cons h t => Vec.cons (f h) (vec_map f t)
```

### 元编程优化

```lean
-- 自动生成高效代码
syntax "auto_generate" ident : command

macro_rules
| `(auto_generate $name) => 
  `(def $name : ℕ → ℕ := fun n => n * 2)

-- 编译时反射
#check @Vec.rec

-- 策略组合优化
macro "fast_simp" : tactic => 
  `(tactic| (simp_all; try assumption; try rfl))
```

## 跨语言性能比较

### 基准测试框架

```haskell
-- Haskell 基准测试
import Criterion.Main

benchmarks :: [Benchmark]
benchmarks = 
  [ bench "list sum" $ whnf sum [1..10000]
  , bench "vector sum" $ whnf U.sum (U.fromList [1..10000])
  , bench "parallel sum" $ whnf parallelSum [1..10000]
  ]

main :: IO ()
main = defaultMain benchmarks
```

```rust
// Rust 基准测试
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_fibonacci(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

criterion_group!(benches, benchmark_fibonacci);
criterion_main!(benches);
```

### 性能分析工具

```haskell
-- Haskell 性能分析
-- 编译: ghc -prof -fprof-auto -rtsopts Main.hs
-- 运行: ./Main +RTS -p -h

import GHC.Conc (numCapabilities)

main :: IO ()
main = do
  putStrLn $ "使用 " ++ show numCapabilities ++ " 个核心"
  let result = expensiveComputation
  print result

expensiveComputation :: Int
expensiveComputation = sum [1..1000000]
```

```rust
// Rust 性能分析
// 使用 cargo flamegraph
fn main() {
    let data: Vec<i32> = (0..1000000).collect();
    let result = expensive_computation(&data);
    println!("结果: {}", result);
}

fn expensive_computation(data: &[i32]) -> i32 {
    data.iter()
        .filter(|&&x| x % 2 == 0)
        .map(|x| x * x)
        .sum()
}
```

## 内存优化策略

### 内存布局优化

```haskell
-- 使用 unpack pragmas
data Point = Point 
  { x :: {-# UNPACK #-} !Double
  , y :: {-# UNPACK #-} !Double
  }

-- 避免装箱
import qualified Data.Vector.Unboxed as U

efficientPoints :: U.Vector (Double, Double)
efficientPoints = U.fromList [(1.0, 2.0), (3.0, 4.0)]
```

```rust
// 内存对齐优化
#[repr(C)]
struct OptimizedStruct {
    a: u64,    // 8 字节
    b: u32,    // 4 字节
    c: u16,    // 2 字节
    d: u8,     // 1 字节
    e: u8,     // 1 字节
}

// 使用 Box 减少栈使用
enum LargeEnum {
    Small(u32),
    Large(Box<[u8; 1000]>),
}
```

### 缓存友好的算法

```haskell
-- 缓存友好的矩阵乘法
import qualified Data.Array as A

type Matrix = A.Array (Int, Int) Double

cacheEfficientMult :: Matrix -> Matrix -> Matrix
cacheEfficientMult a b = 
  let ((ar1, ac1), (ar2, ac2)) = A.bounds a
      ((br1, bc1), (br2, bc2)) = A.bounds b
      bounds = ((ar1, bc1), (ar2, bc2))
  in A.array bounds 
     [((i, j), blockMult i j) | i <- [ar1..ar2], j <- [bc1..bc2]]
  where
    blockMult i j = sum [a A.! (i, k) * b A.! (k, j) | k <- [ac1..ac2]]
```

```rust
// 缓存优化的数据结构
struct CacheOptimizedMatrix {
    data: Vec<f64>,
    rows: usize,
    cols: usize,
}

impl CacheOptimizedMatrix {
    fn multiply(&self, other: &Self) -> Self {
        let mut result = vec![0.0; self.rows * other.cols];
        
        // 分块矩阵乘法
        const BLOCK_SIZE: usize = 64;
        
        for i in (0..self.rows).step_by(BLOCK_SIZE) {
            for j in (0..other.cols).step_by(BLOCK_SIZE) {
                for k in (0..self.cols).step_by(BLOCK_SIZE) {
                    self.multiply_block(&mut result, other, i, j, k);
                }
            }
        }
        
        Self {
            data: result,
            rows: self.rows,
            cols: other.cols,
        }
    }
    
    fn multiply_block(&self, result: &mut [f64], other: &Self, 
                     i: usize, j: usize, k: usize) {
        let block_rows = std::cmp::min(64, self.rows - i);
        let block_cols = std::cmp::min(64, other.cols - j);
        let block_inner = std::cmp::min(64, self.cols - k);
        
        for bi in 0..block_rows {
            for bj in 0..block_cols {
                let mut sum = 0.0;
                for bk in 0..block_inner {
                    sum += self.data[(i + bi) * self.cols + (k + bk)] *
                           other.data[(k + bk) * other.cols + (j + bj)];
                }
                result[(i + bi) * other.cols + (j + bj)] += sum;
            }
        }
    }
}
```

## 编译器优化技巧

### GHC 优化选项

```bash
# Haskell 编译优化
ghc -O2 -fllvm -funbox-strict-fields -funfolding-use-threshold=16 Main.hs

# 特定优化标志
ghc -O2 -fexcess-precision -fno-state-hack -fspec-constr-count=6 Main.hs
```

### Rust 编译优化

```toml
# Cargo.toml 优化配置
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"

[profile.bench]
debug = true
```

## 性能监控和分析

### 运行时性能监控

```haskell
-- Haskell 性能监控
import System.TimeIt
import System.Mem

performanceTest :: IO ()
performanceTest = do
  putStrLn "开始性能测试..."
  
  -- 内存使用前
  stats1 <- getGCStats
  
  -- 计时执行
  (time, result) <- timeItT $ do
    let computation = sum [1..1000000]
    return computation
  
  -- 内存使用后
  stats2 <- getGCStats
  
  putStrLn $ "执行时间: " ++ show time ++ " 秒"
  putStrLn $ "结果: " ++ show result
  putStrLn $ "GC 次数: " ++ show (gcs stats2 - gcs stats1)
```

```rust
// Rust 性能监控
use std::time::Instant;

fn performance_test() {
    println!("开始性能测试...");
    
    let start = Instant::now();
    let result = expensive_computation();
    let duration = start.elapsed();
    
    println!("执行时间: {:?}", duration);
    println!("结果: {}", result);
}

// 使用 perf 工具
// perf record --call-graph=dwarf ./target/release/myapp
// perf report
```

## 最佳实践总结

### 通用优化原则

1. **测量优先**: 先测量，再优化
2. **局部性原理**: 优化数据访问模式
3. **算法复杂度**: 选择合适的算法
4. **类型系统**: 利用静态类型优化
5. **编译器友好**: 编写易于优化的代码

### 语言特定技巧

```haskell
-- Haskell 优化清单
optimizationChecklist :: [String]
optimizationChecklist = 
  [ "使用严格性注解避免内存泄漏"
  , "选择合适的数据结构 (Vector vs List)"
  , "利用编译器优化 (-O2, INLINE)"
  , "使用并行策略处理大数据"
  , "避免过度惰性求值"
  ]
```

```rust
// Rust 优化清单
const OPTIMIZATION_CHECKLIST: &[&str] = &[
    "避免不必要的内存分配",
    "使用零成本抽象",
    "充分利用所有权系统",
    "选择合适的并发原语",
    "编译时计算vs运行时计算",
];
```

## 性能调优工具链

### 分析工具

1. **Haskell**:
   - GHC profiler (`-prof -fprof-auto`)
   - ThreadScope (并行分析)
   - Criterion (基准测试)

2. **Rust**:
   - `cargo bench` (基准测试)
   - Flamegraph (火焰图)
   - Valgrind (内存分析)

3. **Lean**:
   - `#check` (类型检查性能)
   - Lean profiler (证明性能)

### 持续性能监控

```haskell
-- 自动化性能回归测试
import Test.Tasty.Bench

performanceRegression :: TestTree
performanceRegression = testGroup "Performance Tests"
  [ bench "algorithm v1" $ whnf oldAlgorithm testData
  , bench "algorithm v2" $ whnf newAlgorithm testData
  ]
  where
    testData = [1..10000]
```

通过系统性的性能优化方法，我们可以显著提升程序效率，同时保持代码的可读性和正确性。关键是理解每种语言的特性，选择合适的优化策略。

## 参考资料

- [GHC User's Guide - Optimisation](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/using-optimisation.html)
- [The Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Lean 4 Manual - Performance](https://leanprover.github.io/lean4/doc/)
