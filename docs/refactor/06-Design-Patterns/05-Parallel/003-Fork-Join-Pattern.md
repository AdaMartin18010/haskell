# Fork-Join模式 (Fork-Join Pattern)

## 概述

Fork-Join模式是一种常见的并行计算模式，将大任务分解为多个子任务（Fork），并行执行后再合并结果（Join），广泛应用于多核并行、递归分治等场景。

## 核心思想

- 任务分解：将复杂任务递归拆分为可独立并行的小任务。
- 并行执行：各子任务可在不同线程/进程上并行运行。
- 结果合并：所有子任务完成后，将结果合并为最终输出。

## Rust实现示例

```rust
use rayon::prelude::*;

fn parallel_sum(slice: &[i32]) -> i32 {
    if slice.len() < 1000 {
        slice.iter().sum()
    } else {
        let mid = slice.len() / 2;
        let (left, right) = slice.split_at(mid);
        let (sum_left, sum_right) = rayon::join(|| parallel_sum(left), || parallel_sum(right));
        sum_left + sum_right
    }
}

fn main() {
    let data = vec![1; 100_000];
    let sum = parallel_sum(&data);
    println!("sum = {}", sum);
}
```

## Haskell实现示例

```haskell
import Control.Parallel.Strategies

parallelSum :: [Int] -> Int
parallelSum xs
  | length xs < 1000 = sum xs
  | otherwise = runEval $ do
      let (left, right) = splitAt (length xs `div` 2) xs
      sumLeft <- rpar (parallelSum left)
      sumRight <- rpar (parallelSum right)
      rseq sumLeft
      rseq sumRight
      return (sumLeft + sumRight)

main = print $ parallelSum (replicate 100000 1)
```

## Lean实现思路

Lean暂不直接支持多线程并行，但可用递归分治思想模拟Fork-Join结构。

```lean
partial def forkJoinSum (l : List Nat) : Nat :=
  if l.length < 1000 then l.foldl (·+·) 0
  else
    let (left, right) := l.splitAt (l.length / 2)
    forkJoinSum left + forkJoinSum right
```

## 应用场景

- 大规模数据处理（如并行归约、排序、矩阵运算）
- 递归分治算法（如快速排序、归并排序、斐波那契数列）
- 并行图像处理、科学计算

## 最佳实践

- 合理设置分割阈值，避免任务过细导致调度开销大
- 利用高效的线程池/任务调度库（如Rayon、Haskell的par）
- 注意合并阶段的同步与数据一致性

## 总结

Fork-Join模式是高效利用多核资源的基础并行模式，适用于可分解、可合并的计算任务。
