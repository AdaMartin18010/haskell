# 数据并行模式 (Data Parallelism Pattern)

## 概述

数据并行模式是一种将同一操作应用于大量数据元素的并行计算模式，适用于向量化、批量处理、GPU并行等场景。

## 核心思想

- 数据分片：将大数据集分割为多个子集。
- 并行处理：对每个子集独立并行执行相同操作。
- 结果合并：将各子集的处理结果合并为最终输出。

## Rust实现示例

```rust
use rayon::prelude::*;

fn parallel_square(data: &mut [i32]) {
    data.par_iter_mut().for_each(|x| *x *= *x);
}

fn main() {
    let mut data = vec![1, 2, 3, 4, 5];
    parallel_square(&mut data);
    println!("{:?}", data);
}
```

## Haskell实现示例

```haskell
import Control.Parallel.Strategies

parallelSquare :: [Int] -> [Int]
parallelSquare xs = parMap rpar (^2) xs

main = print $ parallelSquare [1,2,3,4,5]
```

## Lean实现思路

Lean可用map函数模拟数据并行。

```lean
def parallelSquare (l : List Nat) : List Nat :=
  l.map (fun x => x * x)
```

## 应用场景

- 向量/矩阵批量运算
- 图像处理、信号处理
- 大规模数据分析、机器学习批处理

## 最佳实践

- 利用高效的并行库（如Rayon、parMap）
- 数据分片均衡，避免负载倾斜
- 注意内存带宽和缓存一致性

## 总结

数据并行模式适用于大批量、同构操作的数据处理任务，是高性能计算和GPU编程的基础模式。
