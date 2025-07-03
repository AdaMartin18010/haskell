# 编程语言对比：Haskell、Rust、Lean

## 概述

本节系统对比Haskell、Rust、Lean三种现代语言在语法、类型系统、内存管理、并发、泛型、元编程、工程生态等方面的异同。

## 1. 语法风格

| 语言   | 主要风格         | 代码示例 |
|--------|------------------|----------|
| Haskell| 纯函数式         | `sum [1..10]` |
| Rust   | 命令式+函数式    | `let s: i32 = (1..=10).sum();` |
| Lean   | 依赖类型/证明    | `#eval List.sum (List.range 11)` |

## 2. 类型系统

| 语言   | 类型系统         | 特点           | 泛型/高阶类型 | 类型推断 |
|--------|------------------|----------------|--------------|----------|
| Haskell| 强类型/高阶类型  | 类型类、GADT   | ✅           | ✅       |
| Rust   | 静态强类型       | trait、生命周期| ✅           | ✅       |
| Lean   | 依赖类型         | typeclass、归纳| ✅           | ✅       |

- Haskell示例：

```haskell
add :: Num a => a -> a -> a
add x y = x + y
```

- Rust示例：

```rust
fn add<T: std::ops::Add<Output=T>>(x: T, y: T) -> T { x + y }
```

- Lean示例：

```lean
def add [Add α] (x y : α) : α := x + y
```

## 3. 内存管理

| 语言   | 内存管理方式     | 说明           |
|--------|------------------|----------------|
| Haskell| 垃圾回收         | 自动GC         |
| Rust   | 所有权/借用      | 零成本抽象     |
| Lean   | 自动/手动        | 主要用于证明   |

## 4. 并发与并行

| 语言   | 并发模型         | 关键特性       |
|--------|------------------|----------------|
| Haskell| STM/Async        | 轻量线程、STM  |
| Rust   | 线程/消息/async  | 安全并发、无数据竞争 |
| Lean   | 任务/并发库      | 理论为主       |

- Haskell STM示例：

```haskell
import Control.Concurrent.STM
atomically $ do
  v <- readTVar tvar
  writeTVar tvar (v+1)
```

- Rust线程示例：

```rust
use std::thread;
let handle = thread::spawn(|| println!("hi"));
handle.join().unwrap();
```

## 5. 泛型与元编程

| 语言   | 泛型/高阶类型    | 元编程         |
|--------|------------------|----------------|
| Haskell| 类型类、模板     | Template Haskell|
| Rust   | trait、宏        | 宏系统         |
| Lean   | typeclass、meta  | tactic/宏      |

- Haskell泛型：

```haskell
map :: (a -> b) -> [a] -> [b]
```

- Rust泛型：

```rust
fn map<T, F: Fn(T) -> U, U>(xs: Vec<T>, f: F) -> Vec<U> {
    xs.into_iter().map(f).collect()
}
```

- Lean泛型：

```lean
def map {α β} (f : α → β) : List α → List β
| [] => []
| (x::xs) => f x :: map f xs
```

## 6. 工程生态

| 语言   | 构建工具         | 包管理         | 生态/社区     |
|--------|------------------|----------------|--------------|
| Haskell| Cabal/Stack      | Hackage        | 成熟、学术    |
| Rust   | Cargo            | crates.io      | 工程、活跃    |
| Lean   | Lake             | mathlib        | 数学、教育    |

## 7. 典型应用领域

| 语言   | 主要应用         |
|--------|------------------|
| Haskell| 编译器、金融、分布式、DSL |
| Rust   | 系统编程、嵌入式、Web、区块链 |
| Lean   | 数学证明、形式化验证、教育 |

## 8. 交叉分析与总结

- Haskell注重抽象与类型安全，适合高层建模和并发。
- Rust强调内存安全和工程实践，适合系统级开发。
- Lean专注于形式化证明和依赖类型，适合理论研究和自动推理。
- 三者在类型系统、泛型、并发等方面互有借鉴，推动了现代编程语言理论与实践的发展。

---

**相关链接**：

- [Haskell实现](../07-Implementation/001-Haskell-Implementation.md)
- [Rust实现](../07-Implementation/002-Rust-Implementation.md)
- [Lean实现](../07-Implementation/003-Lean-Implementation.md)
- [语言范式](./001-Language-Paradigms.md)
