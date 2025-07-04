# 编程语言范式

## 概述

编程语言范式是指编程语言支持的基本程序设计风格和思想。
主流范式包括命令式、函数式、面向对象、逻辑、并发和声明式等。
不同范式适用于不同的问题领域和工程需求。

## 主要编程范式

| 范式         | 代表语言         | 主要特征                         | 典型应用           |
|--------------|------------------|----------------------------------|--------------------|
| 命令式       | C, Rust          | 状态变更、顺序执行、变量赋值     | 系统编程、嵌入式   |
| 函数式       | Haskell, Lean    | 不可变数据、高阶函数、递归       | 数学建模、并发     |
| 面向对象     | Java, Rust       | 封装、继承、多态                 | 大型软件、GUI      |
| 逻辑         | Prolog, Lean     | 规则推理、模式匹配、回溯         | AI、知识推理       |
| 并发         | Rust, Erlang     | 进程/线程、消息传递、无共享状态   | 分布式、网络       |
| 声明式       | SQL, Haskell     | 关注"做什么"而非"怎么做"         | 数据库、配置       |

### 1. 命令式范式

- 以状态变更和顺序执行为核心。
- 典型代码（Rust）：

```rust
let mut x = 0;
for i in 0..10 {
    x += i;
}
```

### 2. 函数式范式

- 强调不可变性、递归和高阶函数。
- 典型代码（Haskell）：

```haskell
sumList :: [Int] -> Int
sumList = foldr (+) 0
```

- Lean 也支持纯函数式风格：

```lean
def sumList (xs : List Nat) : Nat := xs.foldr (· + ·) 0
```

### 3. 面向对象范式

- 以对象、类、封装、继承为核心。
- Rust 通过trait和struct实现OOP：

```rust
trait Drawable {
    fn draw(&self);
}
struct Circle;
impl Drawable for Circle {
    fn draw(&self) { println!("Circle"); }
}
```

### 4. 逻辑范式

- 以规则、关系和推理为核心。
- Lean支持定理证明和逻辑推理：

```lean
theorem and_comm (a b : Prop) : a ∧ b ↔ b ∧ a := by constructor; intro h; cases h; constructor; assumption; assumption
```

### 5. 并发范式

- 以进程、线程、消息传递为核心。
- Rust并发示例：

```rust
use std::thread;
let handle = thread::spawn(|| {
    println!("Hello from a thread!");
});
handle.join().unwrap();
```

### 6. 声明式范式

- 关注"做什么"而非"怎么做"。
- Haskell的列表推导：

```haskell
squares = [x*x | x <- [1..10]]
```

## 多范式对比与交叉分析

| 特性/语言 | Haskell         | Rust            | Lean            |
|-----------|-----------------|-----------------|-----------------|
| 纯函数式  | ✅              | 部分支持        | ✅              |
| 命令式    | IO Monad        | ✅              | IO/State Monad  |
| OOP       | 类型类          | trait/struct    | typeclass/structure |
| 并发      | STM/Async       | 线程/消息/async | 任务/并发库     |
| 逻辑推理  | GHC扩展         | 宏/类型系统     | 定理证明/归纳   |
| 类型系统  | 强类型/高阶     | 零成本抽象      | 依赖类型        |

## 典型应用场景

- Haskell：形式化建模、编译器、金融建模、并发服务器
- Rust：系统编程、嵌入式、WebAssembly、并发网络
- Lean：数学证明、形式化验证、教育、自动推理

## 结论

现代编程语言往往支持多种范式。
Haskell、Rust、Lean在理论和工程实践中各有优势，交叉融合推动了软件工程和形式科学的发展。

---

**相关链接**：

- [Haskell实现](../07-Implementation/001-Haskell-Implementation.md)
- [Rust实现](../07-Implementation/002-Rust-Implementation.md)
- [Lean实现](../07-Implementation/003-Lean-Implementation.md)
- [语言比较](./002-Language-Comparison.md)
