# Rust 深度解析

## 1. 语言概述

Rust 是一门注重安全、并发和性能的系统级编程语言，广泛应用于操作系统、嵌入式、WebAssembly、区块链等领域。

## 2. 语法基础

```rust
// 基本类型与函数
fn double(x: i32) -> i32 {
    x * 2
}

// 模式匹配
fn factorial(n: u32) -> u32 {
    match n {
        0 => 1,
        _ => n * factorial(n-1),
    }
}

// 集合操作
let squares: Vec<i32> = (1..=10).map(|x| x*x).collect();
```

## 3. 类型系统与所有权

- 静态强类型、trait、生命周期、泛型、类型推断
- 所有权与借用：
```rust
fn main() {
    let s = String::from("hello");
    takes_ownership(s); // s被移动
    // println!("{}", s); // 编译错误
}
fn takes_ownership(s: String) {
    println!("{}", s);
}
```
- 借用检查：
```rust
fn print_len(s: &String) {
    println!("len = {}", s.len());
}
```

## 4. 并发与安全

- 线程与消息传递：
```rust
use std::thread;
let handle = thread::spawn(|| {
    println!("Hello from a thread!");
});
handle.join().unwrap();
```
- 互斥与通道：
```rust
use std::sync::{Arc, Mutex};
use std::thread;
let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];
for _ in 0..10 {
    let counter = Arc::clone(&counter);
    handles.push(thread::spawn(move || {
        let mut num = counter.lock().unwrap();
        *num += 1;
    }));
}
for h in handles { h.join().unwrap(); }
```

## 5. 泛型与trait

- 泛型函数：
```rust
fn add<T: std::ops::Add<Output=T>>(x: T, y: T) -> T { x + y }
```
- trait与实现：
```rust
trait Drawable {
    fn draw(&self);
}
struct Circle;
impl Drawable for Circle {
    fn draw(&self) { println!("Circle"); }
}
```

## 6. 工程实践

- 构建工具：Cargo
- 包管理：crates.io
- 测试：cargo test
- 文档：cargo doc
- 性能优化：Profile, Benchmark

## 7. Rust与Haskell/Lean对比

| 特性      | Rust            | Haskell         | Lean            |
|-----------|-----------------|-----------------|-----------------|
| 所有权    | ✅              | GC              | N/A             |
| 借用      | ✅              | N/A             | N/A             |
| trait     | ✅              | 类型类          | typeclass       |
| 并发      | 线程/消息/async | STM/Async       | 任务/并发库     |
| 工程生态  | Cargo/crates.io | Hackage/Stack   | Lake/mathlib    |

## 8. 典型应用
- 操作系统、嵌入式、WebAssembly、区块链、网络服务

---

**相关链接**：
- [Haskell实现](../07-Implementation/001-Haskell-Implementation.md)
- [Lean实现](../07-Implementation/003-Lean-Implementation.md)
- [语言比较](./002-Language-Comparison.md)
