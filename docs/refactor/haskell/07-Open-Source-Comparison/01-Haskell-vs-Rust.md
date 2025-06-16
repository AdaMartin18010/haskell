# Haskell vs Rust 详细对比

## 🎯 概述

Haskell和Rust都是现代编程语言，具有强大的类型系统和内存安全保证。本文档从多个维度详细对比这两种语言，包括类型系统、内存管理、并发模型、生态系统等。

## 📚 核心对比

### 1. 类型系统对比

#### Haskell类型系统

**形式化定义**：
Haskell使用Hindley-Milner类型系统，支持类型推断和多态。

数学表示为：
$$\Gamma \vdash e : \tau \text{ with type inference}$$

**Haskell实现**：
```haskell
-- 类型推断
inferredType = 42  -- Haskell推断为 Int
inferredList = [1, 2, 3, 4, 5]  -- Haskell推断为 [Int]

-- 多态函数
id :: a -> a
id x = x

-- 类型类
class Show a where
    show :: a -> String

instance Show Int where
    show = show

-- 高级类型特性
data Maybe a = Nothing | Just a

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x
```

#### Rust类型系统

**形式化定义**：
Rust使用基于Hindley-Milner的类型系统，但增加了所有权和生命周期概念。

数学表示为：
$$\Gamma \vdash e : \tau \text{ with ownership and lifetime}$$

**Rust实现**：
```rust
// 类型推断
let inferred_type = 42; // Rust推断为 i32
let inferred_list = vec![1, 2, 3, 4, 5]; // Rust推断为 Vec<i32>

// 泛型函数
fn id<T>(x: T) -> T {
    x
}

// 特征（类似Haskell的类型类）
trait Show {
    fn show(&self) -> String;
}

impl Show for i32 {
    fn show(&self) -> String {
        self.to_string()
    }
}

// 枚举类型
enum Option<T> {
    None,
    Some(T),
}

fn safe_head<T>(list: &[T]) -> Option<&T> {
    list.first()
}
```

### 2. 内存管理对比

#### Haskell内存管理

**形式化定义**：
Haskell使用垃圾回收器管理内存，基于惰性求值。

数学表示为：
$$GC(M) = \text{Mark and Sweep}(M)$$

**Haskell实现**：
```haskell
-- 惰性求值
infiniteList :: [Integer]
infiniteList = [1..]

-- 只计算需要的部分
finiteList :: [Integer]
finiteList = take 5 infiniteList

-- 内存泄漏示例（如果不小心）
memoryLeak :: [Integer]
memoryLeak = [1..]  -- 可能造成内存泄漏

-- 避免内存泄漏
avoidLeak :: [Integer]
avoidLeak = take 1000 [1..]  -- 限制大小

-- 严格求值
strictSum :: [Int] -> Int
strictSum = foldl' (+) 0  -- 使用严格版本避免空间泄漏
```

#### Rust内存管理

**形式化定义**：
Rust使用所有权系统在编译时保证内存安全，无需垃圾回收。

数学表示为：
$$\text{Ownership}(x) \implies \text{Unique}(x) \land \text{Safe}(x)$$

**Rust实现**：
```rust
// 所有权系统
fn ownership_example() {
    let s1 = String::from("hello");
    let s2 = s1; // s1的所有权移动到s2，s1不再有效
    
    // println!("{}", s1); // 编译错误：s1已被移动
    println!("{}", s2); // 正确
}

// 借用系统
fn borrowing_example() {
    let s1 = String::from("hello");
    let len = calculate_length(&s1); // 借用s1
    println!("Length of '{}' is {}.", s1, len); // s1仍然有效
}

fn calculate_length(s: &String) -> usize {
    s.len()
}

// 生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 3. 并发模型对比

#### Haskell并发模型

**形式化定义**：
Haskell使用轻量级线程和STM（软件事务内存）进行并发编程。

数学表示为：
$$\text{STM}(T) = \text{Atomic}(T) \land \text{Consistent}(T)$$

**Haskell实现**：
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad

-- 轻量级线程
threadExample :: IO ()
threadExample = do
    threadId1 <- forkIO (putStrLn "Thread 1")
    threadId2 <- forkIO (putStrLn "Thread 2")
    putStrLn "Main thread"

-- STM（软件事务内存）
type Account = TVar Int

transfer :: Account -> Account -> Int -> STM ()
transfer from to amount = do
    fromBalance <- readTVar from
    toBalance <- readTVar to
    writeTVar from (fromBalance - amount)
    writeTVar to (toBalance + amount)

-- 使用STM
bankingExample :: IO ()
bankingExample = do
    account1 <- newTVarIO 100
    account2 <- newTVarIO 50
    
    atomically $ transfer account1 account2 30
    
    balance1 <- readTVarIO account1
    balance2 <- readTVarIO account2
    putStrLn $ "Account1: " ++ show balance1
    putStrLn $ "Account2: " ++ show balance2

-- 并行计算
import Control.Parallel

parallelSum :: [Int] -> Int
parallelSum xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
        leftSum = sum left
        rightSum = sum right
    in leftSum `par` rightSum `pseq` (leftSum + rightSum)
```

#### Rust并发模型

**形式化定义**：
Rust使用所有权系统保证线程安全，通过Send和Sync特征控制并发。

数学表示为：
$$\text{Send}(T) \land \text{Sync}(T) \implies \text{ThreadSafe}(T)$$

**Rust实现**：
```rust
use std::thread;
use std::sync::{Arc, Mutex};
use std::sync::mpsc;

// 线程创建
fn thread_example() {
    let handle1 = thread::spawn(|| {
        println!("Thread 1");
    });
    
    let handle2 = thread::spawn(|| {
        println!("Thread 2");
    });
    
    println!("Main thread");
    
    handle1.join().unwrap();
    handle2.join().unwrap();
}

// 共享状态
fn shared_state_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", *counter.lock().unwrap());
}

// 消息传递
fn message_passing_example() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        let val = String::from("hello");
        tx.send(val).unwrap();
    });
    
    let received = rx.recv().unwrap();
    println!("Got: {}", received);
}

// 原子操作
use std::sync::atomic::{AtomicUsize, Ordering};

fn atomic_example() {
    let counter = AtomicUsize::new(0);
    
    let handle = thread::spawn(move || {
        for _ in 0..1000 {
            counter.fetch_add(1, Ordering::SeqCst);
        }
    });
    
    handle.join().unwrap();
    println!("Counter: {}", counter.load(Ordering::SeqCst));
}
```

### 4. 错误处理对比

#### Haskell错误处理

**形式化定义**：
Haskell使用Maybe和Either类型进行错误处理，基于类型系统。

数学表示为：
$$\text{Maybe}(A) = \text{Nothing} + \text{Just}(A)$$

**Haskell实现**：
```haskell
-- Maybe类型
safeDivide :: Double -> Double -> Maybe Double
safeDivide _ 0 = Nothing
safeDivide x y = Just (x / y)

-- Either类型
data ValidationError = DivisionByZero | NegativeNumber

safeDivideEither :: Double -> Double -> Either ValidationError Double
safeDivideEither _ 0 = Left DivisionByZero
safeDivideEither x y = Right (x / y)

-- 错误处理链
errorHandlingChain :: Double -> Double -> Maybe Double
errorHandlingChain x y = do
    result <- safeDivide x y
    guard (result >= 0)
    return result

-- 异常处理（在IO中）
exceptionHandling :: IO ()
exceptionHandling = do
    result <- try (readFile "nonexistent.txt")
    case result of
        Left e -> putStrLn $ "Error: " ++ show (e :: IOError)
        Right content -> putStrLn content
```

#### Rust错误处理

**形式化定义**：
Rust使用Result类型进行错误处理，强制处理所有错误情况。

数学表示为：
$$\text{Result}(T, E) = \text{Ok}(T) + \text{Err}(E)$$

**Rust实现**：
```rust
// Result类型
fn safe_divide(x: f64, y: f64) -> Result<f64, &'static str> {
    if y == 0.0 {
        Err("Division by zero")
    } else {
        Ok(x / y)
    }
}

// 自定义错误类型
#[derive(Debug)]
enum ValidationError {
    DivisionByZero,
    NegativeNumber,
}

fn safe_divide_with_validation(x: f64, y: f64) -> Result<f64, ValidationError> {
    if y == 0.0 {
        Err(ValidationError::DivisionByZero)
    } else {
        let result = x / y;
        if result < 0.0 {
            Err(ValidationError::NegativeNumber)
        } else {
            Ok(result)
        }
    }
}

// 错误处理链
fn error_handling_chain(x: f64, y: f64) -> Result<f64, ValidationError> {
    let result = safe_divide_with_validation(x, y)?;
    Ok(result)
}

// 使用?操作符
fn process_file() -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string("file.txt")?;
    Ok(content)
}

// 错误处理模式匹配
fn handle_errors() {
    match safe_divide(10.0, 0.0) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 5. 性能对比

#### Haskell性能特性

**形式化定义**：
Haskell的性能基于惰性求值、垃圾回收和编译器优化。

数学表示为：
$$\text{Performance}(Haskell) = \text{LazyEval} + \text{GC} + \text{CompilerOpt}$$

**Haskell实现**：
```haskell
-- 惰性求值优化
lazyOptimization :: [Integer]
lazyOptimization = take 1000 [1..]  -- 只计算需要的部分

-- 严格求值优化
strictOptimization :: [Int] -> Int
strictOptimization = foldl' (+) 0  -- 避免空间泄漏

-- 内存优化
memoryOptimization :: [Int] -> [Int]
memoryOptimization = 
    foldr (\x acc -> if x > 0 then x*2 : acc else acc) []

-- 并行优化
parallelOptimization :: [Int] -> Int
parallelOptimization xs = 
    let (left, right) = splitAt (length xs `div` 2) xs
        leftSum = sum left
        rightSum = sum right
    in leftSum `par` rightSum `pseq` (leftSum + rightSum)

-- 编译时优化
{-# INLINE optimizedFunction #-}
optimizedFunction :: Int -> Int
optimizedFunction x = x * 2 + 1
```

#### Rust性能特性

**形式化定义**：
Rust的性能基于零成本抽象、所有权系统和LLVM优化。

数学表示为：
$$\text{Performance}(Rust) = \text{ZeroCost} + \text{Ownership} + \text{LLVM}$$

**Rust实现**：
```rust
// 零成本抽象
fn zero_cost_abstraction() {
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();
}

// 所有权优化
fn ownership_optimization() {
    let mut data = vec![1, 2, 3, 4, 5];
    data.push(6); // 原地修改，无额外分配
}

// 内联优化
#[inline]
fn optimized_function(x: i32) -> i32 {
    x * 2 + 1
}

// 内存布局优化
#[repr(C)]
struct OptimizedStruct {
    a: u32,
    b: u64,
    c: u32,
}

// 无分配迭代器
fn no_allocation_iteration() {
    let numbers = [1, 2, 3, 4, 5];
    for &num in numbers.iter() {
        println!("{}", num);
    }
}

// SIMD优化
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[cfg(target_arch = "x86_64")]
unsafe fn simd_optimization(a: &[f32], b: &[f32], result: &mut [f32]) {
    for i in (0..a.len()).step_by(4) {
        let va = _mm_loadu_ps(&a[i]);
        let vb = _mm_loadu_ps(&b[i]);
        let vr = _mm_add_ps(va, vb);
        _mm_storeu_ps(&mut result[i], vr);
    }
}
```

### 6. 生态系统对比

#### Haskell生态系统

**包管理器**：Cabal, Stack
**主要库**：GHC, Hackage, Stackage

```haskell
-- Cabal文件示例
-- example.cabal
name:                example
version:             0.1.0.0
build-depends:       base >= 4.7 && < 5
                     , text
                     , aeson
                     , http-client

-- 常用库
import Data.Text (Text)
import Data.Aeson (FromJSON, ToJSON)
import Network.HTTP.Client

-- Web框架
import Web.Scotty

main :: IO ()
main = scotty 3000 $ do
    get "/" $ text "Hello, Haskell!"
    get "/users" $ json [("name", "Alice"), ("age", 30)]
```

#### Rust生态系统

**包管理器**：Cargo
**主要库**：crates.io, std库

```rust
// Cargo.toml
[package]
name = "example"
version = "0.1.0"
edition = "2021"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
axum = "0.6"

// 常用库
use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;
use axum::{routing::get, Router};

// Web框架
#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, Rust!" }))
        .route("/users", get(get_users));
    
    let listener = TcpListener::bind("127.0.0.1:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

#[derive(Serialize)]
struct User {
    name: String,
    age: u32,
}

async fn get_users() -> axum::Json<Vec<User>> {
    axum::Json(vec![
        User { name: "Alice".to_string(), age: 30 },
    ])
}
```

## 📊 性能基准对比

### 计算密集型任务

```haskell
-- Haskell: 斐波那契数列
fibonacci :: Integer -> Integer
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci (n-1) + fibonacci (n-2)

-- 性能测试
main :: IO ()
main = do
    start <- getCurrentTime
    let result = fibonacci 40
    end <- getCurrentTime
    putStrLn $ "Haskell: " ++ show (diffUTCTime end start)
```

```rust
// Rust: 斐波那契数列
fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

// 性能测试
use std::time::Instant;

fn main() {
    let start = Instant::now();
    let result = fibonacci(40);
    let duration = start.elapsed();
    println!("Rust: {:?}", duration);
}
```

### 内存使用对比

```haskell
-- Haskell: 内存使用（惰性求值）
memoryUsage :: IO ()
memoryUsage = do
    let largeList = [1..1000000]
    let sum = foldl' (+) 0 largeList
    putStrLn $ "Sum: " ++ show sum
```

```rust
// Rust: 内存使用（严格求值）
fn memory_usage() {
    let large_vec: Vec<i32> = (1..1_000_000).collect();
    let sum: i32 = large_vec.iter().sum();
    println!("Sum: {}", sum);
}
```

## 🎯 选择指南

### 选择Haskell的场景

1. **函数式编程**：需要纯函数式编程范式
2. **快速原型**：需要快速开发原型和概念验证
3. **数学计算**：涉及复杂的数学计算和算法
4. **类型安全**：需要强大的类型系统保证
5. **并发编程**：需要STM和轻量级线程

### 选择Rust的场景

1. **系统编程**：需要直接控制内存和硬件
2. **性能关键**：需要零成本抽象和最佳性能
3. **内存安全**：需要编译时内存安全保证
4. **并发安全**：需要线程安全保证
5. **嵌入式**：需要资源受限环境

## 🔗 相关链接

- [与Scala对比](02-Haskell-vs-Scala.md)
- [与OCaml对比](03-Haskell-vs-OCaml.md)
- [与F#对比](04-Haskell-vs-FSharp.md)
- [语言特性对比](05-Language-Features-Comparison.md)
- [Haskell基础](../01-Basic-Concepts/README.md)
- [类型体系](../05-Type-System/README.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0  
**状态**: 完成 