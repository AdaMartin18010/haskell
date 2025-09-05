# Rust深度解析

## 核心概念

### 所有权系统

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1; // 所有权转移
    // println!("{}", s1); // 编译错误
}
```

### 借用检查

```rust
fn main() {
    let mut s = String::from("hello");
    let r1 = &s; // 不可变借用
    let r2 = &s; // 不可变借用
    // let r3 = &mut s; // 编译错误：不能同时有可变和不可变借用
}
```

### 生命周期

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

## 类型系统

### 特征（Traits）

```rust
trait Drawable {
    fn draw(&self) -> String;
}

struct Circle {
    radius: f64,
}

impl Drawable for Circle {
    fn draw(&self) -> String {
        format!("Circle with radius {}", self.radius)
    }
}
```

### 泛型

```rust
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

## 内存管理

### 零成本抽象

```rust
// 编译时检查，运行时零开销
fn main() {
    let v = vec![1, 2, 3];
    let sum: i32 = v.iter().sum(); // 编译时优化
}
```

### 智能指针

```rust
use std::rc::Rc;

fn main() {
    let data = Rc::new(vec![1, 2, 3]);
    let data_clone = Rc::clone(&data); // 引用计数增加
    println!("Count: {}", Rc::strong_count(&data));
}
```

## 并发编程

### 线程安全

```rust
use std::thread;
use std::sync::{Arc, Mutex};

fn main() {
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
}
```

### 异步编程

```rust
use tokio;

#[tokio::main]
async fn main() {
    let handle = tokio::spawn(async {
        println!("Hello from async task");
    });
    
    handle.await.unwrap();
}
```

## 错误处理

### Result类型

```rust
use std::fs::File;
use std::io::{self, Read};

fn read_file() -> Result<String, io::Error> {
    let mut file = File::open("hello.txt")?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}
```

### Option类型

```rust
fn divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 {
        None
    } else {
        Some(a / b)
    }
}
```

## 宏系统

### 声明宏

```rust
macro_rules! vec {
    ( $( $x:expr ),* ) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

fn main() {
    let v = vec![1, 2, 3];
}
```

### 过程宏

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn hello(input: TokenStream) -> TokenStream {
    // 宏实现
    TokenStream::new()
}
```

## 应用场景

- **系统编程**: 操作系统、驱动程序
- **Web开发**: WebAssembly、后端服务
- **嵌入式**: 微控制器、实时系统
- **高性能计算**: 数值计算、并行处理

---

**相关链接**：

- [语言范式](./001-Language-Paradigms.md)
- [语言对比](./002-Language-Comparison.md)
