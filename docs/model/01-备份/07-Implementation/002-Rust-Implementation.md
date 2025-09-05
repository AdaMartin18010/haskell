# Rust实现

## 核心特性

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
    // let r3 = &mut s; // 编译错误
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

## 工具

- **rustc**: 编译器
- **cargo**: 包管理器
- **clippy**: 代码检查

---

**相关链接**：

- [Haskell实现](./001-Haskell-Implementation.md)
- [Lean实现](./003-Lean-Implementation.md)
