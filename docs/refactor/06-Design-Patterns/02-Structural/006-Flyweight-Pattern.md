# 享元模式（Flyweight Pattern）

## 概述

享元模式是一种结构型设计模式，通过共享技术有效支持大量细粒度对象的复用，节省内存和提升性能。

## 理论基础

- **内部状态与外部状态分离**
- **对象池/缓存机制**
- **共享不可变对象**

## Rust实现示例

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

struct Flyweight {
    intrinsic: String,
}

struct FlyweightFactory {
    pool: Mutex<HashMap<String, Arc<Flyweight>>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        Self { pool: Mutex::new(HashMap::new()) }
    }
    fn get(&self, key: &str) -> Arc<Flyweight> {
        let mut pool = self.pool.lock().unwrap();
        pool.entry(key.to_string())
            .or_insert_with(|| Arc::new(Flyweight { intrinsic: key.to_string() }))
            .clone()
    }
}
fn main() {
    let factory = FlyweightFactory::new();
    let f1 = factory.get("A");
    let f2 = factory.get("A");
    assert!(Arc::ptr_eq(&f1, &f2));
}
```

## Haskell实现示例

```haskell
import qualified Data.Map as M
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

data Flyweight = Flyweight String
type Pool = IORef (M.Map String Flyweight)
pool :: Pool
pool = unsafePerformIO $ newIORef M.empty
getFlyweight :: String -> Flyweight
getFlyweight key = unsafePerformIO $ do
    m <- readIORef pool
    case M.lookup key m of
        Just f -> return f
        Nothing -> do
            let f = Flyweight key
            writeIORef pool (M.insert key f m)
            return f
```

## Lean实现思路

```lean
structure Flyweight where
  intrinsic : String

abbrev Pool := List (String × Flyweight)

def getFlyweight (key : String) (pool : Pool) : (Flyweight × Pool) :=
  match pool.find? (fun (k, _) => k = key) with
  | some (_, f) => (f, pool)
  | none =>
    let f := { intrinsic := key }
    (f, (key, f) :: pool)
```

## 应用场景

- 字符串常量池
- 图形对象复用
- 数据库连接池

## 最佳实践

- 只共享不可变状态
- 外部状态由客户端维护
- 结合对象池和缓存策略
