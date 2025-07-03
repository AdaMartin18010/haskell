# Rust 创建型模式多实现对比

## 1. 单例模式（Singleton Pattern）

### 通用/多线程实现

```rust
use std::sync::{Arc, Mutex};
use std::sync::Once;

struct Singleton {
    value: i32,
}

impl Singleton {
    fn instance() -> Arc<Mutex<Singleton>> {
        static mut SINGLETON: Option<Arc<Mutex<Singleton>>> = None;
        static ONCE: Once = Once::new();
        unsafe {
            ONCE.call_once(|| {
                let singleton = Singleton { value: 42 };
                SINGLETON = Some(Arc::new(Mutex::new(singleton)));
            });
            SINGLETON.clone().unwrap()
        }
    }
}

fn main() {
    let handles: Vec<_> = (0..5).map(|_| {
        std::thread::spawn(|| {
            let singleton = Singleton::instance();
            let mut instance = singleton.lock().unwrap();
            instance.value += 1;
            println!("Singleton value: {}", instance.value);
        })
    }).collect();
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 异步实现

```rust
use std::sync::{Arc, Mutex};
use tokio::sync::OnceCell;

struct Singleton {
    value: i32,
}

impl Singleton {
    async fn instance() -> Arc<Mutex<Singleton>> {
        static INSTANCE: OnceCell<Arc<Mutex<Singleton>>> = OnceCell::const_new();
        INSTANCE.get_or_init(async {
            Arc::new(Mutex::new(Singleton { value: 42 }))
        }).await.clone()
    }
}

#[tokio::main]
async fn main() {
    let singleton = Singleton::instance().await;
    let mut instance = singleton.lock().unwrap();
    instance.value += 1;
    println!("Singleton value: {}", instance.value);
}
```

### 同步实现

```rust
use std::sync::{Arc, Mutex};
use std::sync::Once;

struct Singleton {
    value: i32,
}

impl Singleton {
    fn instance() -> Arc<Mutex<Singleton>> {
        static mut SINGLETON: Option<Arc<Mutex<Singleton>>> = None;
        static ONCE: Once = Once::new();
        unsafe {
            ONCE.call_once(|| {
                let singleton = Singleton { value: 42 };
                SINGLETON = Some(Arc::new(Mutex::new(singleton)));
            });
            SINGLETON.clone().unwrap()
        }
    }
}

fn main() {
    let singleton = Singleton::instance();
    let mut instance = singleton.lock().unwrap();
    instance.value += 1;
    println!("Singleton value: {}", instance.value);
}
```

---

## 2. 工厂方法模式（Factory Method Pattern）

### 通用/多线程实现

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Result of ConcreteProductA".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Result of ConcreteProductB".to_string()
    }
}

struct Creator;
impl Creator {
    fn factory_method(product_type: &str) -> Box<dyn Product> {
        match product_type {
            "A" => Box::new(ConcreteProductA),
            "B" => Box::new(ConcreteProductB),
            _ => panic!("Unknown product type"),
        }
    }
}

fn main() {
    let handles: Vec<_> = vec!["A", "B"].into_iter().map(|product_type| {
        std::thread::spawn(move || {
            let product = Creator::factory_method(product_type);
            println!("{}", product.operation());
        })
    }).collect();
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 异步实现

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Result of ConcreteProductA".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Result of ConcreteProductB".to_string()
    }
}

struct Creator;
impl Creator {
    async fn factory_method(product_type: &str) -> Box<dyn Product> {
        match product_type {
            "A" => Box::new(ConcreteProductA),
            "B" => Box::new(ConcreteProductB),
            _ => panic!("Unknown product type"),
        }
    }
}

#[tokio::main]
async fn main() {
    let product = Creator::factory_method("A").await;
    println!("{}", product.operation());
}
```

### 同步实现

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Result of ConcreteProductA".to_string()
    }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "Result of ConcreteProductB".to_string()
    }
}

struct Creator;
impl Creator {
    fn factory_method(product_type: &str) -> Box<dyn Product> {
        match product_type {
            "A" => Box::new(ConcreteProductA),
            "B" => Box::new(ConcreteProductB),
            _ => panic!("Unknown product type"),
        }
    }
}

fn main() {
    let product = Creator::factory_method("A");
    println!("{}", product.operation());
}
```

---

（后续可继续补充抽象工厂、建造者、原型、对象池等模式的多实现代码）

# Haskell 典型实现片段

## 类型系统与数据结构

```haskell
data Tree a = Empty | Node a (Tree a) (Tree a)

class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
```

## 惰性求值

```haskell
naturals :: [Integer]
naturals = [0..]

take 5 naturals -- [0,1,2,3,4]
```

## 并发编程（STM事务型内存）

```haskell
import Control.Concurrent.STM

type Account = TVar Double

transfer :: Account -> Account -> Double -> STM ()
transfer from to amount = do
  fromBalance <- readTVar from
  when (fromBalance >= amount) $ do
    writeTVar from (fromBalance - amount)
    toBalance <- readTVar to
    writeTVar to (toBalance + amount)
```

## 性能优化（严格求值）

```haskell
{-# LANGUAGE BangPatterns #-}

factorial :: Integer -> Integer
factorial n = go n 1
  where
    go 0 !acc = acc
    go n !acc = go (n - 1) (n * acc)
```

## QuickCheck属性测试

```haskell
import Test.QuickCheck

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs
```

---

（可按需在各模式下补充更细致的Haskell实现）

# Lean 典型实现片段

## 依赖类型与命题即类型

```lean
-- 依赖类型：类型可以依赖于值
def Vector (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × Vector α n

-- 命题即类型：证明就是程序
def Even : Nat → Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even n
```

## 工厂模式

```lean
-- 抽象产品
inductive Product where
  | ConcreteA : Product
  | ConcreteB : Product

-- 工厂接口
def Factory := Product → Product

-- 具体工厂
def ConcreteFactoryA : Factory := λ _ => Product.ConcreteA
def ConcreteFactoryB : Factory := λ _ => Product.ConcreteB

-- 使用
def createProduct (factory : Factory) : Product := factory Product.ConcreteA
```

## 单例模式

```lean
-- 单例类型
def Singleton := Unit

-- 单例实例
def singleton : Singleton := ()

-- 证明唯一性
theorem singleton_unique (x y : Singleton) : x = y := by
  cases x; cases y; rfl
```

## 建造者模式

```lean
-- 产品
structure ComplexObject where
  part1 : String
  part2 : Nat
  part3 : Bool

-- 建造者
structure Builder where
  part1 : String
  part2 : Nat
  part3 : Bool

-- 构建方法
def Builder.build (b : Builder) : ComplexObject :=
  { part1 := b.part1, part2 := b.part2, part3 := b.part3 }

-- 链式调用
def Builder.withPart1 (b : Builder) (p1 : String) : Builder :=
  { b with part1 := p1 }

def Builder.withPart2 (b : Builder) (p2 : Nat) : Builder :=
  { b with part2 := p2 }
```

## 原型模式

```lean
-- 原型接口
def Prototype (α : Type) := α → α

-- 具体原型
def StringPrototype : Prototype String := λ s => s ++ "_copy"

-- 深度复制
def deepCopy {α : Type} [Repr α] (x : α) : α := x
```

## 证明系统

```lean
-- 策略语言
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ n ih => rw [Nat.add_succ, ih]

-- 自动化证明
theorem simple_arithmetic : 2 + 2 = 4 := by simp
```

---

（可按需在各模式下补充更细致的Lean实现）
