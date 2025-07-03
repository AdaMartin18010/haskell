# Rust 结构型模式多实现对比

## 1. 适配器模式（Adapter Pattern）

### 异步实现

```rust
trait Target {
    fn request(&self) -> String;
}

struct Adaptee;
impl Adaptee {
    async fn specific_request(&self) -> String {
        "Adaptee's specific request".to_string()
    }
}

struct Adapter {
    adaptee: Adaptee,
}
impl Target for Adapter {
    fn request(&self) -> String {
        futures::executor::block_on(self.adaptee.specific_request())
    }
}

#[tokio::main]
async fn main() {
    let adaptee = Adaptee;
    let adapter = Adapter { adaptee };
    println!("{}", adapter.request());
}
```

### 同步实现

```rust
trait Target {
    fn request(&self) -> String;
}

struct Adaptee;
impl Adaptee {
    fn specific_request(&self) -> String {
        "Adaptee's specific request".to_string()
    }
}

struct Adapter {
    adaptee: Adaptee,
}
impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}

fn main() {
    let adaptee = Adaptee;
    let adapter = Adapter { adaptee };
    println!("{}", adapter.request());
}
```

### 多线程实现

```rust
trait Target {
    fn request(&self);
}

struct Adaptee;
impl Adaptee {
    fn specific_request(&self) {
        println!("Called specific request.");
    }
}

struct Adapter {
    adaptee: Adaptee,
}
impl Target for Adapter {
    fn request(&self) {
        self.adaptee.specific_request();
    }
}

#[tokio::main]
async fn main() {
    let adaptee = Adaptee;
    let adapter = Adapter { adaptee };
    adapter.request(); // 输出: Called specific request.
}
```

---

## 2. 桥接模式（Bridge Pattern）

### 异步实现

```rust
trait Implementor {
    fn operation_impl(&self) -> String;
}

struct ConcreteImplementorA;
impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorA".to_string()
    }
}
struct ConcreteImplementorB;
impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorB".to_string()
    }
}
struct Abstraction {
    implementor: Box<dyn Implementor>,
}
impl Abstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Abstraction { implementor }
    }
    async fn operation(&self) -> String {
        self.implementor.operation_impl()
    }
}
#[tokio::main]
async fn main() {
    let implementor_a = Box::new(ConcreteImplementorA);
    let abstraction_a = Abstraction::new(implementor_a);
    println!("{}", abstraction_a.operation().await);
    let implementor_b = Box::new(ConcreteImplementorB);
    let abstraction_b = Abstraction::new(implementor_b);
    println!("{}", abstraction_b.operation().await);
}
```

### 同步实现

```rust
trait Implementor {
    fn operation_impl(&self) -> String;
}
struct ConcreteImplementorA;
impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorA".to_string()
    }
}
struct ConcreteImplementorB;
impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        "ConcreteImplementorB".to_string()
    }
}
struct Abstraction {
    implementor: Box<dyn Implementor>,
}
impl Abstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Abstraction { implementor }
    }
    fn operation(&self) -> String {
        self.implementor.operation_impl()
    }
}
fn main() {
    let implementor_a = Box::new(ConcreteImplementorA);
    let abstraction_a = Abstraction::new(implementor_a);
    println!("{}", abstraction_a.operation());
    let implementor_b = Box::new(ConcreteImplementorB);
    let abstraction_b = Abstraction::new(implementor_b);
    println!("{}", abstraction_b.operation());
}
```

### 多线程实现

```rust
trait Implementor {
    fn operation_impl(&self);
}
struct ConcreteImplementorA;
impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) {
        println!("ConcreteImplementorA operation.");
    }
}
struct ConcreteImplementorB;
impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) {
        println!("ConcreteImplementorB operation.");
    }
}
struct Abstraction {
    implementor: Box<dyn Implementor>,
}
impl Abstraction {
    fn new(implementor: Box<dyn Implementor>) -> Self {
        Abstraction { implementor }
    }
    fn operation(&self) {
        self.implementor.operation_impl();
    }
}
#[tokio::main]
async fn main() {
    let implementor_a = Box::new(ConcreteImplementorA);
    let implementor_b = Box::new(ConcreteImplementorB);
    let abstraction_a = Abstraction::new(implementor_a);
    let abstraction_b = Abstraction::new(implementor_b);
    abstraction_a.operation();
    abstraction_b.operation();
}
```

---

（后续可继续补充组合、装饰器、外观等模式的多实现代码）

# Haskell 典型实现片段

## 类型系统与数据结构

```haskell
data Tree a = Empty | Node a (Tree a) (Tree a)
```

## 惰性求值

```haskell
naturals :: [Integer]
naturals = [0..]

take 5 naturals -- [0,1,2,3,4]
```

## 高阶函数与组合

```haskell
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
```

## Maybe类型与模式匹配

```haskell
data Maybe a = Nothing | Just a

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x
```

---

（可按需在各结构型模式下补充更细致的Haskell实现）
