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

# Lean 典型实现片段

## 依赖类型与结构体

```lean
-- 依赖类型
def Vector (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × Vector α n

-- 结构体
structure Point where
  x : Nat
  y : Nat
```

## 适配器模式

```lean
-- 目标接口
def Target := String → String

-- 被适配的类
def Adaptee := Nat → String

-- 适配器
def Adapter (adaptee : Adaptee) : Target := λ s => adaptee (s.length)

-- 使用
def adaptee : Adaptee := λ n => "Number: " ++ toString n
def target : Target := Adapter adaptee
```

## 桥接模式

```lean
-- 实现接口
def Implementation := String → String

-- 抽象接口
def Abstraction := Implementation → String → String

-- 具体实现
def ConcreteImplementation : Implementation := λ s => "Concrete: " ++ s

-- 具体抽象
def RefinedAbstraction : Abstraction := λ impl s => impl s ++ " (refined)"
```

## 组合模式

```lean
-- 组件接口
inductive Component where
  | Leaf (name : String) : Component
  | Composite (name : String) (children : List Component) : Component

-- 操作
def Component.operation : Component → String
  | Component.Leaf name => "Leaf: " ++ name
  | Component.Composite name children => 
    "Composite: " ++ name ++ " [" ++ 
    String.join (List.map operation children) ++ "]"
```

## 装饰器模式

```lean
-- 组件接口
def Component := String → String

-- 具体组件
def ConcreteComponent : Component := λ s => "Component: " ++ s

-- 装饰器
def Decorator (component : Component) : Component := 
  λ s => "Decorated(" ++ component s ++ ")"

-- 使用
def decorated : Component := Decorator ConcreteComponent
```

## 外观模式

```lean
-- 子系统
def SubsystemA := String → String
def SubsystemB := String → String
def SubsystemC := String → String

-- 外观
structure Facade where
  subsystemA : SubsystemA
  subsystemB : SubsystemB
  subsystemC : SubsystemC

-- 简化接口
def Facade.operation (f : Facade) (s : String) : String :=
  let result1 := f.subsystemA s
  let result2 := f.subsystemB result1
  f.subsystemC result2
```

## 享元模式

```lean
-- 享元接口
def Flyweight := String → String

-- 享元工厂
def FlyweightFactory := String → Flyweight

-- 具体享元
def ConcreteFlyweight (intrinsic : String) : Flyweight :=
  λ extrinsic => "Flyweight(" ++ intrinsic ++ ", " ++ extrinsic ++ ")"

-- 工厂实现
def createFlyweight : FlyweightFactory := λ key => ConcreteFlyweight key
```

## 代理模式

```lean
-- 主题接口
def Subject := String → String

-- 真实主题
def RealSubject : Subject := λ s => "Real: " ++ s

-- 代理
def Proxy (real : Subject) : Subject := 
  λ s => "Proxy: " ++ real s

-- 使用
def proxy : Subject := Proxy RealSubject
```

## 证明系统

```lean
-- 策略语言
theorem proxy_preserves_operation (s : String) : 
  Proxy RealSubject s = "Proxy: Real: " ++ s := by simp

-- 自动化证明
theorem decorator_composition (c : Component) (s : String) :
  Decorator (Decorator c) s = "Decorated(Decorated(" ++ c s ++ "))" := by simp
```

---

（可按需在各模式下补充更细致的Lean实现）
