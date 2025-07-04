# 003 桥接模式

## 1. 理论基础

桥接模式是一种结构型设计模式，将抽象与实现分离，使它们可以独立变化。通过组合而非继承实现解耦。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Implementor a where
  operationImpl :: a -> String

class Abstraction a where
  operation :: a -> String

-- 具体实现
data ConcreteImplementorA = ConcreteImplementorA
data ConcreteImplementorB = ConcreteImplementorB

-- 抽象类
data RefinedAbstraction impl = RefinedAbstraction impl
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 实现接口
class Implementor a where
  operationImpl :: a -> String

instance Implementor ConcreteImplementorA where
  operationImpl ConcreteImplementorA = "Concrete A"

instance Implementor ConcreteImplementorB where
  operationImpl ConcreteImplementorB = "Concrete B"

-- 抽象接口
class Abstraction a where
  operation :: a -> String

instance (Implementor impl) => Abstraction (RefinedAbstraction impl) where
  operation (RefinedAbstraction impl) = "Refined: " ++ operationImpl impl

-- 使用示例
main :: IO ()
main = do
  let implA = ConcreteImplementorA
  let implB = ConcreteImplementorB
  let refinedA = RefinedAbstraction implA
  let refinedB = RefinedAbstraction implB
  print $ operation refinedA
  print $ operation refinedB
```

### Rust实现

```rust
// 实现接口
trait Implementor {
    fn operation_impl(&self) -> String;
}

struct ConcreteImplementorA;
struct ConcreteImplementorB;

impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        "Concrete A".to_string()
    }
}

impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        "Concrete B".to_string()
    }
}

// 抽象类
struct RefinedAbstraction<T: Implementor> {
    implementor: T,
}

impl<T: Implementor> RefinedAbstraction<T> {
    fn operation(&self) -> String {
        format!("Refined: {}", self.implementor.operation_impl())
    }
}
```

### Lean实现

```lean
-- 实现类型
inductive Implementor where
  | ConcreteA : Implementor
  | ConcreteB : Implementor

-- 实现函数
def operationImpl : Implementor → String
  | Implementor.ConcreteA => "Concrete A"
  | Implementor.ConcreteB => "Concrete B"

-- 抽象类型
def Abstraction := Implementor

-- 抽象操作
def operation (a : Abstraction) : String :=
  "Refined: " ++ operationImpl a

-- 桥接正确性定理
theorem bridge_correctness :
  ∀ impl : Implementor, operation impl = "Refined: " ++ operationImpl impl :=
  by simp [operation, operationImpl]
```

## 4. 工程实践

- 抽象与实现分离
- 避免继承爆炸
- 运行时绑定
- 扩展性设计

## 5. 性能优化

- 减少对象创建
- 缓存桥接结果
- 延迟初始化

## 6. 应用场景

- 图形渲染引擎
- 数据库连接池
- 消息队列实现
- 网络协议栈

## 7. 最佳实践

- 保持桥接简单
- 避免过度抽象
- 考虑性能影响
- 文档化桥接关系
