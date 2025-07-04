# 005 外观模式

## 1. 理论基础

外观模式是一种结构型设计模式，为子系统中的一组接口提供一个统一的高层接口。简化客户端与复杂子系统的交互。

## 2. 接口设计

```haskell
-- Haskell接口设计
class SubsystemA a where
  operationA :: a -> String

class SubsystemB a where
  operationB :: a -> String

class SubsystemC a where
  operationC :: a -> String

-- 外观类
data Facade = Facade SubsystemA SubsystemB SubsystemC
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 子系统A
data SubsystemA = SubsystemA deriving Show

instance SubsystemA SubsystemA where
  operationA SubsystemA = "SubsystemA operation"

-- 子系统B
data SubsystemB = SubsystemB deriving Show

instance SubsystemB SubsystemB where
  operationB SubsystemB = "SubsystemB operation"

-- 子系统C
data SubsystemC = SubsystemC deriving Show

instance SubsystemC SubsystemC where
  operationC SubsystemC = "SubsystemC operation"

-- 外观类
data Facade = Facade SubsystemA SubsystemB SubsystemC

-- 外观操作
facadeOperation :: Facade -> String
facadeOperation (Facade a b c) = 
  operationA a ++ " -> " ++ operationB b ++ " -> " ++ operationC c

-- 使用示例
main :: IO ()
main = do
  let facade = Facade SubsystemA SubsystemB SubsystemC
  print $ facadeOperation facade
```

### Rust实现

```rust
// 子系统A
struct SubsystemA;

impl SubsystemA {
    fn operation_a(&self) -> String {
        "SubsystemA operation".to_string()
    }
}

// 子系统B
struct SubsystemB;

impl SubsystemB {
    fn operation_b(&self) -> String {
        "SubsystemB operation".to_string()
    }
}

// 子系统C
struct SubsystemC;

impl SubsystemC {
    fn operation_c(&self) -> String {
        "SubsystemC operation".to_string()
    }
}

// 外观类
struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC,
}

impl Facade {
    fn new() -> Self {
        Facade {
            subsystem_a: SubsystemA,
            subsystem_b: SubsystemB,
            subsystem_c: SubsystemC,
        }
    }
    
    fn operation(&self) -> String {
        format!("{} -> {} -> {}", 
            self.subsystem_a.operation_a(),
            self.subsystem_b.operation_b(),
            self.subsystem_c.operation_c())
    }
}
```

### Lean实现

```lean
-- 子系统类型
def SubsystemA := String
def SubsystemB := String
def SubsystemC := String

-- 子系统操作
def operationA : SubsystemA → String := id
def operationB : SubsystemB → String := id
def operationC : SubsystemC → String := id

-- 外观类型
def Facade := SubsystemA × SubsystemB × SubsystemC

-- 外观操作
def facadeOperation : Facade → String
  | (a, b, c) => operationA a ++ " -> " ++ operationB b ++ " -> " ++ operationC c

-- 外观简化定理
theorem facade_simplifies_interface :
  ∀ f : Facade, facadeOperation f ≠ "" :=
  by simp [facadeOperation, operationA, operationB, operationC]
```

## 4. 工程实践

- 简化复杂接口
- 降低耦合度
- 统一错误处理
- 配置管理

## 5. 性能优化

- 延迟初始化
- 缓存子系统状态
- 异步操作

## 6. 应用场景

- API网关
- 数据库连接池
- 日志系统
- 配置管理

## 7. 最佳实践

- 保持外观简单
- 避免过度抽象
- 考虑性能影响
- 文档化接口
