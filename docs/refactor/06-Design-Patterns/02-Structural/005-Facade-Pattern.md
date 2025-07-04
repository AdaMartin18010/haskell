# 外观模式（Facade Pattern）

## 概述

外观模式是一种结构型设计模式，为子系统中的一组接口提供一个统一的高层接口，使子系统更易使用。它通过封装复杂子系统，简化客户端的调用。

## 理论基础

- **简化接口**：对外暴露统一入口，隐藏内部复杂性。
- **解耦依赖**：降低系统间耦合度。
- **分层架构**：常用于分层系统的接口整合。

## Rust实现示例

```rust
struct SubsystemA;
impl SubsystemA {
    fn do_a(&self) -> String { "A完成".to_string() }
}
struct SubsystemB;
impl SubsystemB {
    fn do_b(&self) -> String { "B完成".to_string() }
}
struct Facade {
    a: SubsystemA,
    b: SubsystemB,
}
impl Facade {
    fn new() -> Self { Self { a: SubsystemA, b: SubsystemB } }
    fn operation(&self) -> String {
        format!("{} + {}", self.a.do_a(), self.b.do_b())
    }
}
fn main() {
    let facade = Facade::new();
    println!("{}", facade.operation());
}
```

## Haskell实现示例

```haskell
data SubsystemA = SubsystemA
doA :: SubsystemA -> String
doA _ = "A完成"
data SubsystemB = SubsystemB
doB :: SubsystemB -> String
doB _ = "B完成"
data Facade = Facade SubsystemA SubsystemB
operation :: Facade -> String
operation (Facade a b) = doA a ++ " + " ++ doB b
main = putStrLn $ operation (Facade SubsystemA SubsystemB)
```

## Lean实现思路

```lean
structure SubsystemA
structure SubsystemB

def doA (_ : SubsystemA) : String := "A完成"
def doB (_ : SubsystemB) : String := "B完成"

structure Facade where
  a : SubsystemA
  b : SubsystemB

def operation (f : Facade) : String := doA f.a ++ " + " ++ doB f.b
```

## 应用场景

- 复杂子系统对外简化调用
- 旧系统迁移与兼容
- 分层架构统一入口

## 最佳实践

- 保持外观类简单稳定
- 不强行引入外观，避免过度封装
- 外观与子系统解耦
