# 代理模式（Proxy Pattern）

## 概述

代理模式是一种结构型设计模式，为其他对象提供一种代理以控制对这个对象的访问。常用于远程代理、虚拟代理、安全代理等场景。

## 理论基础

- **间接访问**：通过代理对象间接访问目标对象。
- **职责分离**：代理与被代理对象分离关注点。
- **增强控制**：可添加访问控制、缓存、延迟加载等。

## Rust实现示例

```rust
trait Subject {
    fn request(&self) -> String;
}
struct RealSubject;
impl Subject for RealSubject {
    fn request(&self) -> String { "真实请求".to_string() }
}
struct Proxy {
    real: RealSubject,
}
impl Subject for Proxy {
    fn request(&self) -> String {
        format!("代理前置处理 -> {}", self.real.request())
    }
}
fn main() {
    let proxy = Proxy { real: RealSubject };
    println!("{}", proxy.request());
}
```

## Haskell实现示例

```haskell
class Subject a where
    request :: a -> String

data RealSubject = RealSubject
instance Subject RealSubject where
    request _ = "真实请求"

data Proxy = Proxy RealSubject
instance Subject Proxy where
    request (Proxy real) = "代理前置处理 -> " ++ request real

main = putStrLn $ request (Proxy RealSubject)
```

## Lean实现思路

```lean
class Subject (α : Type) where
  request : α → String

structure RealSubject
instance : Subject RealSubject where
  request _ := "真实请求"

structure Proxy where
  real : RealSubject

instance : Subject Proxy where
  request p := "代理前置处理 -> " ++ Subject.request p.real
```

## 应用场景

- 远程代理（RPC、分布式对象）
- 虚拟代理（延迟加载）
- 保护代理（权限控制）
- 智能引用（引用计数、缓存）

## 最佳实践

- 明确代理与真实对象职责
- 控制代理层级，避免性能损耗
- 结合依赖注入和AOP
