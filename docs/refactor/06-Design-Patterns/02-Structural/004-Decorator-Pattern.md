# 装饰器模式（Decorator Pattern）

## 概述

装饰器模式是一种结构型设计模式，允许在不改变对象结构的前提下，动态地为对象添加额外的功能。它通过将对象包装在装饰器类中，实现功能的扩展和增强。

## 理论基础

- **开放封闭原则**：对扩展开放，对修改关闭。
- **对象组合**：通过组合而非继承扩展功能。
- **递归包装**：支持多层装饰，灵活叠加功能。

## Rust实现示例

```rust
trait Component {
    fn operation(&self) -> String;
}

struct ConcreteComponent;
impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "核心功能".to_string()
    }
}

struct Decorator<T: Component> {
    component: T,
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        format!("装饰({})", self.component.operation())
    }
}

fn main() {
    let core = ConcreteComponent;
    let decorated = Decorator { component: core };
    println!("{}", decorated.operation());
}
```

## Haskell实现示例

```haskell
class Component a where
    operation :: a -> String

data ConcreteComponent = ConcreteComponent
instance Component ConcreteComponent where
    operation _ = "核心功能"

data Decorator a = Decorator a
instance Component a => Component (Decorator a) where
    operation (Decorator c) = "装饰(" ++ operation c ++ ")"

main = putStrLn $ operation (Decorator ConcreteComponent)
```

## Lean实现思路

```lean
class Component (α : Type) where
  operation : α → String

structure ConcreteComponent
instance : Component ConcreteComponent where
  operation _ := "核心功能"

structure Decorator (α : Type) where
  component : α

instance [Component α] : Component (Decorator α) where
  operation d := "装饰(" ++ Component.operation d.component ++ ")"
```

## 应用场景

- 日志、权限、缓存等横切关注点
- 动态功能扩展
- UI组件样式叠加

## 最佳实践

- 控制装饰层数，避免过度嵌套
- 保持装饰器职责单一
- 结合依赖注入提升灵活性
