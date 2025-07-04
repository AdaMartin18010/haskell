# 001 装饰器模式

## 1. 理论基础

装饰器模式是一种结构型设计模式，允许向对象动态添加新功能而不改变其结构。通过组合和委托实现功能扩展。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Component a where
  operation :: a -> String

data Coffee = Coffee deriving Show
data MilkDecorator = MilkDecorator Coffee deriving Show
data SugarDecorator = SugarDecorator Coffee deriving Show
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 基础组件
instance Component Coffee where
  operation Coffee = "Simple Coffee"

-- 装饰器实现
instance Component MilkDecorator where
  operation (MilkDecorator coffee) = operation coffee ++ ", Milk"

instance Component SugarDecorator where
  operation (SugarDecorator coffee) = operation coffee ++ ", Sugar"

-- 使用示例
main :: IO ()
main = do
  let coffee = Coffee
  let milkCoffee = MilkDecorator coffee
  let sweetMilkCoffee = SugarDecorator milkCoffee
  print $ operation sweetMilkCoffee
```

### Rust实现

```rust
// 基础组件trait
trait Component {
    fn operation(&self) -> String;
}

// 具体组件
struct Coffee;

impl Component for Coffee {
    fn operation(&self) -> String {
        "Simple Coffee".to_string()
    }
}

// 装饰器基类
struct Decorator<T: Component> {
    component: T,
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        self.component.operation()
    }
}

// 具体装饰器
struct MilkDecorator<T: Component> {
    component: T,
}

impl<T: Component> Component for MilkDecorator<T> {
    fn operation(&self) -> String {
        format!("{}, Milk", self.component.operation())
    }
}
```

### Lean实现

```lean
-- 组件类型
inductive Component where
  | Coffee : Component
  | MilkDecorator : Component → Component
  | SugarDecorator : Component → Component

-- 操作函数
def operation : Component → String
  | Component.Coffee => "Simple Coffee"
  | Component.MilkDecorator c => operation c ++ ", Milk"
  | Component.SugarDecorator c => operation c ++ ", Sugar"

-- 装饰器性质定理
theorem decorator_preserves_base : 
  ∀ c : Component, operation (MilkDecorator c) = operation c ++ ", Milk" :=
  by simp [operation]
```

## 4. 工程实践

- 动态功能扩展
- 组合优于继承
- 单一职责原则
- 开闭原则

## 5. 性能优化

- 避免过度装饰
- 缓存装饰结果
- 延迟初始化

## 6. 应用场景

- 日志记录
- 缓存包装
- 权限检查
- 事务管理

## 7. 最佳实践

- 保持装饰器轻量
- 避免装饰器链过长
- 考虑性能影响
- 使用组合而非继承
