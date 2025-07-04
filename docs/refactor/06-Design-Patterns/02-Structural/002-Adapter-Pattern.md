# 002 适配器模式

## 1. 理论基础

适配器模式是一种结构型设计模式，允许不兼容的接口协同工作。通过包装现有类，使其接口符合客户端期望。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Target a where
  request :: a -> String

class Adaptee a where
  specificRequest :: a -> String

-- 适配器类型
data Adapter = Adapter Adaptee
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 目标接口
class Target a where
  request :: a -> String

-- 被适配的类
data Adaptee = Adaptee deriving Show

instance Adaptee Adaptee where
  specificRequest Adaptee = "Specific request"

-- 适配器实现
instance Target Adapter where
  request (Adapter adaptee) = "Adapter: " ++ specificRequest adaptee

-- 使用示例
main :: IO ()
main = do
  let adaptee = Adaptee
  let adapter = Adapter adaptee
  print $ request adapter
```

### Rust实现

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配的类
struct Adaptee;

impl Adaptee {
    fn specific_request(&self) -> String {
        "Specific request".to_string()
    }
}

// 适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        format!("Adapter: {}", self.adaptee.specific_request())
    }
}
```

### Lean实现

```lean
-- 目标接口
def Target := String → String

-- 被适配的类
def Adaptee := String

def specificRequest (a : Adaptee) : String :=
  "Specific request"

-- 适配器函数
def adapter (a : Adaptee) : Target :=
  fun _ => "Adapter: " ++ specificRequest a

-- 适配器正确性定理
theorem adapter_correctness :
  ∀ a : Adaptee, adapter a "" = "Adapter: " ++ specificRequest a :=
  by simp [adapter, specificRequest]
```

## 4. 工程实践

- 接口兼容性
- 遗留系统集成
- 第三方库适配
- 版本兼容性

## 5. 性能优化

- 避免过度包装
- 缓存适配结果
- 直接映射优化

## 6. 应用场景

- 数据库适配器
- API版本兼容
- 硬件接口适配
- 第三方服务集成

## 7. 最佳实践

- 保持适配器简单
- 避免深层嵌套
- 考虑性能开销
- 文档化适配逻辑
