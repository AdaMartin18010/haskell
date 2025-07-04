# 008 策略模式

## 1. 理论基础

策略模式是一种行为型设计模式，定义一系列算法，将每一个算法封装起来，并使它们可以互换。策略模式让算法独立于使用它的客户而变化。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Strategy a where
  algorithm :: a -> Int -> Int -> Int

-- 具体策略
data AddStrategy = AddStrategy
data SubtractStrategy = SubtractStrategy
data MultiplyStrategy = MultiplyStrategy
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 策略接口
class Strategy a where
  algorithm :: a -> Int -> Int -> Int

-- 具体策略
data AddStrategy = AddStrategy deriving Show
data SubtractStrategy = SubtractStrategy deriving Show
data MultiplyStrategy = MultiplyStrategy deriving Show

instance Strategy AddStrategy where
  algorithm AddStrategy a b = a + b

instance Strategy SubtractStrategy where
  algorithm SubtractStrategy a b = a - b

instance Strategy MultiplyStrategy where
  algorithm MultiplyStrategy a b = a * b

-- 上下文
data Context = Context (Maybe Strategy) deriving Show

-- 上下文操作
setStrategy :: Context -> Strategy -> Context
setStrategy (Context _) strategy = Context (Just strategy)

executeStrategy :: Context -> Int -> Int -> Maybe Int
executeStrategy (Context Nothing) _ _ = Nothing
executeStrategy (Context (Just strategy)) a b = Just (algorithm strategy a b)

-- 使用示例
main :: IO ()
main = do
  let context = Context Nothing
  let context' = setStrategy context AddStrategy
  case executeStrategy context' 5 3 of
    Just result -> print result
    Nothing -> putStrLn "No strategy set"
```

### Rust实现

```rust
// 策略trait
trait Strategy {
    fn algorithm(&self, a: i32, b: i32) -> i32;
}

// 具体策略
struct AddStrategy;

impl Strategy for AddStrategy {
    fn algorithm(&self, a: i32, b: i32) -> i32 {
        a + b
    }
}

struct SubtractStrategy;

impl Strategy for SubtractStrategy {
    fn algorithm(&self, a: i32, b: i32) -> i32 {
        a - b
    }
}

struct MultiplyStrategy;

impl Strategy for MultiplyStrategy {
    fn algorithm(&self, a: i32, b: i32) -> i32 {
        a * b
    }
}

// 上下文
struct Context {
    strategy: Option<Box<dyn Strategy>>,
}

impl Context {
    fn new() -> Self {
        Context { strategy: None }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = Some(strategy);
    }
    
    fn execute_strategy(&self, a: i32, b: i32) -> Option<i32> {
        self.strategy.as_ref().map(|s| s.algorithm(a, b))
    }
}
```

### Lean实现

```lean
-- 策略类型
def Strategy := ℕ → ℕ → ℕ

-- 具体策略
def addStrategy : Strategy := fun a b => a + b
def subtractStrategy : Strategy := fun a b => a - b
def multiplyStrategy : Strategy := fun a b => a * b

-- 上下文类型
def Context := Strategy

-- 执行策略
def executeStrategy : Context → ℕ → ℕ → ℕ :=
  fun strategy a b => strategy a b

-- 策略模式正确性定理
theorem strategy_correctness :
  ∀ strategy : Strategy, ∀ a b : ℕ,
  executeStrategy strategy a b = strategy a b :=
  by simp [executeStrategy]
```

## 4. 工程实践

- 算法选择
- 运行时配置
- 插件系统
- 条件分支

## 5. 性能优化

- 策略缓存
- 编译时选择
- 内存管理
- 延迟加载

## 6. 应用场景

- 排序算法
- 压缩算法
- 支付方式
- 验证策略

## 7. 最佳实践

- 保持策略简单
- 避免策略爆炸
- 考虑性能影响
- 实现策略验证
