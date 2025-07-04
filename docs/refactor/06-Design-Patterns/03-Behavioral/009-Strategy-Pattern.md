# 策略模式（Strategy Pattern）

## 概述
策略模式是一种行为型设计模式，定义一系列算法，把它们封装起来，并且使它们可以互相替换。策略模式让算法独立于使用它的客户而变化。

## 理论基础
- **算法封装**：将算法封装在独立的策略类中
- **可替换性**：策略可以互相替换
- **扩展性**：易于添加新的策略

## Rust实现示例
```rust
trait Strategy {
    fn algorithm(&self) -> String;
}

struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn algorithm(&self) -> String {
        "使用策略A".to_string()
    }
}

struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn algorithm(&self) -> String {
        "使用策略B".to_string()
    }
}

struct ConcreteStrategyC;

impl Strategy for ConcreteStrategyC {
    fn algorithm(&self) -> String {
        "使用策略C".to_string()
    }
}

struct Context {
    strategy: Box<dyn Strategy>,
}

impl Context {
    fn new(strategy: Box<dyn Strategy>) -> Self {
        Self { strategy }
    }
    
    fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }
    
    fn execute_strategy(&self) -> String {
        self.strategy.algorithm()
    }
}

fn main() {
    let mut context = Context::new(Box::new(ConcreteStrategyA));
    println!("{}", context.execute_strategy());
    
    context.set_strategy(Box::new(ConcreteStrategyB));
    println!("{}", context.execute_strategy());
    
    context.set_strategy(Box::new(ConcreteStrategyC));
    println!("{}", context.execute_strategy());
}
```

## Haskell实现示例
```haskell
class Strategy a where
    algorithm :: a -> String

data ConcreteStrategyA = ConcreteStrategyA
instance Strategy ConcreteStrategyA where
    algorithm _ = "使用策略A"

data ConcreteStrategyB = ConcreteStrategyB
instance Strategy ConcreteStrategyB where
    algorithm _ = "使用策略B"

data ConcreteStrategyC = ConcreteStrategyC
instance Strategy ConcreteStrategyC where
    algorithm _ = "使用策略C"

data Context a = Context a
newContext :: Strategy a => a -> Context a
newContext strategy = Context strategy
setStrategy :: Strategy a => Context a -> a -> Context a
setStrategy _ strategy = Context strategy
executeStrategy :: Strategy a => Context a -> String
executeStrategy (Context strategy) = algorithm strategy

main = do
    let context1 = newContext ConcreteStrategyA
    putStrLn $ executeStrategy context1
    
    let context2 = setStrategy context1 ConcreteStrategyB
    putStrLn $ executeStrategy context2
    
    let context3 = setStrategy context2 ConcreteStrategyC
    putStrLn $ executeStrategy context3
```

## Lean实现思路
```lean
class Strategy (α : Type) where
  algorithm : α → String

structure ConcreteStrategyA
instance : Strategy ConcreteStrategyA where
  algorithm _ := "使用策略A"

structure ConcreteStrategyB
instance : Strategy ConcreteStrategyB where
  algorithm _ := "使用策略B"

structure ConcreteStrategyC
instance : Strategy ConcreteStrategyC where
  algorithm _ := "使用策略C"

structure Context (α : Type) where
  strategy : α

def newContext (strategy : α) : Context α := { strategy := strategy }
def setStrategy (context : Context α) (strategy : α) : Context α :=
  { context with strategy := strategy }
def executeStrategy (context : Context α) : String :=
  Strategy.algorithm context.strategy
```

## 应用场景
- 排序算法选择
- 支付方式选择
- 压缩算法选择
- 路由策略选择

## 最佳实践
- 策略接口保持简单
- 避免策略类过于复杂
- 支持策略组合 