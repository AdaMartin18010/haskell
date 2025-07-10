# 001 装饰器模式 (Decorator Pattern)

## 1. 理论基础

### 1.1 模式定义

装饰器模式是一种结构型设计模式，允许向对象动态添加新功能而不改变其结构。通过组合和委托实现功能扩展，提供比继承更灵活的功能扩展方式。

### 1.2 核心概念

- **Component（组件）**: 定义对象的接口，可以给这些对象动态地添加职责
- **ConcreteComponent（具体组件）**: 定义一个对象，可以给这个对象添加一些职责
- **Decorator（装饰器）**: 维持一个指向Component对象的引用，并定义一个与Component接口一致的接口
- **ConcreteDecorator（具体装饰器）**: 向组件添加职责

### 1.3 设计原则

- **开闭原则**: 对扩展开放，对修改封闭
- **单一职责**: 每个装饰器只负责一个功能
- **组合优于继承**: 使用组合而不是继承来扩展功能

### 1.4 优缺点分析

**优点:**

- 比继承更灵活，可以动态地给对象添加功能
- 符合开闭原则，易于扩展
- 可以组合多个装饰器
- 避免了继承的静态特性

**缺点:**

- 会产生许多小对象，增加系统复杂度
- 装饰器链过长时难以调试
- 可能导致对象标识问题

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Component a where
  operation :: a -> String
  cost :: a -> Double
  description :: a -> String

-- 基础组件
data Coffee = Coffee deriving Show

-- 装饰器基类
data Decorator a = Decorator a deriving Show

-- 具体装饰器
data MilkDecorator a = MilkDecorator a deriving Show
data SugarDecorator a = SugarDecorator a deriving Show
data WhipDecorator a = WhipDecorator a deriving Show
```

### 2.2 扩展接口

```haskell
-- 支持状态查询的接口
class (Component a) => StatefulComponent a where
  getState :: a -> String
  setState :: a -> String -> a
  
-- 支持撤销的接口
class (Component a) => ReversibleComponent a where
  undo :: a -> Maybe a
  redo :: a -> Maybe a
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 基础组件接口
class Component a where
  operation :: a -> String
  cost :: a -> Double
  description :: a -> String

-- 基础咖啡
data Coffee = Coffee deriving Show

instance Component Coffee where
  operation Coffee = "Simple Coffee"
  cost Coffee = 2.0
  description Coffee = "Basic coffee"

-- 装饰器基类
data Decorator a = Decorator a deriving Show

instance Component a => Component (Decorator a) where
  operation (Decorator component) = operation component
  cost (Decorator component) = cost component
  description (Decorator component) = description component

-- 牛奶装饰器
data MilkDecorator a = MilkDecorator a deriving Show

instance Component a => Component (MilkDecorator a) where
  operation (MilkDecorator component) = operation component ++ ", Milk"
  cost (MilkDecorator component) = cost component + 0.5
  description (MilkDecorator component) = description component ++ " with milk"

-- 糖装饰器
data SugarDecorator a = SugarDecorator a deriving Show

instance Component a => Component (SugarDecorator a) where
  operation (SugarDecorator component) = operation component ++ ", Sugar"
  cost (SugarDecorator component) = cost component + 0.3
  description (SugarDecorator component) = description component ++ " with sugar"

-- 奶油装饰器
data WhipDecorator a = WhipDecorator a deriving Show

instance Component a => Component (WhipDecorator a) where
  operation (WhipDecorator component) = operation component ++ ", Whip"
  cost (WhipDecorator component) = cost component + 0.7
  description (WhipDecorator component) = description component ++ " with whip"

-- 使用示例
main :: IO ()
main = do
  let coffee = Coffee
  let milkCoffee = MilkDecorator coffee
  let sweetMilkCoffee = SugarDecorator milkCoffee
  let fancyCoffee = WhipDecorator sweetMilkCoffee
  
  putStrLn "装饰器模式示例:"
  putStrLn $ "基础咖啡: " ++ operation coffee ++ " - $" ++ show (cost coffee)
  putStrLn $ "加牛奶: " ++ operation milkCoffee ++ " - $" ++ show (cost milkCoffee)
  putStrLn $ "加糖: " ++ operation sweetMilkCoffee ++ " - $" ++ show (cost sweetMilkCoffee)
  putStrLn $ "加奶油: " ++ operation fancyCoffee ++ " - $" ++ show (cost fancyCoffee)
  
  -- 装饰器链构建
  let buildCoffee :: [String] -> Coffee
      buildCoffee [] = Coffee
      buildCoffee ("milk":rest) = MilkDecorator (buildCoffee rest)
      buildCoffee ("sugar":rest) = SugarDecorator (buildCoffee rest)
      buildCoffee ("whip":rest) = WhipDecorator (buildCoffee rest)
      buildCoffee (_:rest) = buildCoffee rest
  
  let customCoffee = buildCoffee ["milk", "sugar", "whip"]
  putStrLn $ "自定义咖啡: " ++ operation customCoffee ++ " - $" ++ show (cost customCoffee)
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 基础组件trait
trait Component {
    fn operation(&self) -> String;
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

// 基础咖啡
#[derive(Debug, Clone)]
struct Coffee;

impl Component for Coffee {
    fn operation(&self) -> String {
        "Simple Coffee".to_string()
    }
    
    fn cost(&self) -> f64 {
        2.0
    }
    
    fn description(&self) -> String {
        "Basic coffee".to_string()
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
    
    fn cost(&self) -> f64 {
        self.component.cost()
    }
    
    fn description(&self) -> String {
        self.component.description()
    }
}

// 牛奶装饰器
struct MilkDecorator<T: Component> {
    component: T,
}

impl<T: Component> Component for MilkDecorator<T> {
    fn operation(&self) -> String {
        format!("{}, Milk", self.component.operation())
    }
    
    fn cost(&self) -> f64 {
        self.component.cost() + 0.5
    }
    
    fn description(&self) -> String {
        format!("{} with milk", self.component.description())
    }
}

// 糖装饰器
struct SugarDecorator<T: Component> {
    component: T,
}

impl<T: Component> Component for SugarDecorator<T> {
    fn operation(&self) -> String {
        format!("{}, Sugar", self.component.operation())
    }
    
    fn cost(&self) -> f64 {
        self.component.cost() + 0.3
    }
    
    fn description(&self) -> String {
        format!("{} with sugar", self.component.description())
    }
}

// 奶油装饰器
struct WhipDecorator<T: Component> {
    component: T,
}

impl<T: Component> Component for WhipDecorator<T> {
    fn operation(&self) -> String {
        format!("{}, Whip", self.component.operation())
    }
    
    fn cost(&self) -> f64 {
        self.component.cost() + 0.7
    }
    
    fn description(&self) -> String {
        format!("{} with whip", self.component.description())
    }
}

// 装饰器构建器
struct CoffeeBuilder<T: Component> {
    component: T,
}

impl CoffeeBuilder<Coffee> {
    fn new() -> Self {
        CoffeeBuilder { component: Coffee }
    }
    
    fn add_milk(self) -> CoffeeBuilder<MilkDecorator<Coffee>> {
        CoffeeBuilder { 
            component: MilkDecorator { component: self.component } 
        }
    }
    
    fn add_sugar(self) -> CoffeeBuilder<SugarDecorator<Coffee>> {
        CoffeeBuilder { 
            component: SugarDecorator { component: self.component } 
        }
    }
}

impl<T: Component> CoffeeBuilder<T> {
    fn add_milk(self) -> CoffeeBuilder<MilkDecorator<T>> {
        CoffeeBuilder { 
            component: MilkDecorator { component: self.component } 
        }
    }
    
    fn add_sugar(self) -> CoffeeBuilder<SugarDecorator<T>> {
        CoffeeBuilder { 
            component: SugarDecorator { component: self.component } 
        }
    }
    
    fn add_whip(self) -> CoffeeBuilder<WhipDecorator<T>> {
        CoffeeBuilder { 
            component: WhipDecorator { component: self.component } 
        }
    }
    
    fn build(self) -> T {
        self.component
    }
}

// 使用示例
fn main() {
    let coffee = Coffee;
    let milk_coffee = MilkDecorator { component: coffee.clone() };
    let sweet_milk_coffee = SugarDecorator { component: milk_coffee };
    let fancy_coffee = WhipDecorator { component: sweet_milk_coffee };
    
    println!("装饰器模式示例:");
    println!("基础咖啡: {} - ${:.2}", coffee.operation(), coffee.cost());
    println!("加牛奶: {} - ${:.2}", milk_coffee.operation(), milk_coffee.cost());
    println!("加糖: {} - ${:.2}", sweet_milk_coffee.operation(), sweet_milk_coffee.cost());
    println!("加奶油: {} - ${:.2}", fancy_coffee.operation(), fancy_coffee.cost());
    
    // 使用构建器模式
    let custom_coffee = CoffeeBuilder::new()
        .add_milk()
        .add_sugar()
        .add_whip()
        .build();
    
    println!("自定义咖啡: {} - ${:.2}", custom_coffee.operation(), custom_coffee.cost());
}
```

### 3.3 Lean实现

```lean
-- 组件类型
inductive Component where
  | Coffee : Component
  | MilkDecorator : Component → Component
  | SugarDecorator : Component → Component
  | WhipDecorator : Component → Component

-- 操作函数
def operation : Component → String
  | Component.Coffee => "Simple Coffee"
  | Component.MilkDecorator c => operation c ++ ", Milk"
  | Component.SugarDecorator c => operation c ++ ", Sugar"
  | Component.WhipDecorator c => operation c ++ ", Whip"

-- 成本函数
def cost : Component → Float
  | Component.Coffee => 2.0
  | Component.MilkDecorator c => cost c + 0.5
  | Component.SugarDecorator c => cost c + 0.3
  | Component.WhipDecorator c => cost c + 0.7

-- 描述函数
def description : Component → String
  | Component.Coffee => "Basic coffee"
  | Component.MilkDecorator c => description c ++ " with milk"
  | Component.SugarDecorator c => description c ++ " with sugar"
  | Component.WhipDecorator c => description c ++ " with whip"

-- 装饰器性质定理
theorem decorator_cost_additive :
  ∀ c : Component, cost (MilkDecorator c) = cost c + 0.5 :=
  by simp [cost]

-- 使用示例
def main : IO Unit := do
  let coffee := Component.Coffee
  let milkCoffee := Component.MilkDecorator coffee
  let sweetMilkCoffee := Component.SugarDecorator milkCoffee
  let fancyCoffee := Component.WhipDecorator sweetMilkCoffee
  
  IO.println s!"装饰器模式示例:"
  IO.println s!"基础咖啡: {coffee.operation} - ${coffee.cost}"
  IO.println s!"加牛奶: {milkCoffee.operation} - ${milkCoffee.cost}"
  IO.println s!"加糖: {sweetMilkCoffee.operation} - ${sweetMilkCoffee.cost}"
  IO.println s!"加奶油: {fancyCoffee.operation} - ${fancyCoffee.cost}"
```

## 4. 工程实践

### 4.1 设计考虑

- **接口一致性**: 确保装饰器和被装饰对象实现相同的接口
- **类型安全**: 在编译时检查装饰器的类型约束
- **内存管理**: 合理管理装饰器链的内存分配
- **性能优化**: 避免不必要的对象创建和复制

### 4.2 实现模式

```haskell
-- 类型安全的装饰器
data SafeDecorator a = SafeDecorator {
  component :: a,
  decorators :: [String]
}

-- 带缓存的装饰器
data CachedDecorator a = CachedDecorator {
  component :: a,
  cache :: Map String String
}

-- 可撤销的装饰器
data ReversibleDecorator a = ReversibleDecorator {
  component :: a,
  history :: [a],
  future :: [a]
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data DecoratorError = 
  InvalidDecoration String
  | CircularDecoration String
  | MaxDecorationsReached String

-- 安全装饰
safeDecorate :: Component a => a -> String -> Either DecoratorError a
safeDecorate component "milk" = Right $ MilkDecorator component
safeDecorate component "sugar" = Right $ SugarDecorator component
safeDecorate component "whip" = Right $ WhipDecorator component
safeDecorate _ decoration = Left $ InvalidDecoration decoration
```

## 5. 性能优化

### 5.1 缓存策略

- **操作结果缓存**: 缓存频繁调用的操作结果
- **装饰器链缓存**: 缓存常用的装饰器组合
- **内存池**: 使用对象池减少内存分配开销

### 5.2 延迟初始化

```haskell
-- 延迟装饰器
data LazyDecorator a = LazyDecorator {
  component :: a,
  decorator :: IO String,
  cached :: Maybe String
}

applyLazyDecorator :: LazyDecorator a -> IO String
applyLazyDecorator (LazyDecorator _ decorator (Just cached)) = return cached
applyLazyDecorator (LazyDecorator _ decorator Nothing) = decorator
```

### 5.3 装饰器链优化

```haskell
-- 优化的装饰器链
data OptimizedDecorator a = OptimizedDecorator {
  component :: a,
  optimizations :: Map String String
}

-- 合并相同类型的装饰器
mergeDecorators :: [String] -> [String]
mergeDecorators = foldr merge []
  where
    merge decorator [] = [decorator]
    merge decorator (x:xs) = 
      if decorator == x 
      then x:xs 
      else decorator:x:xs
```

## 6. 应用场景

### 6.1 日志记录

```haskell
-- 日志装饰器
data LoggingDecorator a = LoggingDecorator {
  component :: a,
  logger :: String -> IO ()
}

instance Component a => Component (LoggingDecorator a) where
  operation (LoggingDecorator component logger) = do
    result <- operation component
    logger $ "Operation called: " ++ result
    return result
```

### 6.2 缓存包装

```haskell
-- 缓存装饰器
data CachingDecorator a = CachingDecorator {
  component :: a,
  cache :: MVar (Map String String)
}

instance Component a => Component (CachingDecorator a) where
  operation (CachingDecorator component cache) = do
    cached <- readMVar cache
    case Map.lookup "operation" cached of
      Just result -> return result
      Nothing -> do
        result <- operation component
        modifyMVar_ cache $ return . Map.insert "operation" result
        return result
```

### 6.3 权限检查

```haskell
-- 权限装饰器
data AuthorizationDecorator a = AuthorizationDecorator {
  component :: a,
  user :: String,
  permissions :: [String]
}

instance Component a => Component (AuthorizationDecorator a) where
  operation (AuthorizationDecorator component user permissions) = do
    if "read" `elem` permissions
    then operation component
    else throwError $ "Access denied for user: " ++ user
```

### 6.4 事务管理

```haskell
-- 事务装饰器
data TransactionDecorator a = TransactionDecorator {
  component :: a,
  transaction :: MVar Bool
}

instance Component a => Component (TransactionDecorator a) where
  operation (TransactionDecorator component transaction) = do
    modifyMVar_ transaction $ return . const True
    result <- operation component
    modifyMVar_ transaction $ return . const False
    return result
```

## 7. 最佳实践

### 7.1 设计原则

- **保持装饰器轻量**: 每个装饰器只负责一个功能
- **避免装饰器链过长**: 限制装饰器的嵌套深度
- **考虑性能影响**: 合理使用缓存和优化
- **使用组合而非继承**: 优先使用装饰器模式而非继承

### 7.2 实现建议

```haskell
-- 装饰器工厂
class DecoratorFactory a where
  createDecorator :: String -> a -> Maybe a
  listDecorators :: [String]
  validateDecorator :: String -> Bool

-- 装饰器注册表
data DecoratorRegistry = DecoratorRegistry {
  decorators :: Map String (forall a. Component a => a -> a),
  metadata :: Map String String
}

-- 线程安全装饰器
data ThreadSafeDecorator a = ThreadSafeDecorator {
  component :: MVar a,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 装饰器测试
testDecorator :: Component a => a -> String -> Bool
testDecorator component decoratorType = 
  let decorated = applyDecorator component decoratorType
      originalCost = cost component
      decoratedCost = cost decorated
  in decoratedCost > originalCost

-- 性能测试
benchmarkDecorator :: Component a => a -> String -> IO Double
benchmarkDecorator component decoratorType = do
  start <- getCurrentTime
  replicateM_ 1000 $ operation $ applyDecorator component decoratorType
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的装饰器类型
- **序列化**: 支持装饰器链的序列化和反序列化
- **版本控制**: 支持装饰器的版本管理
- **分布式**: 支持跨网络的装饰器应用

## 8. 总结

装饰器模式是动态扩展对象功能的强大工具，通过组合和委托提供了比继承更灵活的功能扩展方式。在实现时需要注意类型安全、性能优化和内存管理。该模式在日志记录、缓存包装、权限检查、事务管理等场景中都有广泛应用。
