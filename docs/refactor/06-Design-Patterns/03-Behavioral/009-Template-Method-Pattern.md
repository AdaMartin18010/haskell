# 009 模板方法模式 (Template Method Pattern)

## 1. 理论基础

### 1.1 模式定义

模板方法模式是一种行为型设计模式，定义一个算法的骨架，将一些步骤延迟到子类中实现。模板方法使得子类可以在不改变算法结构的情况下，重新定义算法的某些特定步骤。

### 1.2 核心概念

- **AbstractClass（抽象类）**: 定义模板方法和抽象操作
- **ConcreteClass（具体类）**: 实现抽象操作，提供具体行为
- **Template Method（模板方法）**: 定义算法骨架，调用抽象操作
- **Primitive Operations（基本操作）**: 子类必须实现的操作
- **Hook（钩子）**: 子类可选择重写的操作

### 1.3 设计原则

- **开闭原则**: 对扩展开放，对修改封闭
- **单一职责**: 每个类只负责算法的一个部分
- **依赖倒置**: 高层模块不依赖低层模块

### 1.4 优缺点分析

**优点：**

- 代码复用，避免重复代码
- 扩展性好，易于添加新的具体实现
- 控制子类扩展，防止子类改变算法结构
- 提供默认实现，减少子类负担

**缺点：**

- 可能违反里氏替换原则
- 继承关系固定，不够灵活
- 可能导致"继承地狱"

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class TemplateMethod a where
  templateMethod :: a -> IO ()
  primitiveOperation1 :: a -> IO ()
  primitiveOperation2 :: a -> IO ()
  hook :: a -> IO ()

-- 默认实现
templateMethodDefault :: (TemplateMethod a) => a -> IO ()
templateMethodDefault obj = do
  putStrLn "Template method started"
  primitiveOperation1 obj
  primitiveOperation2 obj
  hook obj
  putStrLn "Template method finished"
```

### 2.2 扩展接口

```haskell
-- 支持参数化模板方法
class ParameterizedTemplate a b where
  parameterizedTemplate :: a -> b -> IO ()
  parameterizedOperation1 :: a -> b -> IO ()
  parameterizedOperation2 :: a -> b -> IO ()

-- 支持条件钩子
class ConditionalTemplate a where
  conditionalTemplate :: a -> IO ()
  shouldExecute :: a -> Bool
  conditionalOperation :: a -> IO ()
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 模板方法接口
class TemplateMethod a where
  templateMethod :: a -> IO ()
  primitiveOperation1 :: a -> IO ()
  primitiveOperation2 :: a -> IO ()
  hook :: a -> IO ()

-- 默认实现
templateMethodDefault :: (TemplateMethod a) => a -> IO ()
templateMethodDefault obj = do
  putStrLn "Template method started"
  primitiveOperation1 obj
  primitiveOperation2 obj
  hook obj
  putStrLn "Template method finished"

-- 具体类A
data ConcreteClassA = ConcreteClassA {
  name :: String,
  config :: String
} deriving Show

instance TemplateMethod ConcreteClassA where
  templateMethod = templateMethodDefault
  primitiveOperation1 obj = putStrLn $ "Concrete A operation 1: " ++ name obj
  primitiveOperation2 obj = putStrLn $ "Concrete A operation 2: " ++ config obj
  hook obj = putStrLn $ "Concrete A hook: " ++ name obj

-- 具体类B
data ConcreteClassB = ConcreteClassB {
  name :: String,
  priority :: Int
} deriving Show

instance TemplateMethod ConcreteClassB where
  templateMethod = templateMethodDefault
  primitiveOperation1 obj = putStrLn $ "Concrete B operation 1: " ++ name obj ++ " (优先级: " ++ show (priority obj) ++ ")"
  primitiveOperation2 obj = putStrLn $ "Concrete B operation 2: " ++ name obj
  hook obj = putStrLn $ "Concrete B hook: " ++ name obj

-- 参数化模板方法
class ParameterizedTemplate a b where
  parameterizedTemplate :: a -> b -> IO ()
  parameterizedOperation1 :: a -> b -> IO ()
  parameterizedOperation2 :: a -> b -> IO ()

-- 条件模板方法
class ConditionalTemplate a where
  conditionalTemplate :: a -> IO ()
  shouldExecute :: a -> Bool
  conditionalOperation :: a -> IO ()

-- 默认条件实现
conditionalTemplateDefault :: (ConditionalTemplate a) => a -> IO ()
conditionalTemplateDefault obj = do
  putStrLn "Conditional template started"
  if shouldExecute obj
  then conditionalOperation obj
  else putStrLn "Operation skipped"
  putStrLn "Conditional template finished"

-- 条件具体类
data ConditionalClass = ConditionalClass {
  name :: String,
  enabled :: Bool
} deriving Show

instance ConditionalTemplate ConditionalClass where
  conditionalTemplate = conditionalTemplateDefault
  shouldExecute obj = enabled obj
  conditionalOperation obj = putStrLn $ "Conditional operation: " ++ name obj

-- 使用示例
main :: IO ()
main = do
  putStrLn "模板方法模式示例:"
  
  -- 基本模板方法
  let concreteA = ConcreteClassA "类A" "配置A"
  let concreteB = ConcreteClassB "类B" 5
  
  putStrLn "\n=== 具体类A ==="
  templateMethod concreteA
  
  putStrLn "\n=== 具体类B ==="
  templateMethod concreteB
  
  -- 条件模板方法
  let conditionalEnabled = ConditionalClass "启用类" True
  let conditionalDisabled = ConditionalClass "禁用类" False
  
  putStrLn "\n=== 条件模板方法 ==="
  conditionalTemplate conditionalEnabled
  conditionalTemplate conditionalDisabled
```

### 3.2 Rust实现

```rust
// 模板方法trait
trait TemplateMethod {
    fn template_method(&self) {
        println!("Template method started");
        self.primitive_operation_1();
        self.primitive_operation_2();
        self.hook();
        println!("Template method finished");
    }
    
    fn primitive_operation_1(&self);
    fn primitive_operation_2(&self);
    fn hook(&self) {
        // 默认空实现
    }
}

// 具体类A
#[derive(Debug)]
struct ConcreteClassA {
    name: String,
    config: String,
}

impl ConcreteClassA {
    fn new(name: String, config: String) -> Self {
        ConcreteClassA { name, config }
    }
}

impl TemplateMethod for ConcreteClassA {
    fn primitive_operation_1(&self) {
        println!("Concrete A operation 1: {}", self.name);
    }
    
    fn primitive_operation_2(&self) {
        println!("Concrete A operation 2: {}", self.config);
    }
    
    fn hook(&self) {
        println!("Concrete A hook: {}", self.name);
    }
}

// 具体类B
#[derive(Debug)]
struct ConcreteClassB {
    name: String,
    priority: i32,
}

impl ConcreteClassB {
    fn new(name: String, priority: i32) -> Self {
        ConcreteClassB { name, priority }
    }
}

impl TemplateMethod for ConcreteClassB {
    fn primitive_operation_1(&self) {
        println!("Concrete B operation 1: {} (优先级: {})", self.name, self.priority);
    }
    
    fn primitive_operation_2(&self) {
        println!("Concrete B operation 2: {}", self.name);
    }
    
    fn hook(&self) {
        println!("Concrete B hook: {}", self.name);
    }
}

// 参数化模板方法
trait ParameterizedTemplate<T> {
    fn parameterized_template(&self, param: &T) {
        println!("Parameterized template started");
        self.parameterized_operation_1(param);
        self.parameterized_operation_2(param);
        println!("Parameterized template finished");
    }
    
    fn parameterized_operation_1(&self, param: &T);
    fn parameterized_operation_2(&self, param: &T);
}

// 条件模板方法
trait ConditionalTemplate {
    fn conditional_template(&self) {
        println!("Conditional template started");
        if self.should_execute() {
            self.conditional_operation();
        } else {
            println!("Operation skipped");
        }
        println!("Conditional template finished");
    }
    
    fn should_execute(&self) -> bool;
    fn conditional_operation(&self);
}

// 条件具体类
#[derive(Debug)]
struct ConditionalClass {
    name: String,
    enabled: bool,
}

impl ConditionalClass {
    fn new(name: String, enabled: bool) -> Self {
        ConditionalClass { name, enabled }
    }
}

impl ConditionalTemplate for ConditionalClass {
    fn should_execute(&self) -> bool {
        self.enabled
    }
    
    fn conditional_operation(&self) {
        println!("Conditional operation: {}", self.name);
    }
}

// 使用示例
fn main() {
    println!("模板方法模式示例:");
    
    // 基本模板方法
    let concrete_a = ConcreteClassA::new("类A".to_string(), "配置A".to_string());
    let concrete_b = ConcreteClassB::new("类B".to_string(), 5);
    
    println!("\n=== 具体类A ===");
    concrete_a.template_method();
    
    println!("\n=== 具体类B ===");
    concrete_b.template_method();
    
    // 条件模板方法
    let conditional_enabled = ConditionalClass::new("启用类".to_string(), true);
    let conditional_disabled = ConditionalClass::new("禁用类".to_string(), false);
    
    println!("\n=== 条件模板方法 ===");
    conditional_enabled.conditional_template();
    conditional_disabled.conditional_template();
}
```

### 3.3 Lean实现

```lean
-- 模板方法类型类
class TemplateMethod (α : Type) where
  templateMethod : α → IO Unit
  primitiveOperation1 : α → IO Unit
  primitiveOperation2 : α → IO Unit
  hook : α → IO Unit

-- 默认实现
def templateMethodDefault {α : Type} [TemplateMethod α] (obj : α) : IO Unit := do
  IO.println "Template method started"
  primitiveOperation1 obj
  primitiveOperation2 obj
  hook obj
  IO.println "Template method finished"

-- 具体类A
structure ConcreteClassA where
  name : String
  config : String

def newConcreteClassA (name : String) (config : String) : ConcreteClassA := {
  name := name,
  config := config
}

instance : TemplateMethod ConcreteClassA where
  templateMethod := templateMethodDefault
  primitiveOperation1 obj := IO.println ("Concrete A operation 1: " ++ obj.name)
  primitiveOperation2 obj := IO.println ("Concrete A operation 2: " ++ obj.config)
  hook obj := IO.println ("Concrete A hook: " ++ obj.name)

-- 具体类B
structure ConcreteClassB where
  name : String
  priority : Nat

def newConcreteClassB (name : String) (priority : Nat) : ConcreteClassB := {
  name := name,
  priority := priority
}

instance : TemplateMethod ConcreteClassB where
  templateMethod := templateMethodDefault
  primitiveOperation1 obj := IO.println ("Concrete B operation 1: " ++ obj.name ++ " (优先级: " ++ toString obj.priority ++ ")")
  primitiveOperation2 obj := IO.println ("Concrete B operation 2: " ++ obj.name)
  hook obj := IO.println ("Concrete B hook: " ++ obj.name)

-- 条件模板方法
class ConditionalTemplate (α : Type) where
  conditionalTemplate : α → IO Unit
  shouldExecute : α → Bool
  conditionalOperation : α → IO Unit

-- 默认条件实现
def conditionalTemplateDefault {α : Type} [ConditionalTemplate α] (obj : α) : IO Unit := do
  IO.println "Conditional template started"
  if shouldExecute obj
  then conditionalOperation obj
  else IO.println "Operation skipped"
  IO.println "Conditional template finished"

-- 条件具体类
structure ConditionalClass where
  name : String
  enabled : Bool

def newConditionalClass (name : String) (enabled : Bool) : ConditionalClass := {
  name := name,
  enabled := enabled
}

instance : ConditionalTemplate ConditionalClass where
  conditionalTemplate := conditionalTemplateDefault
  shouldExecute obj := obj.enabled
  conditionalOperation obj := IO.println ("Conditional operation: " ++ obj.name)

-- 使用示例
def main : IO Unit := do
  IO.println "模板方法模式示例:"
  
  -- 基本模板方法
  let concreteA := newConcreteClassA "类A" "配置A"
  let concreteB := newConcreteClassB "类B" 5
  
  IO.println "\n=== 具体类A ==="
  templateMethod concreteA
  
  IO.println "\n=== 具体类B ==="
  templateMethod concreteB
  
  -- 条件模板方法
  let conditionalEnabled := newConditionalClass "启用类" true
  let conditionalDisabled := newConditionalClass "禁用类" false
  
  IO.println "\n=== 条件模板方法 ==="
  conditionalTemplate conditionalEnabled
  conditionalTemplate conditionalDisabled
```

## 4. 工程实践

### 4.1 设计考虑

- **算法稳定性**: 确保模板方法的核心逻辑稳定
- **扩展点设计**: 合理设计抽象操作和钩子
- **性能影响**: 考虑虚函数调用的性能开销
- **测试策略**: 设计可测试的模板方法

### 4.2 实现模式

```haskell
-- 带配置的模板方法
data ConfigurableTemplate config = ConfigurableTemplate {
  config :: config,
  template :: config -> IO ()
}

-- 带缓存的模板方法
data CachedTemplate cache = CachedTemplate {
  cache :: MVar cache,
  template :: cache -> IO ()
}

-- 带监控的模板方法
data MonitoredTemplate metrics = MonitoredTemplate {
  metrics :: MVar metrics,
  template :: metrics -> IO ()
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data TemplateError = 
  OperationFailed String
  | ConfigurationError String
  | TimeoutError

-- 安全模板方法
safeTemplateMethod :: TemplateMethod a => a -> IO (Either TemplateError ())
safeTemplateMethod obj = 
  try (templateMethod obj) >>= \case
    Left e -> return $ Left $ OperationFailed (show e)
    Right _ -> return $ Right ()
```

## 5. 性能优化

### 5.1 编译时优化

- **内联优化**: 编译器内联简单操作
- **常量折叠**: 编译时计算常量表达式
- **死代码消除**: 移除未使用的代码路径

### 5.2 运行时优化

```haskell
-- 缓存模板结果
data CachedTemplate result = CachedTemplate {
  cache :: MVar (Map String result),
  template :: String -> IO result
}

-- 延迟计算
data LazyTemplate = LazyTemplate {
  template :: IO (),
  computed :: MVar Bool
}
```

### 5.3 内存优化

- **对象池**: 复用模板对象
- **智能指针**: 自动内存管理
- **内存对齐**: 优化访问性能

## 6. 应用场景

### 6.1 框架开发

```haskell
-- Web框架模板
class WebFramework a where
  handleRequest :: a -> Request -> IO Response
  validateRequest :: a -> Request -> Bool
  processRequest :: a -> Request -> IO Response
  formatResponse :: a -> Response -> IO String

-- 默认实现
handleRequestDefault :: (WebFramework a) => a -> Request -> IO Response
handleRequestDefault framework request = do
  if validateRequest framework request
  then do
    response <- processRequest framework request
    formatResponse framework response
  else return $ Response 400 "Bad Request"
```

### 6.2 算法框架

```haskell
-- 排序算法模板
class SortingAlgorithm a where
  sort :: a -> [Int] -> [Int]
  compare :: a -> Int -> Int -> Ordering
  partition :: a -> [Int] -> ([Int], [Int])

-- 快速排序实现
data QuickSort = QuickSort

instance SortingAlgorithm QuickSort where
  sort _ [] = []
  sort _ [x] = [x]
  sort algorithm xs = do
    let (left, right) = partition algorithm xs
    sort algorithm left ++ sort algorithm right
  
  compare _ x y = compare x y
  
  partition _ [] = ([], [])
  partition _ (x:xs) = 
    let (left, right) = partition _ xs
    in if x <= head xs
       then (x:left, right)
       else (left, x:right)
```

### 6.3 测试框架

```haskell
-- 测试框架模板
class TestFramework a where
  runTest :: a -> TestCase -> IO TestResult
  setup :: a -> IO ()
  teardown :: a -> IO ()
  assert :: a -> Bool -> String -> IO ()

-- 默认测试流程
runTestDefault :: (TestFramework a) => a -> TestCase -> IO TestResult
runTestDefault framework testCase = do
  setup framework
  result <- executeTest framework testCase
  teardown framework
  return result
```

### 6.4 构建系统

```haskell
-- 构建系统模板
class BuildSystem a where
  build :: a -> Project -> IO BuildResult
  compile :: a -> Source -> IO Object
  link :: a -> [Object] -> IO Executable
  test :: a -> Project -> IO TestResult

-- 默认构建流程
buildDefault :: (BuildSystem a) => a -> Project -> IO BuildResult
buildDefault system project = do
  objects <- mapM (compile system) (sources project)
  executable <- link system objects
  testResult <- test system project
  return $ BuildResult executable testResult
```

## 7. 最佳实践

### 7.1 设计原则

- **保持模板简单**: 避免复杂的条件逻辑
- **提供扩展点**: 设计合理的抽象操作
- **考虑性能影响**: 避免过度抽象
- **实现文档化**: 清晰说明模板方法的行为

### 7.2 实现建议

```haskell
-- 模板方法工厂
class TemplateFactory a where
  createTemplate :: String -> Maybe a
  listTemplates :: [String]
  validateTemplate :: a -> Bool

-- 模板方法注册表
data TemplateRegistry = TemplateRegistry {
  templates :: Map String (forall a. TemplateMethod a => a),
  metadata :: Map String String
}

-- 线程安全模板管理器
data ThreadSafeTemplateManager = ThreadSafeTemplateManager {
  manager :: MVar TemplateManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 模板方法测试
testTemplate :: TemplateMethod a => a -> Bool
testTemplate obj = 
  -- 测试模板方法的基本行为
  True

-- 性能测试
benchmarkTemplate :: TemplateMethod a => a -> IO Double
benchmarkTemplate obj = do
  start <- getCurrentTime
  replicateM_ 1000 $ templateMethod obj
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的模板方法
- **序列化**: 支持模板方法的序列化
- **版本控制**: 支持模板方法接口的版本管理
- **分布式**: 支持跨网络的模板方法调用

## 8. 总结

模板方法模式是框架设计和算法复用的重要工具，通过定义算法骨架并提供扩展点，实现了代码复用和扩展性的平衡。在实现时需注意模板方法的稳定性、扩展点设计和性能影响。该模式在框架开发、算法实现、测试框架、构建系统等场景中有广泛应用。
