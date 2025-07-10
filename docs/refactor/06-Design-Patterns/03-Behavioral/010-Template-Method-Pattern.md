# 010 模板方法模式 (Template Method Pattern)

## 1. 理论基础

### 1.1 模式定义

模板方法模式是一种行为型设计模式，定义一个操作中的算法骨架，将某些步骤延迟到子类中实现。模板方法使得子类可以不改变算法的结构即可重定义该算法的某些特定步骤。

### 1.2 核心概念

- **AbstractClass（抽象类）**: 定义模板方法，包含算法的骨架
- **ConcreteClass（具体类）**: 实现抽象类中定义的抽象操作
- **Template Method（模板方法）**: 定义算法的骨架，调用抽象操作
- **Primitive Operations（基本操作）**: 子类必须实现的抽象方法

### 1.3 设计原则

- **开闭原则**: 对扩展开放，对修改封闭
- **单一职责**: 每个类只负责一个功能
- **依赖倒置**: 依赖于抽象而非具体实现

### 1.4 优缺点分析

**优点:**

- 代码复用，避免重复代码
- 扩展性好，易于添加新的具体类
- 控制子类扩展，防止子类改变算法结构
- 符合开闭原则

**缺点:**

- 可能导致类的数量增加
- 继承关系可能变得复杂
- 可能违反里氏替换原则

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class AbstractClass a where
  templateMethod :: a -> String
  templateMethod obj = 
    primitiveOperation1 obj ++ 
    primitiveOperation2 obj ++ 
    primitiveOperation3 obj
  
  primitiveOperation1 :: a -> String
  primitiveOperation2 :: a -> String
  primitiveOperation3 :: a -> String
  
  -- 钩子方法
  hookMethod :: a -> String
  hookMethod _ = "默认钩子方法"
```

### 2.2 扩展接口

```haskell
-- 支持参数化的模板方法
class (AbstractClass a) => ParameterizedTemplate a where
  setParameters :: a -> [String] -> a
  getParameters :: a -> [String]
  
-- 支持条件执行的模板方法
class (AbstractClass a) => ConditionalTemplate a where
  shouldExecuteStep :: a -> Int -> Bool
  getStepCount :: a -> Int
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 抽象类接口
class AbstractClass a where
  templateMethod :: a -> String
  templateMethod obj = 
    primitiveOperation1 obj ++ 
    primitiveOperation2 obj ++ 
    primitiveOperation3 obj ++
    hookMethod obj
  
  primitiveOperation1 :: a -> String
  primitiveOperation2 :: a -> String
  primitiveOperation3 :: a -> String
  
  -- 钩子方法
  hookMethod :: a -> String
  hookMethod _ = "默认钩子方法"

-- 具体类A
data ConcreteClassA = ConcreteClassA {
  name :: String,
  parameters :: [String]
} deriving Show

instance AbstractClass ConcreteClassA where
  primitiveOperation1 obj = "具体类A的操作1: " ++ name obj
  primitiveOperation2 obj = "具体类A的操作2: " ++ show (parameters obj)
  primitiveOperation3 obj = "具体类A的操作3"
  hookMethod obj = "具体类A的钩子方法: " ++ name obj

-- 具体类B
data ConcreteClassB = ConcreteClassB {
  name :: String,
  config :: Map String String
} deriving Show

instance AbstractClass ConcreteClassB where
  primitiveOperation1 obj = "具体类B的操作1: " ++ name obj
  primitiveOperation2 obj = "具体类B的操作2: " ++ show (Map.keys $ config obj)
  primitiveOperation3 obj = "具体类B的操作3"
  hookMethod obj = "具体类B的钩子方法: " ++ name obj

-- 参数化模板类
data ParameterizedTemplateClass = ParameterizedTemplateClass {
  baseClass :: ConcreteClassA,
  params :: [String]
} deriving Show

instance AbstractClass ParameterizedTemplateClass where
  primitiveOperation1 obj = primitiveOperation1 (baseClass obj) ++ " (参数化)"
  primitiveOperation2 obj = primitiveOperation2 (baseClass obj) ++ " (参数化)"
  primitiveOperation3 obj = primitiveOperation3 (baseClass obj) ++ " (参数化)"
  hookMethod obj = hookMethod (baseClass obj) ++ " (参数化)"

-- 条件模板类
data ConditionalTemplateClass = ConditionalTemplateClass {
  baseClass :: ConcreteClassB,
  conditions :: Map Int Bool
} deriving Show

instance AbstractClass ConditionalTemplateClass where
  primitiveOperation1 obj = 
    if Map.findWithDefault True 1 (conditions obj)
    then primitiveOperation1 (baseClass obj) ++ " (条件执行)"
    else "跳过操作1"
  
  primitiveOperation2 obj = 
    if Map.findWithDefault True 2 (conditions obj)
    then primitiveOperation2 (baseClass obj) ++ " (条件执行)"
    else "跳过操作2"
  
  primitiveOperation3 obj = 
    if Map.findWithDefault True 3 (conditions obj)
    then primitiveOperation3 (baseClass obj) ++ " (条件执行)"
    else "跳过操作3"
  
  hookMethod obj = hookMethod (baseClass obj) ++ " (条件执行)"

-- 使用示例
main :: IO ()
main = do
  let concreteA = ConcreteClassA "实例A" ["参数1", "参数2"]
  let concreteB = ConcreteClassB "实例B" (Map.fromList [("key1", "value1"), ("key2", "value2")])
  
  putStrLn "模板方法模式示例:"
  
  putStrLn "\n具体类A执行:"
  putStrLn $ templateMethod concreteA
  
  putStrLn "\n具体类B执行:"
  putStrLn $ templateMethod concreteB
  
  -- 参数化模板
  let paramTemplate = ParameterizedTemplateClass concreteA ["额外参数"]
  putStrLn "\n参数化模板执行:"
  putStrLn $ templateMethod paramTemplate
  
  -- 条件模板
  let conditionTemplate = ConditionalTemplateClass concreteB (Map.fromList [(1, True), (2, False), (3, True)])
  putStrLn "\n条件模板执行:"
  putStrLn $ templateMethod conditionTemplate
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 抽象类trait
trait AbstractClass {
    fn template_method(&self) -> String {
        let mut result = String::new();
        result.push_str(&self.primitive_operation1());
        result.push_str(&self.primitive_operation2());
        result.push_str(&self.primitive_operation3());
        result.push_str(&self.hook_method());
        result
    }
    
    fn primitive_operation1(&self) -> String;
    fn primitive_operation2(&self) -> String;
    fn primitive_operation3(&self) -> String;
    
    // 钩子方法
    fn hook_method(&self) -> String {
        "默认钩子方法".to_string()
    }
}

// 具体类A
#[derive(Debug)]
struct ConcreteClassA {
    name: String,
    parameters: Vec<String>,
}

impl ConcreteClassA {
    fn new(name: String, parameters: Vec<String>) -> Self {
        ConcreteClassA { name, parameters }
    }
}

impl AbstractClass for ConcreteClassA {
    fn primitive_operation1(&self) -> String {
        format!("具体类A的操作1: {}", self.name)
    }
    
    fn primitive_operation2(&self) -> String {
        format!("具体类A的操作2: {:?}", self.parameters)
    }
    
    fn primitive_operation3(&self) -> String {
        "具体类A的操作3".to_string()
    }
    
    fn hook_method(&self) -> String {
        format!("具体类A的钩子方法: {}", self.name)
    }
}

// 具体类B
#[derive(Debug)]
struct ConcreteClassB {
    name: String,
    config: HashMap<String, String>,
}

impl ConcreteClassB {
    fn new(name: String, config: HashMap<String, String>) -> Self {
        ConcreteClassB { name, config }
    }
}

impl AbstractClass for ConcreteClassB {
    fn primitive_operation1(&self) -> String {
        format!("具体类B的操作1: {}", self.name)
    }
    
    fn primitive_operation2(&self) -> String {
        let keys: Vec<&String> = self.config.keys().collect();
        format!("具体类B的操作2: {:?}", keys)
    }
    
    fn primitive_operation3(&self) -> String {
        "具体类B的操作3".to_string()
    }
    
    fn hook_method(&self) -> String {
        format!("具体类B的钩子方法: {}", self.name)
    }
}

// 参数化模板类
#[derive(Debug)]
struct ParameterizedTemplateClass {
    base_class: ConcreteClassA,
    params: Vec<String>,
}

impl ParameterizedTemplateClass {
    fn new(base_class: ConcreteClassA, params: Vec<String>) -> Self {
        ParameterizedTemplateClass { base_class, params }
    }
}

impl AbstractClass for ParameterizedTemplateClass {
    fn primitive_operation1(&self) -> String {
        format!("{} (参数化)", self.base_class.primitive_operation1())
    }
    
    fn primitive_operation2(&self) -> String {
        format!("{} (参数化)", self.base_class.primitive_operation2())
    }
    
    fn primitive_operation3(&self) -> String {
        format!("{} (参数化)", self.base_class.primitive_operation3())
    }
    
    fn hook_method(&self) -> String {
        format!("{} (参数化)", self.base_class.hook_method())
    }
}

// 条件模板类
#[derive(Debug)]
struct ConditionalTemplateClass {
    base_class: ConcreteClassB,
    conditions: HashMap<i32, bool>,
}

impl ConditionalTemplateClass {
    fn new(base_class: ConcreteClassB, conditions: HashMap<i32, bool>) -> Self {
        ConditionalTemplateClass { base_class, conditions }
    }
}

impl AbstractClass for ConditionalTemplateClass {
    fn primitive_operation1(&self) -> String {
        if *self.conditions.get(&1).unwrap_or(&true) {
            format!("{} (条件执行)", self.base_class.primitive_operation1())
        } else {
            "跳过操作1".to_string()
        }
    }
    
    fn primitive_operation2(&self) -> String {
        if *self.conditions.get(&2).unwrap_or(&true) {
            format!("{} (条件执行)", self.base_class.primitive_operation2())
        } else {
            "跳过操作2".to_string()
        }
    }
    
    fn primitive_operation3(&self) -> String {
        if *self.conditions.get(&3).unwrap_or(&true) {
            format!("{} (条件执行)", self.base_class.primitive_operation3())
        } else {
            "跳过操作3".to_string()
        }
    }
    
    fn hook_method(&self) -> String {
        format!("{} (条件执行)", self.base_class.hook_method())
    }
}

// 使用示例
fn main() {
    let concrete_a = ConcreteClassA::new(
        "实例A".to_string(),
        vec!["参数1".to_string(), "参数2".to_string()],
    );
    
    let mut config = HashMap::new();
    config.insert("key1".to_string(), "value1".to_string());
    config.insert("key2".to_string(), "value2".to_string());
    let concrete_b = ConcreteClassB::new("实例B".to_string(), config);
    
    println!("模板方法模式示例:");
    
    println!("\n具体类A执行:");
    println!("{}", concrete_a.template_method());
    
    println!("\n具体类B执行:");
    println!("{}", concrete_b.template_method());
    
    // 参数化模板
    let param_template = ParameterizedTemplateClass::new(
        concrete_a,
        vec!["额外参数".to_string()],
    );
    println!("\n参数化模板执行:");
    println!("{}", param_template.template_method());
    
    // 条件模板
    let mut conditions = HashMap::new();
    conditions.insert(1, true);
    conditions.insert(2, false);
    conditions.insert(3, true);
    let condition_template = ConditionalTemplateClass::new(concrete_b, conditions);
    println!("\n条件模板执行:");
    println!("{}", condition_template.template_method());
}
```

### 3.3 Lean实现

```lean
-- 抽象类类型
inductive AbstractClass where
  | ConcreteClassA : String → List String → AbstractClass
  | ConcreteClassB : String → List (String × String) → AbstractClass

-- 模板方法
def templateMethod : AbstractClass → String
  | AbstractClass.ConcreteClassA name params => 
    primitiveOperation1 (AbstractClass.ConcreteClassA name params) ++
    primitiveOperation2 (AbstractClass.ConcreteClassA name params) ++
    primitiveOperation3 (AbstractClass.ConcreteClassA name params) ++
    hookMethod (AbstractClass.ConcreteClassA name params)
  | AbstractClass.ConcreteClassB name config => 
    primitiveOperation1 (AbstractClass.ConcreteClassB name config) ++
    primitiveOperation2 (AbstractClass.ConcreteClassB name config) ++
    primitiveOperation3 (AbstractClass.ConcreteClassB name config) ++
    hookMethod (AbstractClass.ConcreteClassB name config)

-- 基本操作1
def primitiveOperation1 : AbstractClass → String
  | AbstractClass.ConcreteClassA name _ => s!"具体类A的操作1: {name}"
  | AbstractClass.ConcreteClassB name _ => s!"具体类B的操作1: {name}"

-- 基本操作2
def primitiveOperation2 : AbstractClass → String
  | AbstractClass.ConcreteClassA _ params => s!"具体类A的操作2: {params}"
  | AbstractClass.ConcreteClassB _ config => s!"具体类B的操作2: {config.map Prod.fst}"

-- 基本操作3
def primitiveOperation3 : AbstractClass → String
  | AbstractClass.ConcreteClassA _ _ => "具体类A的操作3"
  | AbstractClass.ConcreteClassB _ _ => "具体类B的操作3"

-- 钩子方法
def hookMethod : AbstractClass → String
  | AbstractClass.ConcreteClassA name _ => s!"具体类A的钩子方法: {name}"
  | AbstractClass.ConcreteClassB name _ => s!"具体类B的钩子方法: {name}"

-- 参数化模板类
structure ParameterizedTemplateClass where
  baseClass : AbstractClass
  params : List String

def parameterizedTemplateMethod (template : ParameterizedTemplateClass) : String :=
  primitiveOperation1 template.baseClass ++ " (参数化)" ++
  primitiveOperation2 template.baseClass ++ " (参数化)" ++
  primitiveOperation3 template.baseClass ++ " (参数化)" ++
  hookMethod template.baseClass ++ " (参数化)"

-- 条件模板类
structure ConditionalTemplateClass where
  baseClass : AbstractClass
  conditions : List (Nat × Bool)

def conditionalTemplateMethod (template : ConditionalTemplateClass) : String :=
  let op1 := if template.conditions.any (λ (step, enabled) => step = 1 ∧ enabled)
             then primitiveOperation1 template.baseClass ++ " (条件执行)"
             else "跳过操作1"
  let op2 := if template.conditions.any (λ (step, enabled) => step = 2 ∧ enabled)
             then primitiveOperation2 template.baseClass ++ " (条件执行)"
             else "跳过操作2"
  let op3 := if template.conditions.any (λ (step, enabled) => step = 3 ∧ enabled)
             then primitiveOperation3 template.baseClass ++ " (条件执行)"
             else "跳过操作3"
  let hook := hookMethod template.baseClass ++ " (条件执行)"
  op1 ++ op2 ++ op3 ++ hook

-- 使用示例
def main : IO Unit := do
  let concreteA := AbstractClass.ConcreteClassA "实例A" ["参数1", "参数2"]
  let concreteB := AbstractClass.ConcreteClassB "实例B" [("key1", "value1"), ("key2", "value2")]
  
  IO.println "模板方法模式示例:"
  
  IO.println "\n具体类A执行:"
  IO.println (templateMethod concreteA)
  
  IO.println "\n具体类B执行:"
  IO.println (templateMethod concreteB)
  
  -- 参数化模板
  let paramTemplate := ParameterizedTemplateClass.mk concreteA ["额外参数"]
  IO.println "\n参数化模板执行:"
  IO.println (parameterizedTemplateMethod paramTemplate)
  
  -- 条件模板
  let conditionTemplate := ConditionalTemplateClass.mk concreteB [(1, true), (2, false), (3, true)]
  IO.println "\n条件模板执行:"
  IO.println (conditionalTemplateMethod conditionTemplate)
```

## 4. 工程实践

### 4.1 设计考虑

- **算法稳定性**: 确保模板方法的稳定性
- **扩展性**: 支持新的具体类实现
- **性能优化**: 避免不必要的抽象层
- **错误处理**: 处理模板方法执行失败的情况

### 4.2 实现模式

```haskell
-- 带缓存的模板方法
data CachedTemplateMethod a = CachedTemplateMethod {
  template :: a,
  cache :: MVar (Map String String)
}

-- 异步模板方法
data AsyncTemplateMethod = AsyncTemplateMethod {
  template :: AbstractClass,
  executor :: ThreadPool
}

-- 带监控的模板方法
data MonitoredTemplateMethod a = MonitoredTemplateMethod {
  template :: a,
  metrics :: MVar TemplateMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data TemplateMethodError = 
  TemplateMethodExecutionFailed String
  | InvalidTemplate String
  | TemplateNotFound String

-- 安全执行
safeTemplateMethod :: AbstractClass a => a -> IO (Either TemplateMethodError String)
safeTemplateMethod template = 
  try (return $ templateMethod template) >>= \case
    Left e -> return $ Left $ TemplateMethodExecutionFailed (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略

- **模板结果缓存**: 缓存相同输入的模板方法执行结果
- **模板对象缓存**: 缓存模板对象避免重复创建
- **性能指标缓存**: 缓存模板方法的性能指标

### 5.2 模板优化

```haskell
-- 优化的模板方法
data OptimizedTemplateMethod a = OptimizedTemplateMethod {
  template :: a,
  optimizations :: Map String String
}

-- 并行模板执行
data ParallelTemplateMethod = ParallelTemplateMethod {
  templates :: [AbstractClass],
  executor :: ThreadPool
}

executeParallel :: ParallelTemplateMethod -> IO [String]
executeParallel method = 
  mapConcurrently templateMethod (templates method)
```

### 5.3 模板组合

```haskell
-- 组合模板方法
data CompositeTemplateMethod = CompositeTemplateMethod {
  templates :: [AbstractClass],
  composition :: String -> String -> String
}

executeComposite :: CompositeTemplateMethod -> String
executeComposite composite = 
  foldr (composition composite) "" (map templateMethod (templates composite))
```

## 6. 应用场景

### 6.1 框架设计

```haskell
-- Web框架模板
data WebFrameworkTemplate = WebFrameworkTemplate {
  requestHandler :: Request -> Response,
  middleware :: [Middleware],
  errorHandler :: Error -> Response
}

-- 框架模板方法
executeWebRequest :: WebFrameworkTemplate -> Request -> IO Response
executeWebRequest framework request = do
  -- 1. 预处理
  processedRequest <- preprocessRequest request
  -- 2. 中间件处理
  middlewareResponse <- applyMiddleware (middleware framework) processedRequest
  -- 3. 主要处理
  mainResponse <- requestHandler framework middlewareResponse
  -- 4. 后处理
  finalResponse <- postprocessResponse mainResponse
  return finalResponse
```

### 6.2 算法模板

```haskell
-- 排序算法模板
data SortingAlgorithmTemplate = SortingAlgorithmTemplate {
  compareFunction :: a -> a -> Ordering,
  swapFunction :: [a] -> Int -> Int -> [a],
  partitionFunction :: [a] -> a -> ([a], [a])
}

-- 排序模板方法
executeSort :: SortingAlgorithmTemplate -> [a] -> [a]
executeSort template data = 
  let sorted = sortWithTemplate template data
  in postprocessSortedData sorted
```

### 6.3 构建流程

```haskell
-- 构建流程模板
data BuildProcessTemplate = BuildProcessTemplate {
  sourceCode :: String,
  buildSteps :: [BuildStep],
  testSteps :: [TestStep]
}

-- 构建模板方法
executeBuild :: BuildProcessTemplate -> IO BuildResult
executeBuild template = do
  -- 1. 清理
  cleanBuildDirectory
  -- 2. 编译
  compiledCode <- compileSource (sourceCode template)
  -- 3. 测试
  testResults <- runTests (testSteps template) compiledCode
  -- 4. 打包
  package <- packageBuild compiledCode
  return $ BuildResult package testResults
```

### 6.4 测试框架

```haskell
-- 测试框架模板
data TestFrameworkTemplate = TestFrameworkTemplate {
  testCases :: [TestCase],
  setupFunction :: IO TestEnvironment,
  teardownFunction :: TestEnvironment -> IO ()
}

-- 测试模板方法
executeTests :: TestFrameworkTemplate -> IO TestResults
executeTests framework = do
  -- 1. 设置测试环境
  env <- setupFunction framework
  -- 2. 运行测试用例
  results <- mapM (runTestCase env) (testCases framework)
  -- 3. 清理测试环境
  teardownFunction framework env
  -- 4. 生成测试报告
  return $ generateTestReport results
```

## 7. 最佳实践

### 7.1 设计原则

- **保持模板方法稳定**: 确保模板方法的结构稳定
- **合理使用钩子方法**: 适度使用钩子方法提供扩展点
- **避免过度抽象**: 避免创建过于复杂的抽象层次
- **性能考虑**: 考虑模板方法的性能影响

### 7.2 实现建议

```haskell
-- 模板工厂
class TemplateFactory a where
  createTemplate :: String -> Maybe a
  listTemplates :: [String]
  validateTemplate :: a -> Bool

-- 模板注册表
data TemplateRegistry = TemplateRegistry {
  templates :: Map String (forall a. AbstractClass a => a),
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
-- 模板测试
testTemplate :: AbstractClass a => a -> Bool
testTemplate template = 
  let result = templateMethod template
  in not (null result) && isValidResult result

-- 性能测试
benchmarkTemplate :: AbstractClass a => a -> IO Double
benchmarkTemplate template = do
  start <- getCurrentTime
  replicateM_ 1000 $ templateMethod template
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的模板类型
- **序列化**: 支持模板的序列化和反序列化
- **版本控制**: 支持模板的版本管理
- **分布式**: 支持跨网络的模板执行

## 8. 总结

模板方法模式是定义算法骨架的强大工具，通过将算法的可变部分延迟到子类实现提供了代码复用和扩展性。在实现时需要注意模板方法的稳定性、钩子方法的合理使用和性能优化。该模式在框架设计、算法模板、构建流程、测试框架等场景中都有广泛应用。
