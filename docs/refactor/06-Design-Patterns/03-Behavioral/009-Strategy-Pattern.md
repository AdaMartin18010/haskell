# 009 策略模式 (Strategy Pattern)

## 1. 理论基础

### 1.1 模式定义

策略模式是一种行为型设计模式，定义一系列算法，把它们封装起来，并且使它们可以互相替换。策略模式让算法独立于使用它的客户而变化。

### 1.2 核心概念

- **Strategy（策略）**: 定义所有支持的算法的公共接口
- **ConcreteStrategy（具体策略）**: 实现了Strategy接口的具体算法类
- **Context（上下文）**: 维护一个对Strategy对象的引用，用Strategy对象来配置它的行为

### 1.3 设计原则

- **开闭原则**: 可以添加新的策略而不修改现有代码
- **单一职责**: 每个策略只负责一个算法
- **依赖倒置**: 上下文依赖于抽象策略接口

### 1.4 优缺点分析

**优点:**

- 算法可以自由切换
- 避免使用多重条件语句
- 扩展性良好
- 符合开闭原则

**缺点:**

- 策略类会增多
- 所有策略类都需要对外暴露
- 策略对象可能变得复杂

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Strategy a where
  algorithm :: a -> [Int] -> [Int]
  getDescription :: a -> String
  getComplexity :: a -> String

-- 上下文接口
class Context a where
  setStrategy :: a -> Strategy -> a
  executeStrategy :: a -> [Int] -> [Int]
  getCurrentStrategy :: a -> String
```

### 2.2 扩展接口

```haskell
-- 支持参数的策略接口
class (Strategy a) => ParameterizedStrategy a where
  setParameters :: a -> [String] -> a
  getParameters :: a -> [String]
  
-- 支持组合的策略接口
class (Strategy a) => CompositeStrategy a where
  addStrategy :: a -> Strategy -> a
  removeStrategy :: a -> Strategy -> Maybe a
  getStrategies :: a -> [Strategy]
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 策略接口
class Strategy a where
  algorithm :: a -> [Int] -> [Int]
  getDescription :: a -> String
  getComplexity :: a -> String

-- 具体策略：冒泡排序
data BubbleSortStrategy = BubbleSortStrategy deriving Show

instance Strategy BubbleSortStrategy where
  algorithm _ xs = bubbleSort xs
    where
      bubbleSort [] = []
      bubbleSort xs = bubbleSort (init sorted) ++ [last sorted]
        where
          sorted = bubblePass xs
          bubblePass [] = []
          bubblePass [x] = [x]
          bubblePass (x:y:ys) = 
            if x <= y 
            then x : bubblePass (y:ys)
            else y : bubblePass (x:ys)
  
  getDescription _ = "冒泡排序"
  getComplexity _ = "O(n²)"

-- 具体策略：快速排序
data QuickSortStrategy = QuickSortStrategy deriving Show

instance Strategy QuickSortStrategy where
  algorithm _ xs = quickSort xs
    where
      quickSort [] = []
      quickSort (x:xs) = 
        quickSort (filter (<= x) xs) ++ [x] ++ quickSort (filter (> x) xs)
  
  getDescription _ = "快速排序"
  getComplexity _ = "O(n log n)"

-- 具体策略：归并排序
data MergeSortStrategy = MergeSortStrategy deriving Show

instance Strategy MergeSortStrategy where
  algorithm _ xs = mergeSort xs
    where
      mergeSort [] = []
      mergeSort [x] = [x]
      mergeSort xs = 
        let (left, right) = splitAt (length xs `div` 2) xs
        in merge (mergeSort left) (mergeSort right)
      
      merge [] ys = ys
      merge xs [] = xs
      merge (x:xs) (y:ys) = 
        if x <= y 
        then x : merge xs (y:ys)
        else y : merge (x:xs) ys
  
  getDescription _ = "归并排序"
  getComplexity _ = "O(n log n)"

-- 上下文
data Context = Context {
  strategy :: Maybe Strategy,
  dataSet :: [Int]
} deriving Show

newContext :: Context
newContext = Context Nothing []

setStrategy :: Context -> Strategy -> Context
setStrategy context newStrategy = context { strategy = Just newStrategy }

executeStrategy :: Context -> [Int] -> [Int]
executeStrategy context dataSet = 
  case strategy context of
    Just s -> algorithm s dataSet
    Nothing -> dataSet

getCurrentStrategy :: Context -> String
getCurrentStrategy context = 
  case strategy context of
    Just s -> getDescription s
    Nothing -> "未设置策略"

-- 策略工厂
data StrategyFactory = StrategyFactory {
  strategies :: Map String Strategy
}

createStrategyFactory :: StrategyFactory
createStrategyFactory = StrategyFactory $ Map.fromList [
  ("bubble", BubbleSortStrategy),
  ("quick", QuickSortStrategy),
  ("merge", MergeSortStrategy)
]

getStrategy :: StrategyFactory -> String -> Maybe Strategy
getStrategy factory name = Map.lookup name (strategies factory)

-- 使用示例
main :: IO ()
main = do
  let factory = createStrategyFactory
  let context = newContext
  
  putStrLn "策略模式示例:"
  
  let testData = [64, 34, 25, 12, 22, 11, 90]
  putStrLn $ "原始数据: " ++ show testData
  
  -- 使用冒泡排序
  let context1 = setStrategy context BubbleSortStrategy
  let result1 = executeStrategy context1 testData
  putStrLn $ "冒泡排序结果: " ++ show result1
  putStrLn $ "策略描述: " ++ getCurrentStrategy context1
  putStrLn $ "时间复杂度: " ++ getComplexity BubbleSortStrategy
  
  -- 使用快速排序
  let context2 = setStrategy context QuickSortStrategy
  let result2 = executeStrategy context2 testData
  putStrLn $ "快速排序结果: " ++ show result2
  putStrLn $ "策略描述: " ++ getCurrentStrategy context2
  putStrLn $ "时间复杂度: " ++ getComplexity QuickSortStrategy
  
  -- 使用归并排序
  let context3 = setStrategy context MergeSortStrategy
  let result3 = executeStrategy context3 testData
  putStrLn $ "归并排序结果: " ++ show result3
  putStrLn $ "策略描述: " ++ getCurrentStrategy context3
  putStrLn $ "时间复杂度: " ++ getComplexity MergeSortStrategy
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 策略trait
trait Strategy {
    fn algorithm(&self, data: &[i32]) -> Vec<i32>;
    fn get_description(&self) -> String;
    fn get_complexity(&self) -> String;
}

// 冒泡排序策略
#[derive(Debug)]
struct BubbleSortStrategy;

impl Strategy for BubbleSortStrategy {
    fn algorithm(&self, data: &[i32]) -> Vec<i32> {
        let mut result = data.to_vec();
        let len = result.len();
        
        for i in 0..len {
            for j in 0..len - i - 1 {
                if result[j] > result[j + 1] {
                    result.swap(j, j + 1);
                }
            }
        }
        result
    }
    
    fn get_description(&self) -> String {
        "冒泡排序".to_string()
    }
    
    fn get_complexity(&self) -> String {
        "O(n²)".to_string()
    }
}

// 快速排序策略
#[derive(Debug)]
struct QuickSortStrategy;

impl Strategy for QuickSortStrategy {
    fn algorithm(&self, data: &[i32]) -> Vec<i32> {
        if data.len() <= 1 {
            return data.to_vec();
        }
        
        let pivot = data[0];
        let mut left = Vec::new();
        let mut right = Vec::new();
        
        for &item in &data[1..] {
            if item <= pivot {
                left.push(item);
            } else {
                right.push(item);
            }
        }
        
        let mut result = self.algorithm(&left);
        result.push(pivot);
        result.extend(self.algorithm(&right));
        result
    }
    
    fn get_description(&self) -> String {
        "快速排序".to_string()
    }
    
    fn get_complexity(&self) -> String {
        "O(n log n)".to_string()
    }
}

// 归并排序策略
#[derive(Debug)]
struct MergeSortStrategy;

impl Strategy for MergeSortStrategy {
    fn algorithm(&self, data: &[i32]) -> Vec<i32> {
        if data.len() <= 1 {
            return data.to_vec();
        }
        
        let mid = data.len() / 2;
        let left = self.algorithm(&data[..mid]);
        let right = self.algorithm(&data[mid..]);
        
        self.merge(&left, &right)
    }
    
    fn merge(&self, left: &[i32], right: &[i32]) -> Vec<i32> {
        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;
        
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                result.push(left[i]);
                i += 1;
            } else {
                result.push(right[j]);
                j += 1;
            }
        }
        
        result.extend_from_slice(&left[i..]);
        result.extend_from_slice(&right[j..]);
        result
    }
    
    fn get_description(&self) -> String {
        "归并排序".to_string()
    }
    
    fn get_complexity(&self) -> String {
        "O(n log n)".to_string()
    }
}

// 上下文
#[derive(Debug)]
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
    
    fn execute_strategy(&self, data: &[i32]) -> Vec<i32> {
        match &self.strategy {
            Some(s) => s.algorithm(data),
            None => data.to_vec(),
        }
    }
    
    fn get_current_strategy(&self) -> String {
        match &self.strategy {
            Some(s) => s.get_description(),
            None => "未设置策略".to_string(),
        }
    }
    
    fn get_complexity(&self) -> String {
        match &self.strategy {
            Some(s) => s.get_complexity(),
            None => "未知".to_string(),
        }
    }
}

// 策略工厂
struct StrategyFactory {
    strategies: HashMap<String, Box<dyn Strategy>>,
}

impl StrategyFactory {
    fn new() -> Self {
        let mut strategies = HashMap::new();
        strategies.insert("bubble".to_string(), Box::new(BubbleSortStrategy));
        strategies.insert("quick".to_string(), Box::new(QuickSortStrategy));
        strategies.insert("merge".to_string(), Box::new(MergeSortStrategy));
        
        StrategyFactory { strategies }
    }
    
    fn get_strategy(&self, name: &str) -> Option<Box<dyn Strategy>> {
        self.strategies.get(name).cloned()
    }
    
    fn list_strategies(&self) -> Vec<String> {
        self.strategies.keys().cloned().collect()
    }
}

// 使用示例
fn main() {
    let factory = StrategyFactory::new();
    let mut context = Context::new();
    
    let test_data = vec![64, 34, 25, 12, 22, 11, 90];
    println!("策略模式示例:");
    println!("原始数据: {:?}", test_data);
    
    // 使用冒泡排序
    if let Some(strategy) = factory.get_strategy("bubble") {
        context.set_strategy(strategy);
        let result = context.execute_strategy(&test_data);
        println!("冒泡排序结果: {:?}", result);
        println!("策略描述: {}", context.get_current_strategy());
        println!("时间复杂度: {}", context.get_complexity());
    }
    
    // 使用快速排序
    if let Some(strategy) = factory.get_strategy("quick") {
        context.set_strategy(strategy);
        let result = context.execute_strategy(&test_data);
        println!("快速排序结果: {:?}", result);
        println!("策略描述: {}", context.get_current_strategy());
        println!("时间复杂度: {}", context.get_complexity());
    }
    
    // 使用归并排序
    if let Some(strategy) = factory.get_strategy("merge") {
        context.set_strategy(strategy);
        let result = context.execute_strategy(&test_data);
        println!("归并排序结果: {:?}", result);
        println!("策略描述: {}", context.get_current_strategy());
        println!("时间复杂度: {}", context.get_complexity());
    }
}
```

### 3.3 Lean实现

```lean
-- 策略类型
inductive Strategy where
  | BubbleSort : Strategy
  | QuickSort : Strategy
  | MergeSort : Strategy

-- 算法实现
def algorithm : Strategy → List Int → List Int
  | Strategy.BubbleSort, xs => bubbleSort xs
  | Strategy.QuickSort, xs => quickSort xs
  | Strategy.MergeSort, xs => mergeSort xs

-- 冒泡排序
def bubbleSort : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: xs => 
    if x ≤ y then x :: bubbleSort (y :: xs)
    else y :: bubbleSort (x :: xs)

-- 快速排序
def quickSort : List Int → List Int
  | [] => []
  | x :: xs => 
    let smaller := xs.filter (· ≤ x)
    let larger := xs.filter (· > x)
    quickSort smaller ++ [x] ++ quickSort larger

-- 归并排序
def mergeSort : List Int → List Int
  | [] => []
  | [x] => [x]
  | xs => 
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    merge (mergeSort left) (mergeSort right)

-- 归并函数
def merge : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => 
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

-- 获取描述
def getDescription : Strategy → String
  | Strategy.BubbleSort => "冒泡排序"
  | Strategy.QuickSort => "快速排序"
  | Strategy.MergeSort => "归并排序"

-- 获取复杂度
def getComplexity : Strategy → String
  | Strategy.BubbleSort => "O(n²)"
  | Strategy.QuickSort => "O(n log n)"
  | Strategy.MergeSort => "O(n log n)"

-- 上下文类型
structure Context where
  strategy : Option Strategy

-- 创建上下文
def newContext : Context := { strategy := none }

-- 设置策略
def setStrategy (context : Context) (strategy : Strategy) : Context :=
  { context with strategy := some strategy }

-- 执行策略
def executeStrategy (context : Context) (data : List Int) : List Int :=
  match context.strategy with
  | some s => algorithm s data
  | none => data

-- 获取当前策略描述
def getCurrentStrategy (context : Context) : String :=
  match context.strategy with
  | some s => getDescription s
  | none => "未设置策略"

-- 使用示例
def main : IO Unit := do
  let testData := [64, 34, 25, 12, 22, 11, 90]
  IO.println "策略模式示例:"
  IO.println s!"原始数据: {testData}"
  
  let context := newContext
  
  -- 使用冒泡排序
  let context1 := setStrategy context Strategy.BubbleSort
  let result1 := executeStrategy context1 testData
  IO.println s!"冒泡排序结果: {result1}"
  IO.println s!"策略描述: {getCurrentStrategy context1}"
  IO.println s!"时间复杂度: {getComplexity Strategy.BubbleSort}"
  
  -- 使用快速排序
  let context2 := setStrategy context Strategy.QuickSort
  let result2 := executeStrategy context2 testData
  IO.println s!"快速排序结果: {result2}"
  IO.println s!"策略描述: {getCurrentStrategy context2}"
  IO.println s!"时间复杂度: {getComplexity Strategy.QuickSort}"
  
  -- 使用归并排序
  let context3 := setStrategy context Strategy.MergeSort
  let result3 := executeStrategy context3 testData
  IO.println s!"归并排序结果: {result3}"
  IO.println s!"策略描述: {getCurrentStrategy context3}"
  IO.println s!"时间复杂度: {getComplexity Strategy.MergeSort}"
```

## 4. 工程实践

### 4.1 设计考虑

- **策略选择**: 如何选择合适的策略
- **性能优化**: 避免不必要的策略切换
- **内存管理**: 合理管理策略对象
- **错误处理**: 处理策略执行失败的情况

### 4.2 实现模式

```haskell
-- 带缓存的策略
data CachedStrategy a = CachedStrategy {
  strategy :: a,
  cache :: MVar (Map String String)
}

-- 异步策略执行器
data AsyncStrategyExecutor = AsyncStrategyExecutor {
  threadPool :: ThreadPool,
  strategies :: [Strategy]
}

-- 带监控的策略
data MonitoredStrategy a = MonitoredStrategy {
  strategy :: a,
  metrics :: MVar StrategyMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data StrategyError = 
  StrategyExecutionFailed String
  | InvalidStrategy String
  | StrategyNotFound String

-- 安全执行
safeExecuteStrategy :: Strategy a => a -> [Int] -> IO (Either StrategyError [Int])
safeExecuteStrategy strategy dataSet = 
  try (return $ algorithm strategy dataSet) >>= \case
    Left e -> return $ Left $ StrategyExecutionFailed (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略

- **策略结果缓存**: 缓存相同输入的策略执行结果
- **策略对象缓存**: 缓存策略对象避免重复创建
- **性能指标缓存**: 缓存策略的性能指标

### 5.2 策略选择优化

```haskell
-- 智能策略选择器
data SmartStrategySelector = SmartStrategySelector {
  strategies :: [Strategy],
  performanceHistory :: MVar (Map String Double)
}

selectOptimalStrategy :: SmartStrategySelector -> [Int] -> IO Strategy
selectOptimalStrategy selector dataSet = do
  history <- readMVar (performanceHistory selector)
  let optimalStrategy = selectBestStrategy history dataSet
  return optimalStrategy
```

### 5.3 并行策略执行

```haskell
-- 并行策略执行器
data ParallelStrategyExecutor = ParallelStrategyExecutor {
  strategies :: [Strategy],
  executor :: ThreadPool
}

executeParallel :: ParallelStrategyExecutor -> [Int] -> IO [[Int]]
executeParallel executor dataSet = 
  mapConcurrently (\s -> algorithm s dataSet) (strategies executor)
```

## 6. 应用场景

### 6.1 排序算法选择

```haskell
-- 排序策略管理器
data SortingStrategyManager = SortingStrategyManager {
  strategies :: Map String SortingStrategy,
  currentStrategy :: IORef SortingStrategy
}

selectSortingStrategy :: SortingStrategyManager -> String -> IO ()
selectSortingStrategy manager strategyName = 
  case Map.lookup strategyName (strategies manager) of
    Just strategy -> writeIORef (currentStrategy manager) strategy
    Nothing -> putStrLn $ "未知排序策略: " ++ strategyName
```

### 6.2 支付方式选择

```haskell
-- 支付策略
data PaymentStrategy = PaymentStrategy {
  processPayment :: Double -> IO Bool,
  getDescription :: String
}

-- 支付策略管理器
data PaymentManager = PaymentManager {
  strategies :: Map String PaymentStrategy,
  currentStrategy :: IORef PaymentStrategy
}

processPayment :: PaymentManager -> Double -> IO Bool
processPayment manager amount = do
  strategy <- readIORef (currentStrategy manager)
  processPayment strategy amount
```

### 6.3 压缩算法选择

```haskell
-- 压缩策略
data CompressionStrategy = CompressionStrategy {
  compress :: String -> String,
  decompress :: String -> String,
  getCompressionRatio :: Double
}

-- 压缩策略管理器
data CompressionManager = CompressionManager {
  strategies :: [CompressionStrategy],
  currentStrategy :: IORef CompressionStrategy
}

compressData :: CompressionManager -> String -> IO String
compressData manager data = do
  strategy <- readIORef (currentStrategy manager)
  return $ compress strategy data
```

### 6.4 路由策略选择

```haskell
-- 路由策略
data RoutingStrategy = RoutingStrategy {
  findRoute :: String -> String -> [String],
  getRouteCost :: String -> String -> Double
}

-- 路由策略管理器
data RoutingManager = RoutingManager {
  strategies :: Map String RoutingStrategy,
  currentStrategy :: IORef RoutingStrategy
}

findOptimalRoute :: RoutingManager -> String -> String -> IO [String]
findOptimalRoute manager start end = do
  strategy <- readIORef (currentStrategy manager)
  return $ findRoute strategy start end
```

## 7. 最佳实践

### 7.1 设计原则

- **策略接口简单**: 保持策略接口的简洁性
- **避免策略复杂化**: 避免策略类过于复杂
- **支持策略组合**: 允许策略的组合使用
- **性能考虑**: 考虑策略切换的性能开销

### 7.2 实现建议

```haskell
-- 策略工厂
class StrategyFactory a where
  createStrategy :: String -> Maybe a
  listStrategies :: [String]
  validateStrategy :: a -> Bool

-- 策略注册表
data StrategyRegistry = StrategyRegistry {
  strategies :: Map String (forall a. Strategy a => a),
  metadata :: Map String String
}

-- 线程安全策略管理器
data ThreadSafeStrategyManager = ThreadSafeStrategyManager {
  manager :: MVar StrategyManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 策略测试
testStrategy :: Strategy a => a -> [Int] -> Bool
testStrategy strategy dataSet = 
  let result = algorithm strategy dataSet
  in isSorted result

-- 性能测试
benchmarkStrategy :: Strategy a => a -> [Int] -> IO Double
benchmarkStrategy strategy dataSet = do
  start <- getCurrentTime
  replicateM_ 1000 $ algorithm strategy dataSet
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的策略类型
- **序列化**: 支持策略的序列化和反序列化
- **版本控制**: 支持策略的版本管理
- **分布式**: 支持跨网络的策略执行

## 8. 总结

策略模式是封装算法的强大工具，通过将算法封装为独立的策略对象提供了灵活的选择和切换能力。在实现时需要注意策略接口的简洁性、性能优化和错误处理。该模式在排序算法、支付方式、压缩算法、路由策略等场景中都有广泛应用。
