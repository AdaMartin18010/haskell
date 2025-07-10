# 005 外观模式 (Facade Pattern)

## 1. 理论基础

### 1.1 模式定义
外观模式是一种结构型设计模式，为子系统中的一组接口提供一个统一的高层接口，使子系统更易使用。外观模式通过封装复杂子系统，简化客户端的调用，降低系统的耦合度。

### 1.2 核心概念
- **Facade（外观）**: 为子系统提供一个统一的高层接口
- **Subsystem（子系统）**: 实现子系统的功能，被外观对象调用
- **Client（客户端）**: 通过外观对象访问子系统
- **Complex Subsystem（复杂子系统）**: 包含多个相互依赖的类

### 1.3 设计原则
- **单一职责**: 外观只负责简化接口，不处理业务逻辑
- **开闭原则**: 支持扩展新的子系统
- **依赖倒置**: 客户端依赖外观抽象而非具体子系统

### 1.4 优缺点分析
**优点：**
- 简化客户端调用
- 降低系统耦合度
- 提供统一接口
- 易于维护和扩展

**缺点：**
- 可能成为"上帝对象"
- 增加系统复杂性
- 可能违反开闭原则
- 调试困难

## 2. 接口设计

### 2.1 核心接口
```haskell
-- Haskell接口设计
class Facade a where
  operation :: a -> IO String
  complexOperation :: a -> String -> IO String
  errorHandling :: a -> IO (Either String String)

-- 子系统接口
class Subsystem a where
  subsystemOperation :: a -> IO String
  validateInput :: a -> String -> Bool
```

### 2.2 扩展接口
```haskell
-- 支持配置的外观
class (Facade a) => ConfigurableFacade a where
  setConfiguration :: a -> Configuration -> a
  getConfiguration :: a -> Configuration
  
-- 支持监控的外观
class (Facade a) => MonitoredFacade a where
  getMetrics :: a -> IO Metrics
  logOperation :: a -> String -> IO ()
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 子系统A
data SubsystemA = SubsystemA {
  name :: String,
  status :: String
} deriving Show

subsystemAOperation :: SubsystemA -> IO String
subsystemAOperation subsystem = do
  putStrLn $ "子系统A " ++ name subsystem ++ " 执行操作"
  return $ "A完成: " ++ status subsystem

validateSubsystemA :: SubsystemA -> String -> Bool
validateSubsystemA subsystem input = 
  length input > 0 && status subsystem == "ready"

-- 子系统B
data SubsystemB = SubsystemB {
  name :: String,
  config :: String
} deriving Show

subsystemBOperation :: SubsystemB -> IO String
subsystemBOperation subsystem = do
  putStrLn $ "子系统B " ++ name subsystem ++ " 执行操作"
  return $ "B完成: " ++ config subsystem

validateSubsystemB :: SubsystemB -> String -> Bool
validateSubsystemB subsystem input = 
  length input > 0 && config subsystem /= ""

-- 子系统C
data SubsystemC = SubsystemC {
  name :: String,
  cache :: IORef (Map String String)
} deriving Show

subsystemCOperation :: SubsystemC -> String -> IO String
subsystemCOperation subsystem input = do
  putStrLn $ "子系统C " ++ name subsystem ++ " 处理输入: " ++ input
  cacheMap <- readIORef (cache subsystem)
  case Map.lookup input cacheMap of
    Just result -> do
      putStrLn "从缓存返回结果"
      return result
    Nothing -> do
      let result = "C处理结果: " ++ input
      modifyIORef (cache subsystem) (Map.insert input result)
      return result

-- 外观类
data Facade = Facade {
  subsystemA :: SubsystemA,
  subsystemB :: SubsystemB,
  subsystemC :: SubsystemC,
  logger :: Logger
} deriving Show

instance Facade Facade where
  operation facade = do
    putStrLn "外观模式: 开始执行操作"
    
    -- 验证子系统
    let aValid = validateSubsystemA (subsystemA facade) "test"
    let bValid = validateSubsystemB (subsystemB facade) "test"
    
    if aValid && bValid
    then do
      -- 执行子系统操作
      resultA <- subsystemAOperation (subsystemA facade)
      resultB <- subsystemBOperation (subsystemB facade)
      
      -- 记录日志
      logOperation (logger facade) ("操作完成: " ++ resultA ++ " + " ++ resultB)
      
      return $ resultA ++ " + " ++ resultB
    else do
      logOperation (logger facade) "操作失败: 子系统验证失败"
      return "操作失败"
  
  complexOperation facade input = do
    putStrLn $ "外观模式: 执行复杂操作，输入: " ++ input
    
    -- 验证输入
    let aValid = validateSubsystemA (subsystemA facade) input
    let bValid = validateSubsystemB (subsystemB facade) input
    
    if aValid && bValid
    then do
      -- 执行子系统操作
      resultA <- subsystemAOperation (subsystemA facade)
      resultB <- subsystemBOperation (subsystemB facade)
      resultC <- subsystemCOperation (subsystemC facade) input
      
      -- 记录日志
      logOperation (logger facade) ("复杂操作完成: " ++ resultA ++ " + " ++ resultB ++ " + " ++ resultC)
      
      return $ resultA ++ " + " ++ resultB ++ " + " ++ resultC
    else do
      logOperation (logger facade) "复杂操作失败: 输入验证失败"
      return "复杂操作失败"
  
  errorHandling facade = do
    putStrLn "外观模式: 错误处理操作"
    
    try (operation facade) >>= \case
      Left e -> do
        logOperation (logger facade) $ "错误: " ++ show e
        return $ Left $ "操作失败: " ++ show e
      Right result -> do
        logOperation (logger facade) $ "成功: " ++ result
        return $ Right result

-- 日志系统
data Logger = Logger {
  logLevel :: String,
  logBuffer :: IORef [String]
} deriving Show

newLogger :: String -> IO Logger
newLogger level = do
  bufferRef <- newIORef []
  return $ Logger level bufferRef

logOperation :: Logger -> String -> IO ()
logOperation logger message = do
  buffer <- readIORef (logBuffer logger)
  let timestamp = show (getCurrentTime)
  let logEntry = timestamp ++ " [" ++ logLevel logger ++ "] " ++ message
  writeIORef (logBuffer logger) (logEntry : buffer)
  putStrLn logEntry

-- 配置外观
data ConfigurableFacade = ConfigurableFacade {
  baseFacade :: Facade,
  configuration :: Configuration
} deriving Show

data Configuration = Configuration {
  timeout :: Int,
  retryCount :: Int,
  enableCache :: Bool
} deriving Show

instance Facade ConfigurableFacade where
  operation facade = do
    putStrLn $ "配置外观: 超时=" ++ show (timeout (configuration facade)) ++ 
               " 重试=" ++ show (retryCount (configuration facade))
    operation (baseFacade facade)
  
  complexOperation facade input = do
    if enableCache (configuration facade)
    then do
      putStrLn "使用缓存模式"
      complexOperation (baseFacade facade) input
    else do
      putStrLn "使用非缓存模式"
      complexOperation (baseFacade facade) input
  
  errorHandling facade = do
    let retries = retryCount (configuration facade)
    retryOperation (baseFacade facade) retries

retryOperation :: Facade -> Int -> IO (Either String String)
retryOperation facade 0 = errorHandling facade
retryOperation facade retries = do
  result <- errorHandling facade
  case result of
    Left _ -> do
      putStrLn $ "重试操作，剩余次数: " ++ show (retries - 1)
      retryOperation facade (retries - 1)
    Right _ -> return result

-- 监控外观
data MonitoredFacade = MonitoredFacade {
  baseFacade :: Facade,
  metrics :: IORef Metrics
} deriving Show

data Metrics = Metrics {
  operationCount :: Int,
  successCount :: Int,
  errorCount :: Int,
  averageTime :: Double
} deriving Show

instance Facade MonitoredFacade where
  operation facade = do
    start <- getCurrentTime
    result <- operation (baseFacade facade)
    end <- getCurrentTime
    
    -- 更新指标
    updateMetrics facade (diffUTCTime end start) True
    return result
  
  complexOperation facade input = do
    start <- getCurrentTime
    result <- complexOperation (baseFacade facade) input
    end <- getCurrentTime
    
    -- 更新指标
    updateMetrics facade (diffUTCTime end start) True
    return result
  
  errorHandling facade = do
    start <- getCurrentTime
    result <- errorHandling (baseFacade facade)
    end <- getCurrentTime
    
    -- 更新指标
    case result of
      Left _ -> updateMetrics facade (diffUTCTime end start) False
      Right _ -> updateMetrics facade (diffUTCTime end start) True
    
    return result

updateMetrics :: MonitoredFacade -> NominalDiffTime -> Bool -> IO ()
updateMetrics facade duration success = do
  currentMetrics <- readIORef (metrics facade)
  let newCount = operationCount currentMetrics + 1
  let newSuccessCount = if success then successCount currentMetrics + 1 else successCount currentMetrics
  let newErrorCount = if success then errorCount currentMetrics else errorCount currentMetrics + 1
  let newAverageTime = (averageTime currentMetrics * fromIntegral (operationCount currentMetrics) + realToFrac duration) / fromIntegral newCount
  
  let newMetrics = Metrics newCount newSuccessCount newErrorCount newAverageTime
  writeIORef (metrics facade) newMetrics

-- 使用示例
main :: IO ()
main = do
  putStrLn "外观模式示例:"
  
  -- 创建子系统
  let subsystemA = SubsystemA "子系统A" "ready"
  let subsystemB = SubsystemB "子系统B" "config"
  cacheRef <- newIORef Map.empty
  let subsystemC = SubsystemC "子系统C" cacheRef
  
  -- 创建日志器
  logger <- newLogger "INFO"
  
  -- 创建外观
  let facade = Facade subsystemA subsystemB subsystemC logger
  
  putStrLn "\n=== 基本外观 ==="
  result1 <- operation facade
  putStrLn result1
  
  putStrLn "\n=== 复杂操作 ==="
  result2 <- complexOperation facade "test input"
  putStrLn result2
  
  putStrLn "\n=== 错误处理 ==="
  result3 <- errorHandling facade
  case result3 of
    Left error -> putStrLn $ "错误: " ++ error
    Right success -> putStrLn $ "成功: " ++ success
  
  -- 配置外观
  let config = Configuration 5000 3 True
  let configFacade = ConfigurableFacade facade config
  
  putStrLn "\n=== 配置外观 ==="
  result4 <- operation configFacade
  putStrLn result4
  
  -- 监控外观
  metricsRef <- newIORef (Metrics 0 0 0 0.0)
  let monitoredFacade = MonitoredFacade facade metricsRef
  
  putStrLn "\n=== 监控外观 ==="
  result5 <- operation monitoredFacade
  putStrLn result5
  
  -- 显示指标
  finalMetrics <- readIORef metricsRef
  putStrLn $ "操作次数: " ++ show (operationCount finalMetrics)
  putStrLn $ "成功次数: " ++ show (successCount finalMetrics)
  putStrLn $ "错误次数: " ++ show (errorCount finalMetrics)
  putStrLn $ "平均时间: " ++ show (averageTime finalMetrics)
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 子系统A
#[derive(Debug)]
struct SubsystemA {
    name: String,
    status: String,
}

impl SubsystemA {
    fn new(name: String, status: String) -> Self {
        SubsystemA { name, status }
    }
    
    fn operation(&self) -> String {
        println!("子系统A {} 执行操作", self.name);
        format!("A完成: {}", self.status)
    }
    
    fn validate(&self, input: &str) -> bool {
        !input.is_empty() && self.status == "ready"
    }
}

// 子系统B
#[derive(Debug)]
struct SubsystemB {
    name: String,
    config: String,
}

impl SubsystemB {
    fn new(name: String, config: String) -> Self {
        SubsystemB { name, config }
    }
    
    fn operation(&self) -> String {
        println!("子系统B {} 执行操作", self.name);
        format!("B完成: {}", self.config)
    }
    
    fn validate(&self, input: &str) -> bool {
        !input.is_empty() && !self.config.is_empty()
    }
}

// 子系统C
#[derive(Debug)]
struct SubsystemC {
    name: String,
    cache: Arc<Mutex<HashMap<String, String>>>,
}

impl SubsystemC {
    fn new(name: String) -> Self {
        SubsystemC {
            name,
            cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn operation(&self, input: &str) -> String {
        println!("子系统C {} 处理输入: {}", self.name, input);
        let mut cache = self.cache.lock().unwrap();
        if let Some(result) = cache.get(input) {
            println!("从缓存返回结果");
            result.clone()
        } else {
            let result = format!("C处理结果: {}", input);
            cache.insert(input.to_string(), result.clone());
            result
        }
    }
}

// 日志系统
#[derive(Debug)]
struct Logger {
    level: String,
    buffer: Arc<Mutex<Vec<String>>>,
}

impl Logger {
    fn new(level: String) -> Self {
        Logger {
            level,
            buffer: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    fn log(&self, message: &str) {
        let timestamp = chrono::Utc::now().to_rfc3339();
        let log_entry = format!("{} [{}] {}", timestamp, self.level, message);
        let mut buffer = self.buffer.lock().unwrap();
        buffer.push(log_entry.clone());
        println!("{}", log_entry);
    }
}

// 外观类
#[derive(Debug)]
struct Facade {
    subsystem_a: SubsystemA,
    subsystem_b: SubsystemB,
    subsystem_c: SubsystemC,
    logger: Logger,
}

impl Facade {
    fn new() -> Self {
        Facade {
            subsystem_a: SubsystemA::new("子系统A".to_string(), "ready".to_string()),
            subsystem_b: SubsystemB::new("子系统B".to_string(), "config".to_string()),
            subsystem_c: SubsystemC::new("子系统C".to_string()),
            logger: Logger::new("INFO".to_string()),
        }
    }
    
    fn operation(&self) -> String {
        println!("外观模式: 开始执行操作");
        
        // 验证子系统
        let a_valid = self.subsystem_a.validate("test");
        let b_valid = self.subsystem_b.validate("test");
        
        if a_valid && b_valid {
            // 执行子系统操作
            let result_a = self.subsystem_a.operation();
            let result_b = self.subsystem_b.operation();
            
            // 记录日志
            self.logger.log(&format!("操作完成: {} + {}", result_a, result_b));
            
            format!("{} + {}", result_a, result_b)
        } else {
            self.logger.log("操作失败: 子系统验证失败");
            "操作失败".to_string()
        }
    }
    
    fn complex_operation(&self, input: &str) -> String {
        println!("外观模式: 执行复杂操作，输入: {}", input);
        
        // 验证输入
        let a_valid = self.subsystem_a.validate(input);
        let b_valid = self.subsystem_b.validate(input);
        
        if a_valid && b_valid {
            // 执行子系统操作
            let result_a = self.subsystem_a.operation();
            let result_b = self.subsystem_b.operation();
            let result_c = self.subsystem_c.operation(input);
            
            // 记录日志
            self.logger.log(&format!("复杂操作完成: {} + {} + {}", result_a, result_b, result_c));
            
            format!("{} + {} + {}", result_a, result_b, result_c)
        } else {
            self.logger.log("复杂操作失败: 输入验证失败");
            "复杂操作失败".to_string()
        }
    }
    
    fn error_handling(&self) -> Result<String, String> {
        println!("外观模式: 错误处理操作");
        
        match std::panic::catch_unwind(|| self.operation()) {
            Ok(result) => {
                self.logger.log(&format!("成功: {}", result));
                Ok(result)
            }
            Err(_) => {
                self.logger.log("错误: 操作失败");
                Err("操作失败".to_string())
            }
        }
    }
}

// 配置外观
#[derive(Debug)]
struct ConfigurableFacade {
    base_facade: Facade,
    configuration: Configuration,
}

#[derive(Debug)]
struct Configuration {
    timeout: u64,
    retry_count: u32,
    enable_cache: bool,
}

impl ConfigurableFacade {
    fn new(configuration: Configuration) -> Self {
        ConfigurableFacade {
            base_facade: Facade::new(),
            configuration,
        }
    }
    
    fn operation(&self) -> String {
        println!(
            "配置外观: 超时={} 重试={}",
            self.configuration.timeout, self.configuration.retry_count
        );
        self.base_facade.operation()
    }
    
    fn complex_operation(&self, input: &str) -> String {
        if self.configuration.enable_cache {
            println!("使用缓存模式");
        } else {
            println!("使用非缓存模式");
        }
        self.base_facade.complex_operation(input)
    }
    
    fn error_handling(&self) -> Result<String, String> {
        self.retry_operation(self.configuration.retry_count)
    }
    
    fn retry_operation(&self, retries: u32) -> Result<String, String> {
        if retries == 0 {
            self.base_facade.error_handling()
        } else {
            match self.base_facade.error_handling() {
                Ok(result) => Ok(result),
                Err(_) => {
                    println!("重试操作，剩余次数: {}", retries - 1);
                    self.retry_operation(retries - 1)
                }
            }
        }
    }
}

// 监控外观
#[derive(Debug)]
struct MonitoredFacade {
    base_facade: Facade,
    metrics: Arc<Mutex<Metrics>>,
}

#[derive(Debug)]
struct Metrics {
    operation_count: u32,
    success_count: u32,
    error_count: u32,
    average_time: f64,
}

impl MonitoredFacade {
    fn new() -> Self {
        MonitoredFacade {
            base_facade: Facade::new(),
            metrics: Arc::new(Mutex::new(Metrics {
                operation_count: 0,
                success_count: 0,
                error_count: 0,
                average_time: 0.0,
            })),
        }
    }
    
    fn operation(&self) -> String {
        let start = Instant::now();
        let result = self.base_facade.operation();
        let duration = start.elapsed();
        
        // 更新指标
        self.update_metrics(duration, true);
        result
    }
    
    fn complex_operation(&self, input: &str) -> String {
        let start = Instant::now();
        let result = self.base_facade.complex_operation(input);
        let duration = start.elapsed();
        
        // 更新指标
        self.update_metrics(duration, true);
        result
    }
    
    fn error_handling(&self) -> Result<String, String> {
        let start = Instant::now();
        let result = self.base_facade.error_handling();
        let duration = start.elapsed();
        
        // 更新指标
        let success = result.is_ok();
        self.update_metrics(duration, success);
        result
    }
    
    fn update_metrics(&self, duration: Duration, success: bool) {
        let mut metrics = self.metrics.lock().unwrap();
        metrics.operation_count += 1;
        if success {
            metrics.success_count += 1;
        } else {
            metrics.error_count += 1;
        }
        let duration_secs = duration.as_secs_f64();
        metrics.average_time = (metrics.average_time * (metrics.operation_count - 1) as f64 + duration_secs) / metrics.operation_count as f64;
    }
    
    fn get_metrics(&self) -> Metrics {
        self.metrics.lock().unwrap().clone()
    }
}

// 使用示例
fn main() {
    println!("外观模式示例:");
    
    // 基本外观
    let facade = Facade::new();
    
    println!("\n=== 基本外观 ===");
    println!("{}", facade.operation());
    
    println!("\n=== 复杂操作 ===");
    println!("{}", facade.complex_operation("test input"));
    
    println!("\n=== 错误处理 ===");
    match facade.error_handling() {
        Ok(result) => println!("成功: {}", result),
        Err(error) => println!("错误: {}", error),
    }
    
    // 配置外观
    let config = Configuration {
        timeout: 5000,
        retry_count: 3,
        enable_cache: true,
    };
    let config_facade = ConfigurableFacade::new(config);
    
    println!("\n=== 配置外观 ===");
    println!("{}", config_facade.operation());
    
    // 监控外观
    let monitored_facade = MonitoredFacade::new();
    
    println!("\n=== 监控外观 ===");
    println!("{}", monitored_facade.operation());
    
    // 显示指标
    let metrics = monitored_facade.get_metrics();
    println!("操作次数: {}", metrics.operation_count);
    println!("成功次数: {}", metrics.success_count);
    println!("错误次数: {}", metrics.error_count);
    println!("平均时间: {:.2}s", metrics.average_time);
}
```

### 3.3 Lean实现

```lean
-- 子系统A
structure SubsystemA where
  name : String
  status : String

def newSubsystemA (name : String) (status : String) : SubsystemA := {
  name := name,
  status := status
}

def subsystemAOperation (subsystem : SubsystemA) : IO String := do
  IO.println ("子系统A " ++ subsystem.name ++ " 执行操作")
  return ("A完成: " ++ subsystem.status)

def validateSubsystemA (subsystem : SubsystemA) (input : String) : Bool :=
  input.length > 0 && subsystem.status = "ready"

-- 子系统B
structure SubsystemB where
  name : String
  config : String

def newSubsystemB (name : String) (config : String) : SubsystemB := {
  name := name,
  config := config
}

def subsystemBOperation (subsystem : SubsystemB) : IO String := do
  IO.println ("子系统B " ++ subsystem.name ++ " 执行操作")
  return ("B完成: " ++ subsystem.config)

def validateSubsystemB (subsystem : SubsystemB) (input : String) : Bool :=
  input.length > 0 && subsystem.config.length > 0

-- 外观类
structure Facade where
  subsystemA : SubsystemA
  subsystemB : SubsystemB

def newFacade (a : SubsystemA) (b : SubsystemB) : Facade := {
  subsystemA := a,
  subsystemB := b
}

def operation (facade : Facade) : IO String := do
  IO.println "外观模式: 开始执行操作"
  
  -- 验证子系统
  let aValid := validateSubsystemA facade.subsystemA "test"
  let bValid := validateSubsystemB facade.subsystemB "test"
  
  if aValid && bValid
  then do
    -- 执行子系统操作
    resultA := subsystemAOperation facade.subsystemA
    resultB := subsystemBOperation facade.subsystemB
    
    IO.println ("操作完成: " ++ resultA ++ " + " ++ resultB)
    return (resultA ++ " + " ++ resultB)
  else do
    IO.println "操作失败: 子系统验证失败"
    return "操作失败"

def complexOperation (facade : Facade) (input : String) : IO String := do
  IO.println ("外观模式: 执行复杂操作，输入: " ++ input)
  
  -- 验证输入
  let aValid := validateSubsystemA facade.subsystemA input
  let bValid := validateSubsystemB facade.subsystemB input
  
  if aValid && bValid
  then do
    -- 执行子系统操作
    resultA := subsystemAOperation facade.subsystemA
    resultB := subsystemBOperation facade.subsystemB
    
    IO.println ("复杂操作完成: " ++ resultA ++ " + " ++ resultB)
    return (resultA ++ " + " ++ resultB)
  else do
    IO.println "复杂操作失败: 输入验证失败"
    return "复杂操作失败"

-- 使用示例
def main : IO Unit := do
  IO.println "外观模式示例:"
  
  -- 创建子系统
  let subsystemA := newSubsystemA "子系统A" "ready"
  let subsystemB := newSubsystemB "子系统B" "config"
  
  -- 创建外观
  let facade := newFacade subsystemA subsystemB
  
  IO.println "\n=== 基本外观 ==="
  result1 := operation facade
  IO.println result1
  
  IO.println "\n=== 复杂操作 ==="
  result2 := complexOperation facade "test input"
  IO.println result2
```

## 4. 工程实践

### 4.1 设计考虑
- **接口简化**: 确保外观提供简洁的接口
- **子系统封装**: 合理封装子系统复杂性
- **错误处理**: 统一处理子系统错误
- **性能优化**: 避免外观成为性能瓶颈

### 4.2 实现模式
```haskell
-- 分层外观
data LayeredFacade = LayeredFacade {
  presentationLayer :: PresentationFacade,
  businessLayer :: BusinessFacade,
  dataLayer :: DataFacade
}

-- 异步外观
data AsyncFacade = AsyncFacade {
  facade :: Facade,
  executor :: ThreadPool
}

-- 缓存外观
data CachedFacade = CachedFacade {
  facade :: Facade,
  cache :: MVar (Map String String)
}
```

### 4.3 错误处理
```haskell
-- 错误类型
data FacadeError = 
  SubsystemError String
  | ValidationError String
  | TimeoutError
  | ConfigurationError String

-- 安全外观操作
safeFacadeOperation :: Facade -> IO (Either FacadeError String)
safeFacadeOperation facade = 
  try (operation facade) >>= \case
    Left e -> return $ Left $ SubsystemError (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略
- **结果缓存**: 缓存外观操作结果
- **连接池**: 复用子系统连接
- **异步处理**: 非阻塞子系统调用

### 5.2 负载均衡
```haskell
-- 负载均衡外观
data LoadBalancedFacade = LoadBalancedFacade {
  facades :: [Facade],
  strategy :: LoadBalancingStrategy
}

data LoadBalancingStrategy = RoundRobin | LeastConnections | RandomChoice
```

### 5.3 监控和指标
- **性能监控**: 监控外观操作性能
- **错误统计**: 统计子系统错误
- **资源使用**: 监控子系统资源使用

## 6. 应用场景

### 6.1 复杂子系统封装
```haskell
-- 数据库外观
data DatabaseFacade = DatabaseFacade {
  connectionPool :: ConnectionPool,
  queryCache :: QueryCache,
  transactionManager :: TransactionManager
}

-- 数据库操作
executeQuery :: DatabaseFacade -> String -> IO QueryResult
executeQuery facade query = do
  -- 1. 验证查询
  validateQuery query
  -- 2. 检查缓存
  cachedResult <- getFromCache (queryCache facade) query
  case cachedResult of
    Just result -> return result
    Nothing -> do
      -- 3. 执行查询
      connection <- getConnection (connectionPool facade)
      result <- executeOnConnection connection query
      -- 4. 缓存结果
      putInCache (queryCache facade) query result
      return result
```

### 6.2 旧系统迁移
```haskell
-- 遗留系统外观
data LegacySystemFacade = LegacySystemFacade {
  legacyAdapter :: LegacyAdapter,
  modernInterface :: ModernInterface,
  migrationManager :: MigrationManager
}

-- 兼容性操作
legacyOperation :: LegacySystemFacade -> LegacyRequest -> IO ModernResponse
legacyOperation facade request = do
  -- 1. 转换请求格式
  modernRequest <- convertRequest (legacyAdapter facade) request
  -- 2. 执行现代操作
  modernResponse <- executeModernOperation (modernInterface facade) modernRequest
  -- 3. 转换响应格式
  convertResponse (legacyAdapter facade) modernResponse
```

### 6.3 分层架构
```haskell
-- 分层外观
data LayeredArchitectureFacade = LayeredArchitectureFacade {
  presentationFacade :: PresentationFacade,
  businessFacade :: BusinessFacade,
  dataFacade :: DataFacade
}

-- 分层操作
layeredOperation :: LayeredArchitectureFacade -> UserRequest -> IO UserResponse
layeredOperation facade request = do
  -- 1. 表示层处理
  validatedRequest <- validateRequest (presentationFacade facade) request
  -- 2. 业务层处理
  businessResult <- processBusinessLogic (businessFacade facade) validatedRequest
  -- 3. 数据层处理
  dataResult <- persistData (dataFacade facade) businessResult
  -- 4. 返回响应
  formatResponse (presentationFacade facade) dataResult
```

### 6.4 微服务网关
```haskell
-- 微服务外观
data MicroserviceFacade = MicroserviceFacade {
  serviceRegistry :: ServiceRegistry,
  loadBalancer :: LoadBalancer,
  circuitBreaker :: CircuitBreaker
}

-- 服务调用
callService :: MicroserviceFacade -> ServiceRequest -> IO ServiceResponse
callService facade request = do
  -- 1. 服务发现
  serviceInstance <- discoverService (serviceRegistry facade) (serviceName request)
  -- 2. 负载均衡
  selectedInstance <- selectInstance (loadBalancer facade) serviceInstance
  -- 3. 断路器检查
  if isCircuitOpen (circuitBreaker facade) selectedInstance
  then return $ fallbackResponse request
  else do
    -- 4. 调用服务
    response <- callServiceInstance selectedInstance request
    -- 5. 更新断路器状态
    updateCircuitBreaker (circuitBreaker facade) selectedInstance response
    return response
```

## 7. 最佳实践

### 7.1 设计原则
- **保持外观简单**: 避免外观成为"上帝对象"
- **合理封装**: 只封装必要的复杂性
- **接口稳定**: 确保外观接口的稳定性
- **错误处理**: 统一处理子系统错误

### 7.2 实现建议
```haskell
-- 外观工厂
class FacadeFactory a where
  createFacade :: String -> Maybe a
  listFacades :: [String]
  validateFacade :: a -> Bool

-- 外观注册表
data FacadeRegistry = FacadeRegistry {
  facades :: Map String (forall a. Facade a => a),
  metadata :: Map String String
}

-- 线程安全外观管理器
data ThreadSafeFacadeManager = ThreadSafeFacadeManager {
  manager :: MVar FacadeManager,
  lock :: MVar ()
}
```

### 7.3 测试策略
```haskell
-- 外观测试
testFacade :: Facade a => a -> Bool
testFacade facade = 
  -- 测试外观的基本功能
  True

-- 性能测试
benchmarkFacade :: Facade a => a -> IO Double
benchmarkFacade facade = do
  start <- getCurrentTime
  replicateM_ 1000 $ operation facade
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑
- **插件系统**: 支持动态加载新的外观类型
- **序列化**: 支持外观的序列化和反序列化
- **版本控制**: 支持外观接口的版本管理
- **分布式**: 支持跨网络的外观调用

## 8. 总结

外观模式是简化复杂系统的重要工具，通过提供统一的高层接口，降低了系统的耦合度和复杂度。在实现时需要注意外观的简洁性、子系统的合理封装和错误处理。该模式在复杂子系统封装、旧系统迁移、分层架构、微服务网关等场景中有广泛应用。
