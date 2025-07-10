# 007 观察者模式 (Observer Pattern)

## 1. 理论基础

### 1.1 模式定义

观察者模式是一种行为型设计模式，定义对象间的一种一对多的依赖关系，当一个对象的状态发生改变时，所有依赖于它的对象都得到通知并被自动更新。

### 1.2 核心概念

- **Subject（主题）**: 被观察的对象，维护观察者列表，提供注册和注销观察者的接口
- **Observer（观察者）**: 定义更新接口，当主题状态改变时被调用
- **ConcreteSubject（具体主题）**: 存储对具体观察者对象的引用，在状态改变时通知观察者
- **ConcreteObserver（具体观察者）**: 实现Observer的更新接口，以保持其状态与主题状态一致

### 1.3 设计原则

- **开闭原则**: 可以添加新的观察者而不修改主题
- **单一职责**: 主题负责状态管理，观察者负责响应变化
- **松耦合**: 主题和观察者之间松耦合

### 1.4 优缺点分析

**优点:**

- 支持广播通信，主题无需知道具体有多少个观察者
- 可以随时添加和删除观察者
- 符合开闭原则

**缺点:**

- 可能导致意外的更新，因为观察者不知道其他观察者的存在
- 如果观察者和主题之间有循环依赖，可能导致无限循环
- 观察者可能收到不相关的通知

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Observer a where
  update :: a -> String -> IO ()
  getId :: a -> String

class Subject a where
  attach :: a -> Observer -> IO ()
  detach :: a -> Observer -> IO ()
  notify :: a -> String -> IO ()
  getState :: a -> String
  setState :: a -> String -> IO ()
```

### 2.2 扩展接口

```haskell
-- 支持过滤的观察者接口
class (Observer a) => FilteredObserver a where
  shouldUpdate :: a -> String -> Bool
  getFilter :: a -> String
  
-- 支持优先级的观察者接口
class (Observer a) => PriorityObserver a where
  getPriority :: a -> Int
  setPriority :: a -> Int -> a
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Data.IORef
import Control.Monad
import Data.List (delete)

-- 观察者接口
class Observer a where
  update :: a -> String -> IO ()
  getId :: a -> String

-- 主题接口
class Subject a where
  attach :: a -> Observer -> IO ()
  detach :: a -> Observer -> IO ()
  notify :: a -> String -> IO ()
  getState :: a -> String
  setState :: a -> String -> IO ()

-- 具体主题
data ConcreteSubject = ConcreteSubject {
  state :: IORef String,
  observers :: IORef [Observer]
} deriving Show

newSubject :: IO ConcreteSubject
newSubject = do
  stateRef <- newIORef "初始状态"
  observersRef <- newIORef []
  return $ ConcreteSubject stateRef observersRef

instance Subject ConcreteSubject where
  attach subject observer = do
    observers <- readIORef (observers subject)
    writeIORef (observers subject) (observer : observers)
  
  detach subject observer = do
    observers <- readIORef (observers subject)
    let observerId = getId observer
        filteredObservers = filter (\obs -> getId obs /= observerId) observers
    writeIORef (observers subject) filteredObservers
  
  notify subject message = do
    observers <- readIORef (observers subject)
    mapM_ (\obs -> update obs message) observers
  
  getState subject = do
    readIORef (state subject)
  
  setState subject newState = do
    writeIORef (state subject) newState
    notify subject newState

-- 具体观察者
data ConcreteObserverA = ConcreteObserverA {
  name :: String,
  lastMessage :: IORef String
} deriving Show

newObserverA :: String -> IO ConcreteObserverA
newObserverA name = do
  lastMessageRef <- newIORef ""
  return $ ConcreteObserverA name lastMessageRef

instance Observer ConcreteObserverA where
  update observer message = do
    putStrLn $ "观察者A " ++ name observer ++ " 收到通知: " ++ message
    writeIORef (lastMessage observer) message
  
  getId observer = "ObserverA_" ++ name observer

data ConcreteObserverB = ConcreteObserverB {
  name :: String,
  messageCount :: IORef Int
} deriving Show

newObserverB :: String -> IO ConcreteObserverB
newObserverB name = do
  countRef <- newIORef 0
  return $ ConcreteObserverB name countRef

instance Observer ConcreteObserverB where
  update observer message = do
    count <- readIORef (messageCount observer)
    writeIORef (messageCount observer) (count + 1)
    putStrLn $ "观察者B " ++ name observer ++ " 收到通知: " ++ message ++ " (第" ++ show (count + 1) ++ "次)"

  getId observer = "ObserverB_" ++ name observer

-- 过滤观察者
data FilteredObserver = FilteredObserver {
  observer :: ConcreteObserverA,
  filter :: String
} deriving Show

newFilteredObserver :: String -> String -> IO FilteredObserver
newFilteredObserver name filter = do
  obs <- newObserverA name
  return $ FilteredObserver obs filter

instance Observer FilteredObserver where
  update observer message = 
    if filter observer `isInfixOf` message
    then update (observer observer) message
    else putStrLn $ "观察者 " ++ name (observer observer) ++ " 过滤了消息: " ++ message
  
  getId observer = "Filtered_" ++ getId (observer observer)

-- 优先级观察者
data PriorityObserver = PriorityObserver {
  observer :: ConcreteObserverA,
  priority :: Int
} deriving Show

newPriorityObserver :: String -> Int -> IO PriorityObserver
newPriorityObserver name priority = do
  obs <- newObserverA name
  return $ PriorityObserver obs priority

instance Observer PriorityObserver where
  update observer message = do
    putStrLn $ "优先级" ++ show (priority observer) ++ " 观察者 " ++ name (observer observer) ++ " 收到通知: " ++ message
    update (observer observer) message
  
  getId observer = "Priority_" ++ getId (observer observer)

-- 使用示例
main :: IO ()
main = do
  subject <- newSubject
  
  observerA1 <- newObserverA "观察者A1"
  observerA2 <- newObserverA "观察者A2"
  observerB <- newObserverB "观察者B"
  filteredObserver <- newFilteredObserver "过滤观察者" "重要"
  priorityObserver <- newPriorityObserver "优先级观察者" 1
  
  putStrLn "观察者模式示例:"
  
  -- 注册观察者
  attach subject observerA1
  attach subject observerA2
  attach subject observerB
  attach subject filteredObserver
  attach subject priorityObserver
  
  -- 改变状态
  putStrLn "\n第一次状态改变:"
  setState subject "状态1"
  
  -- 注销一个观察者
  putStrLn "\n注销观察者A1后:"
  detach subject observerA1
  setState subject "状态2"
  
  -- 发送过滤消息
  putStrLn "\n发送过滤消息:"
  setState subject "重要消息"
  setState subject "普通消息"
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::any::Any;

// 观察者trait
trait Observer: Send + Sync {
    fn update(&self, message: &str);
    fn get_id(&self) -> String;
}

// 主题trait
trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer: Arc<dyn Observer>);
    fn notify(&self, message: &str);
    fn get_state(&self) -> String;
    fn set_state(&mut self, state: &str);
}

// 具体主题
#[derive(Debug)]
struct ConcreteSubject {
    state: Arc<Mutex<String>>,
    observers: Arc<Mutex<Vec<Arc<dyn Observer>>>>,
}

impl ConcreteSubject {
    fn new() -> Self {
        ConcreteSubject {
            state: Arc::new(Mutex::new("初始状态".to_string())),
            observers: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        if let Ok(mut observers) = self.observers.lock() {
            observers.push(observer);
        }
    }
    
    fn detach(&mut self, observer: Arc<dyn Observer>) {
        if let Ok(mut observers) = self.observers.lock() {
            let observer_id = observer.get_id();
            observers.retain(|obs| obs.get_id() != observer_id);
        }
    }
    
    fn notify(&self, message: &str) {
        if let Ok(observers) = self.observers.lock() {
            for observer in observers.iter() {
                observer.update(message);
            }
        }
    }
    
    fn get_state(&self) -> String {
        if let Ok(state) = self.state.lock() {
            state.clone()
        } else {
            "未知状态".to_string()
        }
    }
    
    fn set_state(&mut self, state: &str) {
        if let Ok(mut state_ref) = self.state.lock() {
            *state_ref = state.to_string();
        }
        println!("主题状态改变为: {}", state);
        self.notify(state);
    }
}

// 具体观察者A
#[derive(Debug)]
struct ConcreteObserverA {
    name: String,
    last_message: Arc<Mutex<String>>,
}

impl ConcreteObserverA {
    fn new(name: String) -> Self {
        ConcreteObserverA {
            name,
            last_message: Arc::new(Mutex::new("".to_string())),
        }
    }
}

impl Observer for ConcreteObserverA {
    fn update(&self, message: &str) {
        println!("观察者A {} 收到通知: {}", self.name, message);
        if let Ok(mut last_message) = self.last_message.lock() {
            *last_message = message.to_string();
        }
    }
    
    fn get_id(&self) -> String {
        format!("ObserverA_{}", self.name)
    }
}

// 具体观察者B
#[derive(Debug)]
struct ConcreteObserverB {
    name: String,
    message_count: Arc<Mutex<i32>>,
}

impl ConcreteObserverB {
    fn new(name: String) -> Self {
        ConcreteObserverB {
            name,
            message_count: Arc::new(Mutex::new(0)),
        }
    }
}

impl Observer for ConcreteObserverB {
    fn update(&self, message: &str) {
        if let Ok(mut count) = self.message_count.lock() {
            *count += 1;
            println!("观察者B {} 收到通知: {} (第{}次)", self.name, message, *count);
        }
    }
    
    fn get_id(&self) -> String {
        format!("ObserverB_{}", self.name)
    }
}

// 过滤观察者
#[derive(Debug)]
struct FilteredObserver {
    observer: Arc<ConcreteObserverA>,
    filter: String,
}

impl FilteredObserver {
    fn new(observer: Arc<ConcreteObserverA>, filter: String) -> Self {
        FilteredObserver { observer, filter }
    }
}

impl Observer for FilteredObserver {
    fn update(&self, message: &str) {
        if message.contains(&self.filter) {
            self.observer.update(message);
        } else {
            println!("观察者 {} 过滤了消息: {}", self.observer.name, message);
        }
    }
    
    fn get_id(&self) -> String {
        format!("Filtered_{}", self.observer.get_id())
    }
}

// 优先级观察者
#[derive(Debug)]
struct PriorityObserver {
    observer: Arc<ConcreteObserverA>,
    priority: i32,
}

impl PriorityObserver {
    fn new(observer: Arc<ConcreteObserverA>, priority: i32) -> Self {
        PriorityObserver { observer, priority }
    }
}

impl Observer for PriorityObserver {
    fn update(&self, message: &str) {
        println!("优先级{} 观察者 {} 收到通知: {}", self.priority, self.observer.name, message);
        self.observer.update(message);
    }
    
    fn get_id(&self) -> String {
        format!("Priority_{}", self.observer.get_id())
    }
}

// 使用示例
fn main() {
    let mut subject = ConcreteSubject::new();
    
    let observer_a1 = Arc::new(ConcreteObserverA::new("观察者A1".to_string()));
    let observer_a2 = Arc::new(ConcreteObserverA::new("观察者A2".to_string()));
    let observer_b = Arc::new(ConcreteObserverB::new("观察者B".to_string()));
    
    let filtered_observer = Arc::new(FilteredObserver::new(
        Arc::new(ConcreteObserverA::new("过滤观察者".to_string())),
        "重要".to_string(),
    ));
    
    let priority_observer = Arc::new(PriorityObserver::new(
        Arc::new(ConcreteObserverA::new("优先级观察者".to_string())),
        1,
    ));
    
    println!("观察者模式示例:");
    
    // 注册观察者
    subject.attach(observer_a1.clone());
    subject.attach(observer_a2.clone());
    subject.attach(observer_b.clone());
    subject.attach(filtered_observer.clone());
    subject.attach(priority_observer.clone());
    
    // 改变状态
    println!("\n第一次状态改变:");
    subject.set_state("状态1");
    
    // 注销一个观察者
    println!("\n注销观察者A1后:");
    subject.detach(observer_a1.clone());
    subject.set_state("状态2");
    
    // 发送过滤消息
    println!("\n发送过滤消息:");
    subject.set_state("重要消息");
    subject.set_state("普通消息");
}
```

### 3.3 Lean实现

```lean
-- 观察者类型
inductive Observer where
  | ConcreteObserverA : String → Observer
  | ConcreteObserverB : String → Observer
  | FilteredObserver : Observer → String → Observer
  | PriorityObserver : Observer → Nat → Observer

-- 主题类型
structure Subject where
  state : String
  observers : List Observer

-- 更新函数
def update : Observer → String → IO Unit
  | Observer.ConcreteObserverA name, message => 
    IO.println s!"观察者A {name} 收到通知: {message}"
  | Observer.ConcreteObserverB name, message => 
    IO.println s!"观察者B {name} 收到通知: {message}"
  | Observer.FilteredObserver observer filter, message => 
    if filter ∈ message then update observer message
    else IO.println s!"观察者过滤了消息: {message}"
  | Observer.PriorityObserver observer priority, message => 
    IO.println s!"优先级{priority} 观察者收到通知: {message}" >>
    update observer message

-- 获取观察者ID
def getObserverId : Observer → String
  | Observer.ConcreteObserverA name => s!"ObserverA_{name}"
  | Observer.ConcreteObserverB name => s!"ObserverB_{name}"
  | Observer.FilteredObserver observer _ => s!"Filtered_{getObserverId observer}"
  | Observer.PriorityObserver observer _ => s!"Priority_{getObserverId observer}"

-- 通知所有观察者
def notify : Subject → String → IO Unit
  | subject, message => subject.observers.forM (λ obs => update obs message)

-- 添加观察者
def attach : Subject → Observer → Subject
  | subject, observer => { subject with observers := observer :: subject.observers }

-- 移除观察者
def detach : Subject → String → Subject
  | subject, observerId => 
    { subject with observers := subject.observers.filter (λ obs => getObserverId obs ≠ observerId) }

-- 设置状态
def setState : Subject → String → IO Subject
  | subject, newState => do
    IO.println s!"主题状态改变为: {newState}"
    notify subject newState
    return { subject with state := newState }

-- 使用示例
def main : IO Unit := do
  let observerA1 := Observer.ConcreteObserverA "观察者A1"
  let observerA2 := Observer.ConcreteObserverA "观察者A2"
  let observerB := Observer.ConcreteObserverB "观察者B"
  let filteredObserver := Observer.FilteredObserver observerA1 "重要"
  let priorityObserver := Observer.PriorityObserver observerA2 1
  
  let subject := Subject.mk "初始状态" []
  let subject1 := attach subject observerA1
  let subject2 := attach subject1 observerA2
  let subject3 := attach subject2 observerB
  let subject4 := attach subject3 filteredObserver
  let subject5 := attach subject4 priorityObserver
  
  IO.println "观察者模式示例:"
  
  -- 第一次状态改变
  IO.println "\n第一次状态改变:"
  subject6 ← setState subject5 "状态1"
  
  -- 注销观察者
  IO.println "\n注销观察者A1后:"
  let subject7 := detach subject6 "ObserverA_观察者A1"
  setState subject7 "状态2"
  
  -- 发送过滤消息
  IO.println "\n发送过滤消息:"
  subject8 ← setState subject7 "重要消息"
  setState subject8 "普通消息"
```

## 4. 工程实践

### 4.1 设计考虑

- **内存管理**: 避免循环引用导致的内存泄漏
- **线程安全**: 在多线程环境中安全地管理观察者
- **性能优化**: 避免不必要的通知
- **错误处理**: 处理观察者更新时的异常

### 4.2 实现模式

```haskell
-- 线程安全的主题
data ThreadSafeSubject = ThreadSafeSubject {
  state :: MVar String,
  observers :: MVar [Observer]
}

-- 异步通知
data AsyncSubject = AsyncSubject {
  subject :: Subject,
  executor :: ThreadPool
}

-- 带缓存的观察者
data CachedObserver = CachedObserver {
  observer :: Observer,
  cache :: MVar (Map String String)
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data ObserverError = 
  ObserverUpdateFailed String
  | CircularReference String
  | ObserverNotFound String

-- 安全通知
safeNotify :: Subject -> String -> IO (Either ObserverError ())
safeNotify subject message = 
  try (notify subject message) >>= \case
    Left e -> return $ Left $ ObserverUpdateFailed (show e)
    Right _ -> return $ Right ()
```

## 5. 性能优化

### 5.1 缓存策略

- **观察者缓存**: 缓存观察者的更新结果
- **状态缓存**: 缓存主题的状态变化
- **通知缓存**: 缓存通知消息

### 5.2 异步通知

```haskell
-- 异步通知器
data AsyncNotifier = AsyncNotifier {
  threadPool :: ThreadPool,
  queue :: MVar [Notification]
}

asyncNotify :: AsyncNotifier -> Observer -> String -> IO ThreadId
asyncNotify notifier observer message = 
  forkIO $ do
    update observer message
    return ()
```

### 5.3 批量通知

```haskell
-- 批量通知器
data BatchNotifier = BatchNotifier {
  observers :: [Observer],
  batchSize :: Int
}

notifyBatch :: BatchNotifier -> String -> IO ()
notifyBatch notifier message = 
  forM_ (chunksOf (batchSize notifier) (observers notifier)) $ \batch ->
    mapConcurrently (\obs -> update obs message) batch
```

## 6. 应用场景

### 6.1 事件处理系统

```haskell
-- 事件系统
data EventSystem = EventSystem {
  subjects :: Map String Subject,
  eventTypes :: [String]
}

handleEvent :: EventSystem -> String -> String -> IO ()
handleEvent system eventType message = 
  case Map.lookup eventType (subjects system) of
    Just subject -> notify subject message
    Nothing -> putStrLn $ "未知事件类型: " ++ eventType
```

### 6.2 数据绑定

```haskell
-- 数据绑定系统
data DataBinding = DataBinding {
  dataSource :: IORef String,
  observers :: [Observer]
}

updateData :: DataBinding -> String -> IO ()
updateData binding newData = do
  writeIORef (dataSource binding) newData
  mapM_ (\obs -> update obs newData) (observers binding)
```

### 6.3 日志系统

```haskell
-- 日志系统
data LogSystem = LogSystem {
  logLevel :: LogLevel,
  observers :: [Observer]
}

logMessage :: LogSystem -> LogLevel -> String -> IO ()
logMessage system level message = 
  if level >= logLevel system
  then mapM_ (\obs -> update obs message) (observers system)
  else return ()
```

### 6.4 配置管理

```haskell
-- 配置管理器
data ConfigManager = ConfigManager {
  config :: IORef (Map String String),
  observers :: [Observer]
}

updateConfig :: ConfigManager -> String -> String -> IO ()
updateConfig manager key value = do
  config' <- readIORef (config manager)
  writeIORef (config manager) (Map.insert key value config')
  mapM_ (\obs -> update obs (key ++ "=" ++ value)) (observers manager)
```

## 7. 最佳实践

### 7.1 设计原则

- **避免循环引用**: 确保观察者和主题之间没有循环依赖
- **最小化通知**: 只在状态真正改变时通知观察者
- **错误隔离**: 一个观察者的错误不应影响其他观察者
- **线程安全**: 在多线程环境中安全地管理观察者

### 7.2 实现建议

```haskell
-- 观察者工厂
class ObserverFactory a where
  createObserver :: String -> Maybe a
  listObserverTypes :: [String]
  validateObserver :: a -> Bool

-- 观察者注册表
data ObserverRegistry = ObserverRegistry {
  observers :: Map String (forall a. Observer a => a),
  metadata :: Map String String
}

-- 线程安全观察者管理器
data ThreadSafeObserverManager = ThreadSafeObserverManager {
  manager :: MVar ObserverManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 观察者测试
testObserver :: Observer a => a -> String -> Bool
testObserver observer message = 
  let result = update observer message
  in isRight result

-- 性能测试
benchmarkObserver :: Observer a => a -> String -> IO Double
benchmarkObserver observer message = do
  start <- getCurrentTime
  replicateM_ 1000 $ update observer message
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的观察者类型
- **序列化**: 支持观察者的序列化和反序列化
- **版本控制**: 支持观察者的版本管理
- **分布式**: 支持跨网络的观察者通信

## 8. 总结

观察者模式是实现松耦合对象间通信的强大工具，通过发布-订阅机制提供了灵活的事件处理能力。在实现时需要注意内存管理、线程安全和性能优化。该模式在事件处理、数据绑定、日志系统、配置管理等场景中都有广泛应用。
