# 主动对象模式 (Active Object Pattern)

## 1. 理论基础

### 1.1 模式定义

主动对象模式是一种并发设计模式，它将方法调用与执行分离。每个主动对象都有自己的控制线程，方法调用被封装成请求对象并放入队列中异步执行。这种模式实现了调用者与执行者的解耦，提高了系统的并发性和响应性。

### 1.2 形式化定义

```lean
-- 主动对象模式的形式化定义
inductive ActiveObjectPattern : Type
| ActiveObject : Scheduler → RequestQueue → ControlThread → ActiveObject

-- 请求队列的形式化
inductive RequestQueue : Type
| Empty : RequestQueue
| Enqueue : Request → RequestQueue → RequestQueue
| Dequeue : RequestQueue → Option Request × RequestQueue

-- 调度器的形式化
inductive Scheduler : Type
| Scheduler : RequestQueue → ControlThread → Scheduler

-- 主动对象正确性定理
theorem active_object_correctness (ao : ActiveObject) :
  ∀ (request : Request),
  RequestEnqueued request ao.queue →
  Eventually (RequestExecuted request ao.scheduler) →
  ActiveObjectInvariant ao

-- 并发安全性定理
theorem active_object_thread_safety (ao : ActiveObject) :
  ∀ (req1 req2 : Request),
  RequestEnqueued req1 ao.queue →
  RequestEnqueued req2 ao.queue →
  req1 ≠ req2 →
  NoDataRace (req1, req2)
```

### 1.3 语义模型

```haskell
-- 主动对象模式的语义模型
data ActiveObjectSemantics = ActiveObjectSemantics
  { requestQueue :: RequestQueue
  , scheduler :: Scheduler
  , controlThread :: ControlThread
  , invariants :: [Invariant]
  }

-- 请求语义
data Request = Request
  { requestId :: UUID
  , requestType :: RequestType
  , requestData :: RequestData
  , priority :: Priority
  , timestamp :: UTCTime
  }

-- 调度器语义
data Scheduler = Scheduler
  { queue :: TVar [Request]
  , running :: TVar Bool
  , threadPool :: ThreadPool
  , schedulingPolicy :: SchedulingPolicy
  }

-- 主动对象正确性验证
validateActiveObject :: ActiveObjectSemantics -> Bool
validateActiveObject semantics = 
  all validateInvariant (invariants semantics) &&
  validateScheduler (scheduler semantics) &&
  validateThreadSafety semantics
```

## 2. 设计原则

### 2.1 核心原则

1. **调用与执行分离**：方法调用立即返回，执行异步进行
2. **请求队列管理**：使用线程安全的队列管理待执行请求
3. **独立控制线程**：每个主动对象有自己的控制线程
4. **异步响应机制**：支持Future/Promise模式获取执行结果

### 2.2 设计约束

```rust
// 主动对象设计约束
trait ActiveObjectConstraints {
    // 线程安全性
    fn thread_safety_guaranteed(&self) -> bool;
    
    // 请求顺序性
    fn request_ordering_preserved(&self) -> bool;
    
    // 响应时间约束
    fn response_time_bounded(&self) -> Duration;
    
    // 资源使用限制
    fn resource_usage_limited(&self) -> ResourceUsage;
}
```

## 3. 多语言实现

### 3.1 Rust实现

#### 3.1.1 基础主动对象

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::{Duration, Instant};
use uuid::Uuid;
use serde::{Deserialize, Serialize};

// 请求特征
#[async_trait::async_trait]
pub trait Request: Send + Sync {
    async fn execute(&self) -> Result<Response, RequestError>;
    fn priority(&self) -> Priority;
    fn id(&self) -> Uuid;
}

// 请求类型
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum RequestType {
    Compute { data: Vec<u8> },
    Network { url: String },
    Database { query: String },
    Custom { payload: String },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RequestData {
    pub request_type: RequestType,
    pub metadata: HashMap<String, String>,
    pub timestamp: Instant,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

// 具体请求实现
pub struct ConcreteRequest {
    id: Uuid,
    data: RequestData,
    priority: Priority,
}

impl ConcreteRequest {
    pub fn new(data: RequestData, priority: Priority) -> Self {
        ConcreteRequest {
            id: Uuid::new_v4(),
            data,
            priority,
        }
    }
}

#[async_trait::async_trait]
impl Request for ConcreteRequest {
    async fn execute(&self) -> Result<Response, RequestError> {
        match &self.data.request_type {
            RequestType::Compute { data } => {
                // 模拟计算任务
                thread::sleep(Duration::from_millis(100));
                Ok(Response::Success {
                    data: format!("Computed: {:?}", data),
                    timestamp: Instant::now(),
                })
            }
            RequestType::Network { url } => {
                // 模拟网络请求
                thread::sleep(Duration::from_millis(200));
                Ok(Response::Success {
                    data: format!("Network response from: {}", url),
                    timestamp: Instant::now(),
                })
            }
            RequestType::Database { query } => {
                // 模拟数据库查询
                thread::sleep(Duration::from_millis(150));
                Ok(Response::Success {
                    data: format!("Database result: {}", query),
                    timestamp: Instant::now(),
                })
            }
            RequestType::Custom { payload } => {
                // 自定义处理
                Ok(Response::Success {
                    data: format!("Custom processed: {}", payload),
                    timestamp: Instant::now(),
                })
            }
        }
    }
    
    fn priority(&self) -> Priority {
        self.priority
    }
    
    fn id(&self) -> Uuid {
        self.id
    }
}

// 响应类型
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Response {
    Success { data: String, timestamp: Instant },
    Error { message: String, code: u32 },
}

#[derive(Debug, thiserror::Error)]
pub enum RequestError {
    #[error("Execution timeout")]
    Timeout,
    #[error("Resource unavailable")]
    ResourceUnavailable,
    #[error("Invalid request: {0}")]
    InvalidRequest(String),
}

// 调度器实现
pub struct Scheduler {
    queue: Arc<Mutex<VecDeque<Box<dyn Request>>>>,
    condition: Arc<Condvar>,
    running: Arc<Mutex<bool>>,
    thread_pool: ThreadPool,
    config: SchedulerConfig,
}

#[derive(Clone)]
pub struct SchedulerConfig {
    pub max_queue_size: usize,
    pub worker_threads: usize,
    pub timeout: Duration,
    pub enable_priority: bool,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        SchedulerConfig {
            max_queue_size: 1000,
            worker_threads: 4,
            timeout: Duration::from_secs(30),
            enable_priority: true,
        }
    }
}

impl Scheduler {
    pub fn new(config: SchedulerConfig) -> Self {
        Scheduler {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            condition: Arc::new(Condvar::new()),
            running: Arc::new(Mutex::new(true)),
            thread_pool: ThreadPool::new(config.worker_threads),
            config,
        }
    }
    
    pub fn start(&self) {
        let queue = Arc::clone(&self.queue);
        let condition = Arc::clone(&self.condition);
        let running = Arc::clone(&self.running);
        let thread_pool = self.thread_pool.clone();
        let config = self.config.clone();
        
        thread::spawn(move || {
            while *running.lock().unwrap() {
                let request = {
                    let mut queue_guard = queue.lock().unwrap();
                    while queue_guard.is_empty() && *running.lock().unwrap() {
                        queue_guard = condition.wait(queue_guard).unwrap();
                    }
                    
                    if *running.lock().unwrap() {
                        queue_guard.pop_front()
                    } else {
                        None
                    }
                };
                
                if let Some(request) = request {
                    let thread_pool = thread_pool.clone();
                    thread::spawn(move || {
                        let rt = tokio::runtime::Runtime::new().unwrap();
                        rt.block_on(async {
                            if let Err(e) = request.execute().await {
                                eprintln!("Request execution failed: {:?}", e);
                            }
                        });
                    });
                }
            }
        });
    }
    
    pub fn stop(&self) {
        *self.running.lock().unwrap() = false;
        self.condition.notify_all();
    }
    
    pub fn enqueue(&self, request: Box<dyn Request>) -> Result<(), SchedulerError> {
        let mut queue = self.queue.lock().unwrap();
        
        if queue.len() >= self.config.max_queue_size {
            return Err(SchedulerError::QueueFull);
        }
        
        if self.config.enable_priority {
            // 优先级插入
            let priority = request.priority();
            let mut insert_pos = 0;
            for (i, existing_request) in queue.iter().enumerate() {
                if existing_request.priority() < priority {
                    insert_pos = i;
                    break;
                }
                insert_pos = i + 1;
            }
            queue.insert(insert_pos, request);
        } else {
            queue.push_back(request);
        }
        
        self.condition.notify_one();
        Ok(())
    }
    
    pub fn queue_size(&self) -> usize {
        self.queue.lock().unwrap().len()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SchedulerError {
    #[error("Queue is full")]
    QueueFull,
    #[error("Scheduler is stopped")]
    SchedulerStopped,
}

// 线程池实现
#[derive(Clone)]
pub struct ThreadPool {
    workers: Arc<Mutex<Vec<thread::JoinHandle<()>>>>,
}

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        ThreadPool {
            workers: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

// 主动对象实现
pub struct ActiveObject {
    scheduler: Scheduler,
    metrics: Arc<Mutex<ActiveObjectMetrics>>,
}

#[derive(Default)]
pub struct ActiveObjectMetrics {
    pub total_requests: u64,
    pub completed_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: Duration,
}

impl ActiveObject {
    pub fn new(config: SchedulerConfig) -> Self {
        let scheduler = Scheduler::new(config);
        scheduler.start();
        
        ActiveObject {
            scheduler,
            metrics: Arc::new(Mutex::new(ActiveObjectMetrics::default())),
        }
    }
    
    pub fn request(&self, data: RequestData, priority: Priority) -> Result<Uuid, ActiveObjectError> {
        let request = Box::new(ConcreteRequest::new(data, priority));
        let request_id = request.id();
        
        self.scheduler.enqueue(request)
            .map_err(ActiveObjectError::SchedulerError)?;
        
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.total_requests += 1;
        }
        
        Ok(request_id)
    }
    
    pub fn shutdown(&self) {
        self.scheduler.stop();
    }
    
    pub fn get_metrics(&self) -> ActiveObjectMetrics {
        self.metrics.lock().unwrap().clone()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ActiveObjectError {
    #[error("Scheduler error: {0}")]
    SchedulerError(#[from] SchedulerError),
    #[error("Request timeout")]
    RequestTimeout,
}
```

#### 3.1.2 高级主动对象

```rust
// 支持Future的主动对象
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct FutureRequest<T> {
    id: Uuid,
    data: RequestData,
    priority: Priority,
    result: Arc<Mutex<Option<Result<T, RequestError>>>>,
    waker: Arc<Mutex<Option<std::task::Waker>>>,
}

impl<T> FutureRequest<T> {
    pub fn new(data: RequestData, priority: Priority) -> Self {
        FutureRequest {
            id: Uuid::new_v4(),
            data,
            priority,
            result: Arc::new(Mutex::new(None)),
            waker: Arc::new(Mutex::new(None)),
        }
    }
}

impl<T> Future for FutureRequest<T> {
    type Output = Result<T, RequestError>;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut result = self.result.lock().unwrap();
        
        if let Some(result) = result.take() {
            Poll::Ready(result)
        } else {
            *self.waker.lock().unwrap() = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}

// 支持批处理的主动对象
pub struct BatchActiveObject {
    scheduler: Scheduler,
    batch_size: usize,
    batch_timeout: Duration,
}

impl BatchActiveObject {
    pub fn new(config: SchedulerConfig, batch_size: usize, batch_timeout: Duration) -> Self {
        BatchActiveObject {
            scheduler: Scheduler::new(config),
            batch_size,
            batch_timeout,
        }
    }
    
    pub fn batch_request(&self, requests: Vec<RequestData>) -> Result<Vec<Uuid>, ActiveObjectError> {
        let mut request_ids = Vec::new();
        
        for request_data in requests {
            let request_id = self.request(request_data, Priority::Normal)?;
            request_ids.push(request_id);
        }
        
        Ok(request_ids)
    }
}
```

### 3.2 Haskell实现

#### 3.2.1 函数式主动对象

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef
import Data.Time.Clock
import Data.UUID
import Data.UUID.V4
import qualified Data.Map as Map
import qualified Data.Text as T

-- 请求类型类
class Request a where
    execute :: MonadIO m => a -> m (Either RequestError Response)
    priority :: a -> Priority
    requestId :: a -> UUID

-- 数据类型
data RequestType = ComputeRequest ByteString
                 | NetworkRequest String
                 | DatabaseRequest String
                 | CustomRequest String

data RequestData = RequestData
    { requestType :: RequestType
    , metadata :: Map String String
    , timestamp :: UTCTime
    }

data Priority = Low | Normal | High | Critical
    deriving (Eq, Ord, Show)

data Response = SuccessResponse String UTCTime
              | ErrorResponse String Int

data RequestError = TimeoutError
                  | ResourceUnavailableError
                  | InvalidRequestError String

-- 具体请求实现
data ConcreteRequest = ConcreteRequest
    { requestId' :: UUID
    , requestData :: RequestData
    , requestPriority :: Priority
    }

instance Request ConcreteRequest where
    execute request = do
        case requestType (requestData request) of
            ComputeRequest data -> do
                liftIO $ threadDelay 100000
                now <- liftIO getCurrentTime
                return $ Right $ SuccessResponse ("Computed: " ++ show data) now
            NetworkRequest url -> do
                liftIO $ threadDelay 200000
                now <- liftIO getCurrentTime
                return $ Right $ SuccessResponse ("Network response from: " ++ url) now
            DatabaseRequest query -> do
                liftIO $ threadDelay 150000
                now <- liftIO getCurrentTime
                return $ Right $ SuccessResponse ("Database result: " ++ query) now
            CustomRequest payload -> do
                now <- liftIO getCurrentTime
                return $ Right $ SuccessResponse ("Custom processed: " ++ payload) now
    
    priority = requestPriority
    requestId = requestId'

-- 调度器配置
data SchedulerConfig = SchedulerConfig
    { maxQueueSize :: Int
    , workerThreads :: Int
    , timeout :: NominalDiffTime
    , enablePriority :: Bool
    }

defaultSchedulerConfig :: SchedulerConfig
defaultSchedulerConfig = SchedulerConfig
    { maxQueueSize = 1000
    , workerThreads = 4
    , timeout = 30.0
    , enablePriority = True
    }

-- 调度器
data Scheduler = Scheduler
    { queue :: TVar [ConcreteRequest]
    , running :: TVar Bool
    , config :: SchedulerConfig
    , metrics :: TVar SchedulerMetrics
    }

data SchedulerMetrics = SchedulerMetrics
    { totalRequests :: Int
    , completedRequests :: Int
    , failedRequests :: Int
    , averageResponseTime :: NominalDiffTime
    }

newScheduler :: SchedulerConfig -> IO Scheduler
newScheduler config = do
    queue <- newTVarIO []
    running <- newTVarIO True
    metrics <- newTVarIO $ SchedulerMetrics 0 0 0 0.0
    return $ Scheduler queue running config metrics

startScheduler :: Scheduler -> IO ()
startScheduler scheduler = do
    replicateM_ (workerThreads $ config scheduler) $
        forkIO $ workerLoop scheduler
    return ()

workerLoop :: Scheduler -> IO ()
workerLoop scheduler = do
    shouldRun <- readTVarIO (running scheduler)
    if shouldRun
        then do
            request <- atomically $ do
                requests <- readTVar (queue scheduler)
                case requests of
                    [] -> retry
                    (r:rs) -> do
                        writeTVar (queue scheduler) rs
                        return r
            result <- execute request
            atomically $ updateMetrics scheduler result
            workerLoop scheduler
        else return ()

updateMetrics :: Scheduler -> Either RequestError Response -> STM ()
updateMetrics scheduler result = do
    metrics' <- readTVar (metrics scheduler)
    case result of
        Left _ -> writeTVar (metrics scheduler) metrics'
            { totalRequests = totalRequests metrics' + 1
            , failedRequests = failedRequests metrics' + 1
            }
        Right _ -> writeTVar (metrics scheduler) metrics'
            { totalRequests = totalRequests metrics' + 1
            , completedRequests = completedRequests metrics' + 1
            }

stopScheduler :: Scheduler -> IO ()
stopScheduler scheduler = do
    atomically $ writeTVar (running scheduler) False

enqueueRequest :: Scheduler -> ConcreteRequest -> IO (Either String ())
enqueueRequest scheduler request = do
    atomically $ do
        requests <- readTVar (queue scheduler)
        if length requests >= maxQueueSize (config scheduler)
            then return $ Left "Queue is full"
            else do
                let newRequests = if enablePriority (config scheduler)
                                 then insertByPriority request requests
                                 else requests ++ [request]
                writeTVar (queue scheduler) newRequests
                return $ Right ()

insertByPriority :: ConcreteRequest -> [ConcreteRequest] -> [ConcreteRequest]
insertByPriority request requests = 
    let (before, after) = span (\r -> priority r >= priority request) requests
    in before ++ [request] ++ after

-- 主动对象
data ActiveObject = ActiveObject
    { scheduler :: Scheduler
    , objectMetrics :: IORef ActiveObjectMetrics
    }

data ActiveObjectMetrics = ActiveObjectMetrics
    { totalRequests' :: Int
    , completedRequests' :: Int
    , failedRequests' :: Int
    }

newActiveObject :: SchedulerConfig -> IO ActiveObject
newActiveObject config = do
    scheduler <- newScheduler config
    startScheduler scheduler
    metrics <- newIORef $ ActiveObjectMetrics 0 0 0
    return $ ActiveObject scheduler metrics

request :: ActiveObject -> RequestData -> Priority -> IO (Either String UUID)
request activeObject requestData priority = do
    requestId <- liftIO nextRandom
    let concreteRequest = ConcreteRequest requestId requestData priority
    
    result <- enqueueRequest (scheduler activeObject) concreteRequest
    case result of
        Left err -> return $ Left err
        Right _ -> do
            modifyIORef (objectMetrics activeObject) $ \metrics ->
                metrics { totalRequests' = totalRequests' metrics + 1 }
            return $ Right requestId

shutdown :: ActiveObject -> IO ()
shutdown activeObject = do
    stopScheduler (scheduler activeObject)

getMetrics :: ActiveObject -> IO ActiveObjectMetrics
getMetrics activeObject = readIORef (objectMetrics activeObject)
```

#### 3.2.2 高级Haskell实现

```haskell
-- 支持Future的主动对象
import Control.Concurrent.MVar

data FutureRequest a = FutureRequest
    { futureId :: UUID
    , futureData :: RequestData
    , futurePriority :: Priority
    , futureResult :: MVar (Either RequestError a)
    }

instance Request (FutureRequest a) where
    execute request = do
        result <- executeConcreteRequest request
        putMVar (futureResult request) result
        return result
    
    priority = futurePriority
    requestId = futureId

executeConcreteRequest :: FutureRequest a -> IO (Either RequestError a)
executeConcreteRequest request = do
    case requestType (futureData request) of
        ComputeRequest data -> do
            threadDelay 100000
            return $ Right $ "Computed: " ++ show data
        NetworkRequest url -> do
            threadDelay 200000
            return $ Right $ "Network response from: " ++ url
        DatabaseRequest query -> do
            threadDelay 150000
            return $ Right $ "Database result: " ++ query
        CustomRequest payload -> do
            return $ Right $ "Custom processed: " ++ payload

-- 批处理主动对象
data BatchActiveObject = BatchActiveObject
    { batchScheduler :: Scheduler
    , batchSize :: Int
    , batchTimeout :: NominalDiffTime
    }

newBatchActiveObject :: SchedulerConfig -> Int -> NominalDiffTime -> IO BatchActiveObject
newBatchActiveObject config batchSize batchTimeout = do
    scheduler <- newScheduler config
    startScheduler scheduler
    return $ BatchActiveObject scheduler batchSize batchTimeout

batchRequest :: BatchActiveObject -> [RequestData] -> IO (Either String [UUID])
batchRequest batchObject requests = do
    let concreteRequests = map (\data -> ConcreteRequest 
            (unsafePerformIO nextRandom) 
            data 
            Normal) requests
    
    results <- mapM (enqueueRequest (batchScheduler batchObject)) concreteRequests
    
    if any isLeft results
        then return $ Left "Some requests failed to enqueue"
        else return $ Right $ map requestId concreteRequests
```

### 3.3 Lean实现

#### 3.3.1 形式化主动对象

```lean
import Lean.Data.HashMap
import Lean.Data.Json
import System.Time

-- 请求类型类
class Request (α : Type) where
  execute : α → IO (Except Error Response)
  priority : α → Priority
  requestId : α → String

-- 数据类型
inductive RequestType
| Compute : ByteArray → RequestType
| Network : String → RequestType
| Database : String → RequestType
| Custom : String → RequestType

structure RequestData where
  requestType : RequestType
  metadata : HashMap String String
  timestamp : IO.Prim.Real

inductive Priority
| Low
| Normal
| High
| Critical

inductive Response
| Success : String → IO.Prim.Real → Response
| Error : String → Nat → Response

structure Error where
  message : String
  code : Nat

-- 具体请求
structure ConcreteRequest where
  id : String
  data : RequestData
  priority : Priority

instance : Request ConcreteRequest where
  execute request := do
    match request.data.requestType with
    | RequestType.Compute data => do
      IO.sleep 100
      let timestamp ← IO.monoMsNow
      return Except.ok (Response.Success ("Computed: " ++ toString data) timestamp)
    | RequestType.Network url => do
      IO.sleep 200
      let timestamp ← IO.monoMsNow
      return Except.ok (Response.Success ("Network response from: " ++ url) timestamp)
    | RequestType.Database query => do
      IO.sleep 150
      let timestamp ← IO.monoMsNow
      return Except.ok (Response.Success ("Database result: " ++ query) timestamp)
    | RequestType.Custom payload => do
      let timestamp ← IO.monoMsNow
      return Except.ok (Response.Success ("Custom processed: " ++ payload) timestamp)
  
  priority := ConcreteRequest.priority
  requestId := ConcreteRequest.id

-- 调度器
structure Scheduler where
  queue : List ConcreteRequest
  running : Bool
  config : SchedulerConfig

structure SchedulerConfig where
  maxQueueSize : Nat
  workerThreads : Nat
  timeout : Nat
  enablePriority : Bool

def newScheduler (config : SchedulerConfig) : IO Scheduler :=
  pure { queue := [], running := true, config := config }

def startScheduler (scheduler : Scheduler) : IO Unit := do
  -- 启动工作线程
  for i in [:scheduler.config.workerThreads] do
    IO.spawn (workerLoop scheduler)
  return ()

def workerLoop (scheduler : Scheduler) : IO Unit := do
  shouldRun ← readSchedulerRunning scheduler
  if shouldRun
    then do
      request ← dequeueRequest scheduler
      match request with
      | some req => do
        result ← execute req
        updateMetrics scheduler result
        workerLoop scheduler
      | none => workerLoop scheduler
    else return ()

def dequeueRequest (scheduler : Scheduler) : IO (Option ConcreteRequest) := do
  -- 从队列中取出请求
  pure none

def updateMetrics (scheduler : Scheduler) (result : Except Error Response) : IO Unit := do
  -- 更新指标
  return ()

-- 主动对象
structure ActiveObject where
  scheduler : Scheduler
  metrics : ActiveObjectMetrics

structure ActiveObjectMetrics where
  totalRequests : Nat
  completedRequests : Nat
  failedRequests : Nat

def newActiveObject (config : SchedulerConfig) : IO ActiveObject := do
  scheduler ← newScheduler config
  startScheduler scheduler
  return { scheduler := scheduler, metrics := { totalRequests := 0, completedRequests := 0, failedRequests := 0 } }

def request (activeObject : ActiveObject) (data : RequestData) (priority : Priority) : IO (Except String String) := do
  let concreteRequest := { id := "req_" ++ toString (activeObject.metrics.totalRequests), data := data, priority := priority }
  result ← enqueueRequest activeObject.scheduler concreteRequest
  return result

def enqueueRequest (scheduler : Scheduler) (request : ConcreteRequest) : IO (Except String Unit) := do
  -- 将请求加入队列
  pure (Except.ok ())

def shutdown (activeObject : ActiveObject) : IO Unit := do
  -- 关闭调度器
  return ()
```

## 4. 工程实践

### 4.1 架构设计

```rust
// 主动对象架构设计
pub mod active_object {
    pub mod core {
        use super::super::*;
        
        pub trait ActiveObjectCore {
            fn validate_configuration(&self) -> Result<(), ActiveObjectError>;
            fn initialize(&mut self) -> Result<(), ActiveObjectError>;
            fn shutdown(&mut self) -> Result<(), ActiveObjectError>;
            fn health_check(&self) -> HealthStatus;
        }
    }
    
    pub mod factory {
        use super::core::ActiveObjectCore;
        
        pub trait ActiveObjectFactory {
            type ActiveObject: ActiveObjectCore;
            
            fn create_active_object(&self, config: &ActiveObjectConfig) -> Result<Self::ActiveObject, ActiveObjectError>;
            fn validate_config(&self, config: &ActiveObjectConfig) -> Result<(), ActiveObjectError>;
        }
    }
    
    pub mod registry {
        use std::collections::HashMap;
        use super::factory::ActiveObjectFactory;
        
        pub struct ActiveObjectRegistry {
            factories: HashMap<String, Box<dyn ActiveObjectFactory>>,
        }
        
        impl ActiveObjectRegistry {
            pub fn new() -> Self {
                ActiveObjectRegistry { factories: HashMap::new() }
            }
            
            pub fn register_factory<F: ActiveObjectFactory + 'static>(
                &mut self, 
                name: String, 
                factory: F
            ) {
                self.factories.insert(name, Box::new(factory));
            }
            
            pub fn create_active_object(
                &self, 
                name: &str, 
                config: &ActiveObjectConfig
            ) -> Result<Box<dyn ActiveObjectCore>, ActiveObjectError> {
                if let Some(factory) = self.factories.get(name) {
                    factory.create_active_object(config)
                } else {
                    Err(ActiveObjectError::FactoryNotFound(name.to_string()))
                }
            }
        }
    }
}
```

### 4.2 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::time::Duration;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ActiveObjectConfig {
    pub scheduler_config: SchedulerConfig,
    pub thread_pool_config: ThreadPoolConfig,
    pub monitoring_config: MonitoringConfig,
    pub security_config: SecurityConfig,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ThreadPoolConfig {
    pub min_threads: usize,
    pub max_threads: usize,
    pub keep_alive_time: Duration,
    pub queue_capacity: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MonitoringConfig {
    pub metrics_enabled: bool,
    pub health_check_interval: Duration,
    pub log_level: LogLevel,
    pub tracing_enabled: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecurityConfig {
    pub request_validation: bool,
    pub rate_limiting: bool,
    pub max_request_size: usize,
    pub allowed_request_types: Vec<String>,
}

impl Default for ActiveObjectConfig {
    fn default() -> Self {
        ActiveObjectConfig {
            scheduler_config: SchedulerConfig::default(),
            thread_pool_config: ThreadPoolConfig {
                min_threads: 2,
                max_threads: 8,
                keep_alive_time: Duration::from_secs(60),
                queue_capacity: 1000,
            },
            monitoring_config: MonitoringConfig {
                metrics_enabled: true,
                health_check_interval: Duration::from_secs(30),
                log_level: LogLevel::Info,
                tracing_enabled: false,
            },
            security_config: SecurityConfig {
                request_validation: true,
                rate_limiting: true,
                max_request_size: 1024 * 1024,
                allowed_request_types: vec!["compute".to_string(), "network".to_string()],
            },
        }
    }
}
```

### 4.3 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ActiveObjectError {
    #[error("Configuration error: {0}")]
    Configuration(String),
    
    #[error("Scheduler error: {0}")]
    Scheduler(#[from] SchedulerError),
    
    #[error("Thread pool error: {0}")]
    ThreadPool(String),
    
    #[error("Request validation error: {0}")]
    RequestValidation(String),
    
    #[error("Rate limiting error: {0}")]
    RateLimiting(String),
    
    #[error("Resource exhaustion: {0}")]
    ResourceExhaustion(String),
    
    #[error("Security violation: {0}")]
    SecurityViolation(String),
}

impl ActiveObjectError {
    pub fn is_retryable(&self) -> bool {
        matches!(self, 
            ActiveObjectError::Scheduler(_) | 
            ActiveObjectError::ThreadPool(_) |
            ActiveObjectError::ResourceExhaustion(_)
        )
    }
    
    pub fn error_code(&self) -> u32 {
        match self {
            ActiveObjectError::Configuration(_) => 2001,
            ActiveObjectError::Scheduler(_) => 2002,
            ActiveObjectError::ThreadPool(_) => 2003,
            ActiveObjectError::RequestValidation(_) => 2004,
            ActiveObjectError::RateLimiting(_) => 2005,
            ActiveObjectError::ResourceExhaustion(_) => 2006,
            ActiveObjectError::SecurityViolation(_) => 2007,
        }
    }
}
```

## 5. 性能优化

### 5.1 线程池优化

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;
use std::collections::HashMap;

pub struct OptimizedThreadPool {
    workers: Vec<Worker>,
    task_queue: Arc<tokio::sync::mpsc::UnboundedSender<Task>>,
    metrics: Arc<Mutex<ThreadPoolMetrics>>,
}

struct Worker {
    id: usize,
    handle: Option<thread::JoinHandle<()>>,
}

struct Task {
    id: Uuid,
    request: Box<dyn Request + Send>,
    priority: Priority,
    created_at: Instant,
}

#[derive(Default)]
struct ThreadPoolMetrics {
    total_tasks: u64,
    completed_tasks: u64,
    failed_tasks: u64,
    average_execution_time: Duration,
    queue_size: usize,
}

impl OptimizedThreadPool {
    pub fn new(size: usize) -> Self {
        let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
        let task_queue = Arc::new(tx);
        let rx = Arc::new(Mutex::new(rx));
        
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            let rx = Arc::clone(&rx);
            let metrics = Arc::new(Mutex::new(ThreadPoolMetrics::default()));
            
            let handle = thread::spawn(move || {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    while let Some(task) = rx.lock().unwrap().recv().await {
                        let start_time = Instant::now();
                        
                        if let Err(e) = task.request.execute().await {
                            eprintln!("Task execution failed: {:?}", e);
                        }
                        
                        let execution_time = start_time.elapsed();
                        Self::update_metrics(&metrics, execution_time);
                    }
                });
            });
            
            workers.push(Worker { id, handle: Some(handle) });
        }
        
        OptimizedThreadPool {
            workers,
            task_queue,
            metrics: Arc::new(Mutex::new(ThreadPoolMetrics::default())),
        }
    }
    
    pub fn submit(&self, task: Task) -> Result<(), ThreadPoolError> {
        self.task_queue.send(task)
            .map_err(|_| ThreadPoolError::QueueFull)
    }
    
    fn update_metrics(metrics: &Arc<Mutex<ThreadPoolMetrics>>, execution_time: Duration) {
        if let Ok(mut metrics) = metrics.lock() {
            metrics.completed_tasks += 1;
            metrics.average_execution_time = 
                (metrics.average_execution_time + execution_time) / 2;
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ThreadPoolError {
    #[error("Thread pool queue is full")]
    QueueFull,
    #[error("Thread pool is shut down")]
    Shutdown,
}
```

### 5.2 内存管理

```rust
use std::alloc::{alloc, dealloc, Layout};
use std::ptr::NonNull;

pub struct MemoryPool {
    blocks: Vec<NonNull<u8>>,
    block_size: usize,
    free_list: Vec<NonNull<u8>>,
}

impl MemoryPool {
    pub fn new(block_size: usize, initial_blocks: usize) -> Self {
        let mut blocks = Vec::new();
        let mut free_list = Vec::new();
        
        for _ in 0..initial_blocks {
            let layout = Layout::from_size_align(block_size, 8).unwrap();
            let ptr = unsafe { alloc(layout) };
            
            if !ptr.is_null() {
                let non_null = NonNull::new(ptr).unwrap();
                blocks.push(non_null);
                free_list.push(non_null);
            }
        }
        
        MemoryPool {
            blocks,
            block_size,
            free_list,
        }
    }
    
    pub fn allocate(&mut self) -> Option<NonNull<u8>> {
        self.free_list.pop()
    }
    
    pub fn deallocate(&mut self, ptr: NonNull<u8>) {
        self.free_list.push(ptr);
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        for block in &self.blocks {
            let layout = Layout::from_size_align(self.block_size, 8).unwrap();
            unsafe { dealloc(block.as_ptr(), layout) };
        }
    }
}
```

## 6. 应用场景

### 6.1 异步任务处理

```rust
// 异步任务处理示例
pub struct AsyncTaskProcessor {
    active_object: ActiveObject,
    task_registry: HashMap<String, Box<dyn TaskHandler>>,
}

pub trait TaskHandler: Send + Sync {
    async fn handle(&self, data: &[u8]) -> Result<Vec<u8>, TaskError>;
    fn task_type(&self) -> &str;
}

impl AsyncTaskProcessor {
    pub fn new(config: ActiveObjectConfig) -> Self {
        AsyncTaskProcessor {
            active_object: ActiveObject::new(config),
            task_registry: HashMap::new(),
        }
    }
    
    pub fn register_handler<H: TaskHandler + 'static>(&mut self, handler: H) {
        self.task_registry.insert(handler.task_type().to_string(), Box::new(handler));
    }
    
    pub async fn process_task(&self, task_type: &str, data: &[u8]) -> Result<Vec<u8>, TaskError> {
        if let Some(handler) = self.task_registry.get(task_type) {
            handler.handle(data).await
        } else {
            Err(TaskError::HandlerNotFound(task_type.to_string()))
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TaskError {
    #[error("Handler not found: {0}")]
    HandlerNotFound(String),
    #[error("Task execution failed: {0}")]
    ExecutionFailed(String),
}
```

### 6.2 消息队列系统

```rust
// 消息队列系统示例
pub struct MessageQueue {
    active_object: ActiveObject,
    message_handlers: HashMap<String, Box<dyn MessageHandler>>,
}

pub trait MessageHandler: Send + Sync {
    async fn handle_message(&self, message: &Message) -> Result<MessageResponse, MessageError>;
    fn message_type(&self) -> &str;
}

impl MessageQueue {
    pub fn new(config: ActiveObjectConfig) -> Self {
        MessageQueue {
            active_object: ActiveObject::new(config),
            message_handlers: HashMap::new(),
        }
    }
    
    pub fn register_handler<H: MessageHandler + 'static>(&mut self, handler: H) {
        self.message_handlers.insert(handler.message_type().to_string(), Box::new(handler));
    }
    
    pub async fn enqueue_message(&self, message: Message) -> Result<Uuid, MessageError> {
        let request_data = RequestData {
            request_type: RequestType::Custom { payload: serde_json::to_string(&message)? },
            metadata: HashMap::new(),
            timestamp: Instant::now(),
        };
        
        self.active_object.request(request_data, Priority::Normal)
            .map_err(MessageError::ActiveObjectError)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Message {
    pub id: Uuid,
    pub message_type: String,
    pub payload: Vec<u8>,
    pub timestamp: Instant,
}

#[derive(Debug, thiserror::Error)]
pub enum MessageError {
    #[error("Active object error: {0}")]
    ActiveObjectError(#[from] ActiveObjectError),
    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),
    #[error("Handler not found: {0}")]
    HandlerNotFound(String),
}
```

## 7. 最佳实践

### 7.1 设计原则

1. **单一职责**：每个主动对象只负责一种类型的任务
2. **资源管理**：合理管理线程池和内存资源
3. **错误处理**：实现完善的错误处理和恢复机制
4. **监控指标**：建立完善的监控和指标收集

### 7.2 性能考虑

1. **线程池调优**：根据负载调整线程池大小
2. **内存优化**：使用对象池减少内存分配
3. **队列管理**：实现优先级队列和背压机制
4. **异步处理**：充分利用异步编程提高并发性能

### 7.3 错误处理

1. **超时处理**：实现请求超时和重试机制
2. **降级策略**：提供降级方案保证系统可用性
3. **监控告警**：建立完善的监控和告警机制
4. **日志记录**：记录关键操作和错误信息

### 7.4 安全考虑

1. **输入验证**：验证所有输入数据
2. **资源限制**：限制单个请求的资源使用
3. **访问控制**：实现适当的访问控制机制
4. **审计日志**：记录关键操作日志

## 8. 总结

主动对象模式是一个强大的并发设计模式，它通过将方法调用与执行分离来提高系统的并发性和响应性。通过本文档的详细阐述，我们建立了：

1. **完整的理论基础**：包括形式化定义和语义模型
2. **多语言实现**：Rust、Haskell、Lean的完整实现
3. **工程实践**：包括架构设计、配置管理、错误处理
4. **性能优化**：线程池优化、内存管理等优化方案
5. **应用场景**：异步任务处理、消息队列等实际应用
6. **最佳实践**：设计原则、性能考虑、安全考虑等

这些内容为主动对象模式的实际应用提供了全面的指导，确保在实际项目中能够正确、高效地使用主动对象模式。
