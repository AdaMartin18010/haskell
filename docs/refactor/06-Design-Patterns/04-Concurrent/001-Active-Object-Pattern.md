# 主动对象模式（Active Object Pattern）

## 概述
主动对象模式是一种并发设计模式，将方法调用与执行分离，每个主动对象都有自己的控制线程，方法调用被封装成请求对象并放入队列中异步执行。

## 理论基础
- **方法调用与执行分离**：调用立即返回，执行异步进行
- **请求队列**：使用队列管理待执行的请求
- **调度器**：独立的调度线程处理请求

## Rust实现示例
```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;

// 请求特征
trait Request {
    fn execute(&self);
}

// 具体请求
struct ConcreteRequest {
    message: String,
}

impl ConcreteRequest {
    fn new(message: String) -> Self {
        Self { message }
    }
}

impl Request for ConcreteRequest {
    fn execute(&self) {
        println!("执行请求: {}", self.message);
        thread::sleep(Duration::from_millis(100));
    }
}

// 调度器
struct Scheduler {
    queue: Arc<Mutex<VecDeque<Box<dyn Request + Send>>>>,
    condition: Arc<Condvar>,
    running: Arc<Mutex<bool>>,
}

impl Scheduler {
    fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            condition: Arc::new(Condvar::new()),
            running: Arc::new(Mutex::new(true)),
        }
    }
    
    fn start(&self) {
        let queue = Arc::clone(&self.queue);
        let condition = Arc::clone(&self.condition);
        let running = Arc::clone(&self.running);
        
        thread::spawn(move || {
            while *running.lock().unwrap() {
                let request = {
                    let mut queue_guard = queue.lock().unwrap();
                    while queue_guard.is_empty() && *running.lock().unwrap() {
                        queue_guard = condition.wait(queue_guard).unwrap();
                    }
                    queue_guard.pop_front()
                };
                
                if let Some(request) = request {
                    request.execute();
                }
            }
        });
    }
    
    fn stop(&self) {
        *self.running.lock().unwrap() = false;
        self.condition.notify_all();
    }
    
    fn enqueue(&self, request: Box<dyn Request + Send>) {
        if let Ok(mut queue) = self.queue.lock() {
            queue.push_back(request);
            self.condition.notify_one();
        }
    }
}

// 主动对象
struct ActiveObject {
    scheduler: Scheduler,
}

impl ActiveObject {
    fn new() -> Self {
        let scheduler = Scheduler::new();
        scheduler.start();
        Self { scheduler }
    }
    
    fn request(&self, message: String) {
        let request = Box::new(ConcreteRequest::new(message));
        self.scheduler.enqueue(request);
    }
    
    fn shutdown(&self) {
        self.scheduler.stop();
    }
}

fn main() {
    let active_object = ActiveObject::new();
    
    // 发送多个请求
    for i in 0..5 {
        active_object.request(format!("请求 {}", i));
    }
    
    // 等待一段时间让请求执行
    thread::sleep(Duration::from_millis(1000));
    
    active_object.shutdown();
    println!("主动对象已关闭");
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef

-- 请求类型
class Request a where
    execute :: a -> IO ()

data ConcreteRequest = ConcreteRequest String
instance Request ConcreteRequest where
    execute (ConcreteRequest message) = do
        putStrLn $ "执行请求: " ++ message
        threadDelay 100000

-- 调度器
data Scheduler = Scheduler 
    { queue :: TVar [ConcreteRequest]
    , running :: TVar Bool
    }

newScheduler :: IO Scheduler
newScheduler = do
    queue <- newTVarIO []
    running <- newTVarIO True
    return $ Scheduler queue running

startScheduler :: Scheduler -> IO ()
startScheduler scheduler = do
    forkIO $ schedulerLoop scheduler
    return ()

schedulerLoop :: Scheduler -> IO ()
schedulerLoop scheduler = do
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
            execute request
            schedulerLoop scheduler
        else return ()

stopScheduler :: Scheduler -> IO ()
stopScheduler scheduler = do
    atomically $ writeTVar (running scheduler) False

enqueueRequest :: Scheduler -> ConcreteRequest -> IO ()
enqueueRequest scheduler request = do
    atomically $ do
        requests <- readTVar (queue scheduler)
        writeTVar (queue scheduler) (requests ++ [request])

-- 主动对象
data ActiveObject = ActiveObject Scheduler

newActiveObject :: IO ActiveObject
newActiveObject = do
    scheduler <- newScheduler
    startScheduler scheduler
    return $ ActiveObject scheduler

request :: ActiveObject -> String -> IO ()
request (ActiveObject scheduler) message = do
    let request = ConcreteRequest message
    enqueueRequest scheduler request

shutdown :: ActiveObject -> IO ()
shutdown (ActiveObject scheduler) = do
    stopScheduler scheduler

main = do
    activeObject <- newActiveObject
    
    -- 发送多个请求
    mapM_ (\i -> request activeObject ("请求 " ++ show i)) [0..4]
    
    -- 等待一段时间让请求执行
    threadDelay 1000000
    
    shutdown activeObject
    putStrLn "主动对象已关闭"
```

## Lean实现思路
```lean
-- 请求类型类
class Request (α : Type) where
  execute : α → IO Unit

-- 具体请求
structure ConcreteRequest where
  message : String

instance : Request ConcreteRequest where
  execute request := do
    IO.println ("执行请求: " ++ request.message)
    IO.sleep 100

-- 调度器
structure Scheduler where
  queue : List ConcreteRequest
  running : Bool

def newScheduler : IO Scheduler :=
  pure { queue := [], running := true }

def startScheduler (scheduler : Scheduler) : IO Unit := do
  -- 启动调度线程
  IO.println "调度器已启动"

def stopScheduler (scheduler : Scheduler) : Scheduler :=
  { scheduler with running := false }

def enqueueRequest (scheduler : Scheduler) (request : ConcreteRequest) : Scheduler :=
  { scheduler with queue := scheduler.queue ++ [request] }

-- 主动对象
structure ActiveObject where
  scheduler : Scheduler

def newActiveObject : IO ActiveObject := do
  let scheduler := newScheduler
  startScheduler scheduler
  pure { scheduler := scheduler }

def request (activeObject : ActiveObject) (message : String) : ActiveObject :=
  let request := ConcreteRequest message
  { activeObject with scheduler := enqueueRequest activeObject.scheduler request }

def shutdown (activeObject : ActiveObject) : ActiveObject :=
  { activeObject with scheduler := stopScheduler activeObject.scheduler }
```

## 应用场景
- 异步任务处理
- 消息队列系统
- 事件驱动架构
- 并发服务器

## 最佳实践
- 合理控制队列大小
- 实现请求优先级
- 提供取消机制
- 监控队列状态 