# Master-Worker模式（Master-Worker Pattern）

## 概述
Master-Worker模式是一种并行设计模式，由一个Master节点负责任务分配和结果收集，多个Worker节点并行执行具体任务。

## 理论基础
- **任务分配**：Master负责任务分解和分配
- **并行执行**：Worker并行处理分配的任务
- **结果收集**：Master收集和整合Worker的结果

## Rust实现示例
```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;

// 任务类型
#[derive(Clone)]
struct Task {
    id: u32,
    data: String,
}

// 结果类型
#[derive(Clone)]
struct Result {
    task_id: u32,
    processed_data: String,
}

// Worker节点
struct Worker {
    id: u32,
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    result_queue: Arc<Mutex<VecDeque<Result>>>,
    condition: Arc<Condvar>,
    running: Arc<Mutex<bool>>,
}

impl Worker {
    fn new(
        id: u32,
        task_queue: Arc<Mutex<VecDeque<Task>>>,
        result_queue: Arc<Mutex<VecDeque<Result>>>,
        condition: Arc<Condvar>,
        running: Arc<Mutex<bool>>,
    ) -> Self {
        Self {
            id,
            task_queue,
            result_queue,
            condition,
            running,
        }
    }
    
    fn start(&self) {
        let worker_id = self.id;
        let task_queue = Arc::clone(&self.task_queue);
        let result_queue = Arc::clone(&self.result_queue);
        let condition = Arc::clone(&self.condition);
        let running = Arc::clone(&self.running);
        
        thread::spawn(move || {
            while *running.lock().unwrap() {
                let task = {
                    let mut queue_guard = task_queue.lock().unwrap();
                    while queue_guard.is_empty() && *running.lock().unwrap() {
                        queue_guard = condition.wait(queue_guard).unwrap();
                    }
                    queue_guard.pop_front()
                };
                
                if let Some(task) = task {
                    // 处理任务
                    let result = Self::process_task(task, worker_id);
                    
                    // 提交结果
                    if let Ok(mut result_queue) = result_queue.lock() {
                        result_queue.push_back(result);
                    }
                }
            }
        });
    }
    
    fn process_task(task: Task, worker_id: u32) -> Result {
        // 模拟处理时间
        thread::sleep(Duration::from_millis(100));
        
        Result {
            task_id: task.id,
            processed_data: format!("Worker {} 处理了任务 {}", worker_id, task.data),
        }
    }
}

// Master节点
struct Master {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    result_queue: Arc<Mutex<VecDeque<Result>>>,
    condition: Arc<Condvar>,
    running: Arc<Mutex<bool>>,
    workers: Vec<Worker>,
}

impl Master {
    fn new(num_workers: u32) -> Self {
        let task_queue = Arc::new(Mutex::new(VecDeque::new()));
        let result_queue = Arc::new(Mutex::new(VecDeque::new()));
        let condition = Arc::new(Condvar::new());
        let running = Arc::new(Mutex::new(true));
        
        let mut workers = Vec::new();
        for i in 0..num_workers {
            let worker = Worker::new(
                i,
                Arc::clone(&task_queue),
                Arc::clone(&result_queue),
                Arc::clone(&condition),
                Arc::clone(&running),
            );
            workers.push(worker);
        }
        
        Self {
            task_queue,
            result_queue,
            condition,
            running,
            workers,
        }
    }
    
    fn start(&self) {
        // 启动所有Worker
        for worker in &self.workers {
            worker.start();
        }
    }
    
    fn submit_task(&self, task: Task) {
        if let Ok(mut queue) = self.task_queue.lock() {
            queue.push_back(task);
            self.condition.notify_one();
        }
    }
    
    fn submit_tasks(&self, tasks: Vec<Task>) {
        if let Ok(mut queue) = self.task_queue.lock() {
            for task in tasks {
                queue.push_back(task);
            }
            self.condition.notify_all();
        }
    }
    
    fn get_results(&self) -> Vec<Result> {
        if let Ok(mut queue) = self.result_queue.lock() {
            queue.drain(..).collect()
        } else {
            Vec::new()
        }
    }
    
    fn shutdown(&self) {
        *self.running.lock().unwrap() = false;
        self.condition.notify_all();
    }
}

// 任务生成器
struct TaskGenerator;

impl TaskGenerator {
    fn generate_tasks(count: u32) -> Vec<Task> {
        (0..count)
            .map(|i| Task {
                id: i,
                data: format!("任务数据 {}", i),
            })
            .collect()
    }
}

// 结果处理器
struct ResultProcessor;

impl ResultProcessor {
    fn process_results(results: Vec<Result>) {
        println!("处理了 {} 个结果:", results.len());
        for result in results {
            println!("任务 {}: {}", result.task_id, result.processed_data);
        }
    }
}

// 负载均衡Master
struct LoadBalancedMaster {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    result_queue: Arc<Mutex<VecDeque<Result>>>,
    condition: Arc<Condvar>,
    running: Arc<Mutex<bool>>,
    workers: Vec<Worker>,
    worker_stats: Arc<Mutex<Vec<u32>>>,
}

impl LoadBalancedMaster {
    fn new(num_workers: u32) -> Self {
        let task_queue = Arc::new(Mutex::new(VecDeque::new()));
        let result_queue = Arc::new(Mutex::new(VecDeque::new()));
        let condition = Arc::new(Condvar::new());
        let running = Arc::new(Mutex::new(true));
        let worker_stats = Arc::new(Mutex::new(vec![0; num_workers as usize]));
        
        let mut workers = Vec::new();
        for i in 0..num_workers {
            let worker = Worker::new(
                i,
                Arc::clone(&task_queue),
                Arc::clone(&result_queue),
                Arc::clone(&condition),
                Arc::clone(&running),
            );
            workers.push(worker);
        }
        
        Self {
            task_queue,
            result_queue,
            condition,
            running,
            workers,
            worker_stats,
        }
    }
    
    fn submit_task_with_load_balancing(&self, task: Task) {
        // 简单的轮询负载均衡
        if let Ok(mut stats) = self.worker_stats.lock() {
            let worker_index = stats.iter().enumerate().min_by_key(|(_, &count)| count).unwrap().0;
            stats[worker_index] += 1;
        }
        
        if let Ok(mut queue) = self.task_queue.lock() {
            queue.push_back(task);
            self.condition.notify_one();
        }
    }
}

fn main() {
    // 基本Master-Worker示例
    let master = Master::new(4);
    master.start();
    
    // 生成任务
    let tasks = TaskGenerator::generate_tasks(10);
    master.submit_tasks(tasks);
    
    // 等待处理完成
    thread::sleep(Duration::from_millis(2000));
    
    // 获取结果
    let results = master.get_results();
    ResultProcessor::process_results(results);
    
    // 关闭Master
    master.shutdown();
    
    // 负载均衡示例
    let lb_master = LoadBalancedMaster::new(4);
    lb_master.start();
    
    let lb_tasks = TaskGenerator::generate_tasks(20);
    for task in lb_tasks {
        lb_master.submit_task_with_load_balancing(task);
    }
    
    thread::sleep(Duration::from_millis(3000));
    let lb_results = lb_master.get_results();
    println!("负载均衡处理完成，结果数量: {}", lb_results.len());
    
    lb_master.shutdown();
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef

-- 任务类型
data Task = Task
    { taskId :: Int
    , taskData :: String
    }

-- 结果类型
data Result = Result
    { resultTaskId :: Int
    , processedData :: String
    }

-- Worker节点
data Worker = Worker
    { workerId :: Int
    , taskQueue :: TVar [Task]
    , resultQueue :: TVar [Result]
    , running :: TVar Bool
    }

newWorker :: Int -> TVar [Task] -> TVar [Result] -> TVar Bool -> IO Worker
newWorker id taskQueue resultQueue running = do
    return $ Worker id taskQueue resultQueue running

startWorker :: Worker -> IO ()
startWorker worker = do
    forkIO $ workerLoop worker
    return ()

workerLoop :: Worker -> IO ()
workerLoop worker = do
    shouldRun <- readTVarIO (running worker)
    if shouldRun
        then do
            task <- atomically $ do
                tasks <- readTVar (taskQueue worker)
                case tasks of
                    [] -> retry
                    (t:ts) -> do
                        writeTVar (taskQueue worker) ts
                        return t
            -- 处理任务
            let result = processTask task (workerId worker)
            -- 提交结果
            atomically $ do
                results <- readTVar (resultQueue worker)
                writeTVar (resultQueue worker) (result : results)
            workerLoop worker
        else return ()

processTask :: Task -> Int -> Result
processTask task workerId = do
    threadDelay 100000 -- 模拟处理时间
    Result
        { resultTaskId = taskId task
        , processedData = "Worker " ++ show workerId ++ " 处理了任务 " ++ taskData task
        }

-- Master节点
data Master = Master
    { taskQueue :: TVar [Task]
    , resultQueue :: TVar [Result]
    , running :: TVar Bool
    , workers :: [Worker]
    }

newMaster :: Int -> IO Master
newMaster numWorkers = do
    taskQueue <- newTVarIO []
    resultQueue <- newTVarIO []
    running <- newTVarIO True
    
    workers <- mapM (\id -> newWorker id taskQueue resultQueue running) [0..numWorkers-1]
    
    return $ Master taskQueue resultQueue running workers

startMaster :: Master -> IO ()
startMaster master = do
    mapM_ startWorker (workers master)

submitTask :: Master -> Task -> IO ()
submitTask master task = do
    atomically $ do
        tasks <- readTVar (taskQueue master)
        writeTVar (taskQueue master) (task : tasks)

submitTasks :: Master -> [Task] -> IO ()
submitTasks master tasks = do
    atomically $ do
        currentTasks <- readTVar (taskQueue master)
        writeTVar (taskQueue master) (tasks ++ currentTasks)

getResults :: Master -> IO [Result]
getResults master = do
    atomically $ do
        results <- readTVar (resultQueue master)
        writeTVar (resultQueue master) []
        return results

shutdownMaster :: Master -> IO ()
shutdownMaster master = do
    atomically $ writeTVar (running master) False

-- 任务生成器
generateTasks :: Int -> [Task]
generateTasks count = [Task i ("任务数据 " ++ show i) | i <- [0..count-1]]

-- 结果处理器
processResults :: [Result] -> IO ()
processResults results = do
    putStrLn $ "处理了 " ++ show (length results) ++ " 个结果:"
    mapM_ (\result -> putStrLn $ "任务 " ++ show (resultTaskId result) ++ ": " ++ processedData result) results

-- 负载均衡Master
data LoadBalancedMaster = LoadBalancedMaster
    { lbTaskQueue :: TVar [Task]
    , lbResultQueue :: TVar [Result]
    , lbRunning :: TVar Bool
    , lbWorkers :: [Worker]
    , workerStats :: TVar [Int]
    }

newLoadBalancedMaster :: Int -> IO LoadBalancedMaster
newLoadBalancedMaster numWorkers = do
    taskQueue <- newTVarIO []
    resultQueue <- newTVarIO []
    running <- newTVarIO True
    workerStats <- newTVarIO (replicate numWorkers 0)
    
    workers <- mapM (\id -> newWorker id taskQueue resultQueue running) [0..numWorkers-1]
    
    return $ LoadBalancedMaster taskQueue resultQueue running workers workerStats

submitTaskWithLoadBalancing :: LoadBalancedMaster -> Task -> IO ()
submitTaskWithLoadBalancing lbm task = do
    -- 简单的轮询负载均衡
    atomically $ do
        stats <- readTVar (workerStats lbm)
        let workerIndex = minimum (zip [0..] stats) & snd & minimum & fst
        writeTVar (workerStats lbm) (updateAt workerIndex (+1) stats)
    
    atomically $ do
        tasks <- readTVar (lbTaskQueue lbm)
        writeTVar (lbTaskQueue lbm) (task : tasks)

-- 测试函数
testBasicMasterWorker :: IO ()
testBasicMasterWorker = do
    master <- newMaster 4
    startMaster master
    
    let tasks = generateTasks 10
    submitTasks master tasks
    
    threadDelay 2000000
    results <- getResults master
    processResults results
    
    shutdownMaster master

testLoadBalancedMasterWorker :: IO ()
testLoadBalancedMasterWorker = do
    lbm <- newLoadBalancedMaster 4
    startMaster lbm
    
    let tasks = generateTasks 20
    mapM_ (submitTaskWithLoadBalancing lbm) tasks
    
    threadDelay 3000000
    results <- getResults lbm
    putStrLn $ "负载均衡处理完成，结果数量: " ++ show (length results)
    
    shutdownMaster lbm

main :: IO ()
main = do
    testBasicMasterWorker
    testLoadBalancedMasterWorker
```

## Lean实现思路
```lean
-- 任务类型
structure Task where
  taskId : Nat
  taskData : String

-- 结果类型
structure Result where
  resultTaskId : Nat
  processedData : String

-- Worker节点
structure Worker where
  workerId : Nat
  taskQueue : List Task
  resultQueue : List Result
  running : Bool

def newWorker (id : Nat) : Worker :=
  { workerId := id
  , taskQueue := []
  , resultQueue := []
  , running := true
  }

def processTask (task : Task) (workerId : Nat) : Result :=
  { resultTaskId := task.taskId
  , processedData := "Worker " ++ toString workerId ++ " 处理了任务 " ++ task.taskData
  }

-- Master节点
structure Master where
  taskQueue : List Task
  resultQueue : List Result
  running : Bool
  workers : List Worker

def newMaster (numWorkers : Nat) : Master :=
  { taskQueue := []
  , resultQueue := []
  , running := true
  , workers := List.range numWorkers |>.map newWorker
  }

def submitTask (master : Master) (task : Task) : Master :=
  { master with taskQueue := task :: master.taskQueue }

def getResults (master : Master) : (List Result × Master) :=
  (master.resultQueue, { master with resultQueue := [] })

def shutdownMaster (master : Master) : Master :=
  { master with running := false }

-- 任务生成器
def generateTasks (count : Nat) : List Task :=
  List.range count |>.map fun i =>
    { taskId := i
    , taskData := "任务数据 " ++ toString i
    }
```

## 应用场景
- 分布式计算
- 图像渲染
- 数据处理
- 网络爬虫

## 最佳实践
- 实现负载均衡
- 处理Worker故障
- 监控任务进度
- 优化任务粒度 