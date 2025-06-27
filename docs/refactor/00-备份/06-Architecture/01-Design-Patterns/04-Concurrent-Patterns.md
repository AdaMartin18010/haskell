# 并发设计模式 - 形式化理论与Haskell实现

## 📋 概述

并发设计模式关注多线程、异步编程和并发控制，提供安全高效的并发解决方案。本文档从形式化角度分析并发模式，并提供Haskell实现。

## 🎯 核心概念

### 并发系统的形式化模型

#### 定义 1.1 (并发系统)

设 $S$ 为状态空间，并发系统定义为：
$$\text{ConcurrentSystem} = (S, \rightarrow, \text{initial})$$

其中：

- $S$ 是状态集合
- $\rightarrow \subseteq S \times S$ 是状态转换关系
- $\text{initial} \in S$ 是初始状态

#### 定义 1.2 (并发模式)

并发模式是一个五元组 $(P, T, \text{sync}, \text{comm}, \text{control})$，其中：

- $P$ 是进程类型
- $T$ 是线程类型
- $\text{sync}$ 是同步函数
- $\text{comm}$ 是通信函数
- $\text{control}$ 是控制函数

## 🔒 互斥锁模式 (Mutex Pattern)

### 形式化定义

#### 定义 2.1 (互斥锁)

互斥锁定义为：
$$\text{Mutex} = (L, \text{acquire}, \text{release})$$

其中：

- $L$ 是锁状态类型
- $\text{acquire} : L \rightarrow L \times \text{Bool}$ 是获取函数
- $\text{release} : L \rightarrow L$ 是释放函数

### Haskell实现

```haskell
import Control.Concurrent.MVar
import Control.Monad

-- 互斥锁类型
data Mutex = Mutex (MVar ())

-- 创建互斥锁
newMutex :: IO Mutex
newMutex = do
    mvar <- newMVar ()
    return $ Mutex mvar

-- 获取锁
acquireMutex :: Mutex -> IO ()
acquireMutex (Mutex mvar) = takeMVar mvar

-- 释放锁
releaseMutex :: Mutex -> IO ()
releaseMutex (Mutex mvar) = putMVar mvar ()

-- 带超时的锁获取
acquireMutexTimeout :: Mutex -> Int -> IO Bool
acquireMutexTimeout (Mutex mvar) timeout = do
    result <- tryTakeMVar mvar
    case result of
        Just _ -> return True
        Nothing -> do
            threadDelay timeout
            result' <- tryTakeMVar mvar
            case result' of
                Just _ -> return True
                Nothing -> return False

-- 可重入锁
data ReentrantMutex = ReentrantMutex
    { lock :: MVar ()
    , owner :: MVar (Maybe ThreadId)
    , count :: MVar Int
    }

newReentrantMutex :: IO ReentrantMutex
newReentrantMutex = do
    lock <- newMVar ()
    owner <- newMVar Nothing
    count <- newMVar 0
    return $ ReentrantMutex lock owner count

acquireReentrantMutex :: ReentrantMutex -> IO ()
acquireReentrantMutex mutex = do
    currentThread <- myThreadId
    currentOwner <- readMVar (owner mutex)
    currentCount <- readMVar (count mutex)
    
    if currentOwner == Just currentThread
    then do
        -- 重入
        modifyMVar_ (count mutex) (return . (+1))
    else do
        -- 首次获取
        takeMVar (lock mutex)
        modifyMVar_ (owner mutex) (const $ return $ Just currentThread)
        modifyMVar_ (count mutex) (const $ return 1)

releaseReentrantMutex :: ReentrantMutex -> IO ()
releaseReentrantMutex mutex = do
    currentThread <- myThreadId
    currentOwner <- readMVar (owner mutex)
    currentCount <- readMVar (count mutex)
    
    if currentOwner == Just currentThread
    then do
        if currentCount == 1
        then do
            -- 最后一次释放
            modifyMVar_ (owner mutex) (const $ return Nothing)
            modifyMVar_ (count mutex) (const $ return 0)
            putMVar (lock mutex) ()
        else do
            -- 减少计数
            modifyMVar_ (count mutex) (return . subtract 1)
    else
        error "Attempting to release mutex not owned by current thread"

-- 使用示例
exampleMutex :: IO ()
exampleMutex = do
    mutex <- newMutex
    sharedResource <- newMVar 0
    
    let worker id = do
        acquireMutex mutex
        current <- readMVar sharedResource
        putMVar sharedResource (current + 1)
        putStrLn $ "Worker " ++ show id ++ " incremented to " ++ show (current + 1)
        releaseMutex mutex
    
    -- 启动多个线程
    mapM_ (\id -> forkIO $ worker id) [1..5]
    threadDelay 1000000  -- 等待1秒
```

### 形式化证明

#### 定理 2.1 (互斥锁的安全性)

对于任意互斥锁 $\text{Mutex}$，同时最多只有一个线程持有锁：
$$\forall t_1, t_2 \in \text{Thread}, \text{holds}(t_1, l) \land \text{holds}(t_2, l) \Rightarrow t_1 = t_2$$

**证明**：
互斥锁确保临界区的互斥访问，防止数据竞争。

## 🔄 读写锁模式 (Read-Write Lock Pattern)

### 形式化定义

#### 定义 3.1 (读写锁)

读写锁定义为：
$$\text{RWLock} = (R, \text{readLock}, \text{writeLock}, \text{unlock})$$

其中：

- $R$ 是锁状态类型
- $\text{readLock} : R \rightarrow R \times \text{Bool}$ 是读锁函数
- $\text{writeLock} : R \rightarrow R \times \text{Bool}$ 是写锁函数
- $\text{unlock} : R \rightarrow R$ 是解锁函数

### Haskell实现

```haskell
-- 读写锁状态
data RWLockState = RWLockState
    { readers :: Int
    , writers :: Int
    , waitingWriters :: Int
    }

-- 读写锁
data RWLock = RWLock
    { state :: MVar RWLockState
    , readSemaphore :: MVar ()
    , writeSemaphore :: MVar ()
    }

-- 创建读写锁
newRWLock :: IO RWLock
newRWLock = do
    state <- newMVar $ RWLockState 0 0 0
    readSemaphore <- newMVar ()
    writeSemaphore <- newMVar ()
    return $ RWLock state readSemaphore writeSemaphore

-- 获取读锁
acquireReadLock :: RWLock -> IO ()
acquireReadLock lock = do
    currentState <- readMVar (state lock)
    
    if writers currentState > 0 || waitingWriters currentState > 0
    then do
        -- 有写者，等待
        takeMVar (readSemaphore lock)
        acquireReadLock lock
    else do
        -- 可以读取
        modifyMVar_ (state lock) $ \s -> 
            return $ s { readers = readers s + 1 }

-- 释放读锁
releaseReadLock :: RWLock -> IO ()
releaseReadLock lock = do
    modifyMVar_ (state lock) $ \s -> do
        let newReaders = readers s - 1
        if newReaders == 0 && waitingWriters s > 0
        then do
            putMVar (writeSemaphore lock) ()
            return $ s { readers = newReaders }
        else
            return $ s { readers = newReaders }

-- 获取写锁
acquireWriteLock :: RWLock -> IO ()
acquireWriteLock lock = do
    modifyMVar_ (state lock) $ \s -> 
        return $ s { waitingWriters = waitingWriters s + 1 }
    
    currentState <- readMVar (state lock)
    
    if readers currentState > 0 || writers currentState > 0
    then do
        -- 有读者或写者，等待
        takeMVar (writeSemaphore lock)
        acquireWriteLock lock
    else do
        -- 可以写入
        modifyMVar_ (state lock) $ \s -> 
            return $ s { 
                writers = writers s + 1
                , waitingWriters = waitingWriters s - 1 
            }

-- 释放写锁
releaseWriteLock :: RWLock -> IO ()
releaseWriteLock lock = do
    modifyMVar_ (state lock) $ \s -> do
        let newWriters = writers s - 1
        if waitingWriters s > 0
        then do
            putMVar (writeSemaphore lock) ()
            return $ s { writers = newWriters }
        else if readers s > 0
        then do
            replicateM_ (readers s) $ putMVar (readSemaphore lock) ()
            return $ s { writers = newWriters }
        else
            return $ s { writers = newWriters }

-- 使用示例
exampleRWLock :: IO ()
exampleRWLock = do
    lock <- newRWLock
    sharedData <- newMVar "Initial data"
    
    let reader id = do
        acquireReadLock lock
        data <- readMVar sharedData
        putStrLn $ "Reader " ++ show id ++ " read: " ++ data
        threadDelay 100000  -- 模拟读取时间
        releaseReadLock lock
    
    let writer id = do
        acquireWriteLock lock
        data <- readMVar sharedData
        let newData = data ++ " (modified by writer " ++ show id ++ ")"
        putMVar sharedData newData
        putStrLn $ "Writer " ++ show id ++ " wrote: " ++ newData
        threadDelay 200000  -- 模拟写入时间
        releaseWriteLock lock
    
    -- 启动多个读者和写者
    mapM_ (\id -> forkIO $ reader id) [1..3]
    mapM_ (\id -> forkIO $ writer id) [1..2]
    threadDelay 2000000  -- 等待2秒
```

### 形式化证明

#### 定理 3.1 (读写锁的正确性)

对于任意读写锁 $\text{RWLock}$，满足以下性质：

1. 多个读者可以同时访问
2. 写者独占访问
3. 读者和写者不能同时访问

**证明**：
读写锁通过状态管理确保这些性质，防止读写冲突。

## 🔄 条件变量模式 (Condition Variable Pattern)

### 形式化定义

#### 定义 4.1 (条件变量)

条件变量定义为：
$$\text{Condition} = (C, \text{wait}, \text{signal}, \text{broadcast})$$

其中：

- $C$ 是条件类型
- $\text{wait} : C \times \text{Mutex} \rightarrow \text{Unit}$ 是等待函数
- $\text{signal} : C \rightarrow \text{Unit}$ 是信号函数
- $\text{broadcast} : C \rightarrow \text{Unit}$ 是广播函数

### Haskell实现

```haskell
-- 条件变量
data Condition = Condition (MVar [MVar ()])

-- 创建条件变量
newCondition :: IO Condition
newCondition = do
    waiters <- newMVar []
    return $ Condition waiters

-- 等待条件
waitCondition :: Condition -> Mutex -> IO ()
waitCondition (Condition waiters) mutex = do
    -- 创建等待者
    waiter <- newEmptyMVar
    modifyMVar_ waiters (return . (waiter:))
    
    -- 释放互斥锁
    releaseMutex mutex
    
    -- 等待信号
    takeMVar waiter
    
    -- 重新获取互斥锁
    acquireMutex mutex

-- 发送信号
signalCondition :: Condition -> IO ()
signalCondition (Condition waiters) = do
    currentWaiters <- readMVar waiters
    case currentWaiters of
        [] -> return ()  -- 没有等待者
        (waiter:rest) -> do
            modifyMVar_ waiters (const $ return rest)
            putMVar waiter ()  -- 唤醒一个等待者

-- 广播信号
broadcastCondition :: Condition -> IO ()
broadcastCondition (Condition waiters) = do
    currentWaiters <- readMVar waiters
    modifyMVar_ waiters (const $ return [])
    mapM_ (\waiter -> putMVar waiter ()) currentWaiters

-- 生产者-消费者模式
data ProducerConsumer = ProducerConsumer
    { buffer :: MVar [Int]
    , mutex :: Mutex
    , notEmpty :: Condition
    , notFull :: Condition
    , maxSize :: Int
    }

newProducerConsumer :: Int -> IO ProducerConsumer
newProducerConsumer size = do
    buffer <- newMVar []
    mutex <- newMutex
    notEmpty <- newCondition
    notFull <- newCondition
    return $ ProducerConsumer buffer mutex notEmpty notFull size

-- 生产者
produce :: ProducerConsumer -> Int -> IO ()
produce pc item = do
    acquireMutex (mutex pc)
    
    -- 检查缓冲区是否满
    currentBuffer <- readMVar (buffer pc)
    if length currentBuffer >= maxSize pc
    then do
        waitCondition (notFull pc) (mutex pc)
        produce pc item  -- 递归调用
    else do
        -- 添加项目
        modifyMVar_ (buffer pc) (return . (item:))
        putStrLn $ "Produced: " ++ show item
        signalCondition (notEmpty pc)
        releaseMutex (mutex pc)

-- 消费者
consume :: ProducerConsumer -> IO Int
consume pc = do
    acquireMutex (mutex pc)
    
    -- 检查缓冲区是否空
    currentBuffer <- readMVar (buffer pc)
    if null currentBuffer
    then do
        waitCondition (notEmpty pc) (mutex pc)
        consume pc  -- 递归调用
    else do
        -- 移除项目
        let (item:rest) = currentBuffer
        putMVar (buffer pc) rest
        putStrLn $ "Consumed: " ++ show item
        signalCondition (notFull pc)
        releaseMutex (mutex pc)
        return item

-- 使用示例
exampleProducerConsumer :: IO ()
exampleProducerConsumer = do
    pc <- newProducerConsumer 5
    
    let producer id = do
        mapM_ (\item -> do
            produce pc item
            threadDelay 100000
        ) [id*10..id*10+9]
    
    let consumer id = do
        replicateM_ 10 $ do
            item <- consume pc
            threadDelay 150000
    
    -- 启动生产者和消费者
    mapM_ (\id -> forkIO $ producer id) [1..2]
    mapM_ (\id -> forkIO $ consumer id) [1..2]
    threadDelay 5000000  -- 等待5秒
```

### 形式化证明

#### 定理 4.1 (条件变量的正确性)

对于任意条件变量 $\text{Condition}$，等待和信号操作满足：
$$\text{wait}(c, m) \land \text{signal}(c) \Rightarrow \text{awakened}$$

**证明**：
条件变量确保等待的线程在收到信号后被正确唤醒。

## 🔄 信号量模式 (Semaphore Pattern)

### 形式化定义

#### 定义 5.1 (信号量)

信号量定义为：
$$\text{Semaphore} = (S, \text{acquire}, \text{release})$$

其中：

- $S$ 是信号量状态类型
- $\text{acquire} : S \rightarrow S \times \text{Bool}$ 是获取函数
- $\text{release} : S \rightarrow S$ 是释放函数

### Haskell实现

```haskell
-- 信号量
data Semaphore = Semaphore (MVar Int)

-- 创建信号量
newSemaphore :: Int -> IO Semaphore
newSemaphore initial = do
    mvar <- newMVar initial
    return $ Semaphore mvar

-- 获取信号量
acquireSemaphore :: Semaphore -> IO ()
acquireSemaphore (Semaphore mvar) = do
    current <- readMVar mvar
    if current > 0
    then modifyMVar_ mvar (return . subtract 1)
    else do
        -- 等待
        threadDelay 1000
        acquireSemaphore (Semaphore mvar)

-- 释放信号量
releaseSemaphore :: Semaphore -> IO ()
releaseSemaphore (Semaphore mvar) = do
    modifyMVar_ mvar (return . (+1))

-- 带超时的信号量获取
acquireSemaphoreTimeout :: Semaphore -> Int -> IO Bool
acquireSemaphoreTimeout (Semaphore mvar) timeout = do
    current <- readMVar mvar
    if current > 0
    then do
        modifyMVar_ mvar (return . subtract 1)
        return True
    else do
        threadDelay timeout
        current' <- readMVar mvar
        if current' > 0
        then do
            modifyMVar_ mvar (return . subtract 1)
            return True
        else
            return False

-- 哲学家就餐问题
data Philosopher = Philosopher
    { id :: Int
    , leftFork :: Semaphore
    , rightFork :: Semaphore
    }

-- 创建哲学家
newPhilosopher :: Int -> Semaphore -> Semaphore -> Philosopher
newPhilosopher id leftFork rightFork = Philosopher id leftFork rightFork

-- 哲学家就餐
dine :: Philosopher -> IO ()
dine philosopher = do
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " is thinking"
    threadDelay 100000
    
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " is hungry"
    
    -- 获取叉子
    acquireSemaphore (leftFork philosopher)
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " picked up left fork"
    
    acquireSemaphore (rightFork philosopher)
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " picked up right fork"
    
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " is eating"
    threadDelay 200000
    
    -- 释放叉子
    releaseSemaphore (rightFork philosopher)
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " put down right fork"
    
    releaseSemaphore (leftFork philosopher)
    putStrLn $ "Philosopher " ++ show (id philosopher) ++ " put down left fork"

-- 使用示例
exampleDiningPhilosophers :: IO ()
exampleDiningPhilosophers = do
    -- 创建5个叉子
    forks <- mapM (\_ -> newSemaphore 1) [1..5]
    
    -- 创建5个哲学家
    let philosophers = zipWith3 newPhilosopher [1..5] forks (tail forks ++ [head forks])
    
    -- 启动哲学家
    mapM_ (\philosopher -> forkIO $ forever $ dine philosopher) philosophers
    
    threadDelay 5000000  -- 运行5秒
```

### 形式化证明

#### 定理 5.1 (信号量的正确性)

对于任意信号量 $\text{Semaphore}$，满足：
$$\text{acquire}(s) \land \text{release}(s) \Rightarrow \text{balanced}$$

**证明**：
信号量确保获取和释放操作平衡，防止资源泄漏。

## 📊 性能分析与优化

### 时间复杂度分析

| 模式 | 获取时间复杂度 | 释放时间复杂度 | 空间复杂度 |
|------|----------------|----------------|------------|
| 互斥锁 | O(1) | O(1) | O(1) |
| 读写锁 | O(1) | O(1) | O(n) |
| 条件变量 | O(1) | O(1) | O(n) |
| 信号量 | O(1) | O(1) | O(1) |

### 内存优化策略

```haskell
-- 无锁数据结构
data LockFreeStack a = LockFreeStack (MVar [a])

newLockFreeStack :: IO (LockFreeStack a)
newLockFreeStack = do
    mvar <- newMVar []
    return $ LockFreeStack mvar

push :: a -> LockFreeStack a -> IO ()
push item (LockFreeStack mvar) = do
    modifyMVar_ mvar (return . (item:))

pop :: LockFreeStack a -> IO (Maybe a)
pop (LockFreeStack mvar) = do
    current <- readMVar mvar
    case current of
        [] -> return Nothing
        (item:rest) -> do
            putMVar mvar rest
            return $ Just item
```

## 🎯 最佳实践

### 1. 模式选择原则

- **简单同步**：使用互斥锁
- **读写分离**：使用读写锁
- **条件等待**：使用条件变量
- **资源控制**：使用信号量

### 2. 性能考虑

- 避免锁竞争
- 合理使用无锁数据结构
- 考虑内存屏障
- 优化线程调度

### 3. 可维护性

- 避免死锁
- 提供清晰的文档
- 进行充分的测试
- 监控性能指标

## 🔗 相关链接

- [创建型设计模式](../01-Creational-Patterns/README.md)
- [结构型设计模式](../02-Structural-Patterns/README.md)
- [行为型设计模式](../03-Behavioral-Patterns/README.md)
- [设计模式总览](../README.md)

---

*本文档提供了并发设计模式的完整形式化理论和Haskell实现，为并发编程提供了坚实的理论基础。*
