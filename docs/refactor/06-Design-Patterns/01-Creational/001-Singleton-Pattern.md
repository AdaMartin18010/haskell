# 单例模式 (Singleton Pattern)

## 概述

单例模式确保一个类只有一个实例，并提供一个全局访问点。它是最简单的设计模式之一，但实现线程安全的单例需要考虑并发问题。

## 核心概念

### 1. 基本特征

- **唯一性**: 确保类只有一个实例
- **全局访问**: 提供全局访问点
- **延迟初始化**: 首次访问时创建实例
- **线程安全**: 在多线程环境下保证唯一性

### 2. 实现方式

- **饿汉式**: 类加载时创建实例
- **懒汉式**: 首次访问时创建实例
- **双重检查锁定**: 线程安全的懒汉式
- **静态内部类**: 延迟加载的线程安全实现

## 理论基础

### 1. 基本单例实现

```rust
use std::sync::{Arc, Mutex, Once};
use std::sync::atomic::{AtomicBool, Ordering};

// 饿汉式单例
struct EagerSingleton {
    data: String,
}

impl EagerSingleton {
    // 静态实例，在编译时初始化
    static INSTANCE: EagerSingleton = EagerSingleton {
        data: String::from("Eager Singleton"),
    };
    
    fn get_instance() -> &'static Self {
        &Self::INSTANCE
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 懒汉式单例（非线程安全）
struct LazySingleton {
    data: String,
}

impl LazySingleton {
    fn new() -> Self {
        Self {
            data: String::from("Lazy Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 线程安全的懒汉式单例
struct ThreadSafeSingleton {
    data: String,
}

impl ThreadSafeSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Thread Safe Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 使用Mutex的线程安全单例
struct MutexSingleton {
    data: String,
}

impl MutexSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Mutex Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

// 全局单例实例
static mut SINGLETON: Option<MutexSingleton> = None;
static INIT: Once = Once::new();

fn get_mutex_singleton() -> &'static MutexSingleton {
    unsafe {
        INIT.call_once(|| {
            SINGLETON = Some(MutexSingleton::new());
        });
        SINGLETON.as_ref().unwrap()
    }
}

// 使用Arc<Mutex>的线程安全单例
struct ArcMutexSingleton {
    data: String,
}

impl ArcMutexSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Arc Mutex Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

lazy_static::lazy_static! {
    static ref ARC_MUTEX_SINGLETON: Arc<Mutex<ArcMutexSingleton>> = 
        Arc::new(Mutex::new(ArcMutexSingleton::new()));
}

fn get_arc_mutex_singleton() -> Arc<Mutex<ArcMutexSingleton>> {
    Arc::clone(&ARC_MUTEX_SINGLETON)
}

// 双重检查锁定单例
struct DoubleCheckSingleton {
    data: String,
}

impl DoubleCheckSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Double Check Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static mut DOUBLE_CHECK_SINGLETON: Option<DoubleCheckSingleton> = None;
static DOUBLE_CHECK_INIT: Once = Once::new();

fn get_double_check_singleton() -> &'static DoubleCheckSingleton {
    unsafe {
        DOUBLE_CHECK_INIT.call_once(|| {
            DOUBLE_CHECK_SINGLETON = Some(DoubleCheckSingleton::new());
        });
        DOUBLE_CHECK_SINGLETON.as_ref().unwrap()
    }
}

// 原子布尔标志的单例
struct AtomicSingleton {
    data: String,
}

impl AtomicSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Atomic Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static mut ATOMIC_SINGLETON: Option<AtomicSingleton> = None;
static ATOMIC_INITIALIZED: AtomicBool = AtomicBool::new(false);

fn get_atomic_singleton() -> &'static AtomicSingleton {
    if !ATOMIC_INITIALIZED.load(Ordering::Acquire) {
        unsafe {
            if !ATOMIC_INITIALIZED.load(Ordering::Acquire) {
                ATOMIC_SINGLETON = Some(AtomicSingleton::new());
                ATOMIC_INITIALIZED.store(true, Ordering::Release);
            }
        }
    }
    unsafe { ATOMIC_SINGLETON.as_ref().unwrap() }
}
```

### 2. 高级单例实现

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 无锁单例实现
struct LockFreeSingleton {
    data: String,
}

impl LockFreeSingleton {
    fn new() -> Self {
        Self {
            data: String::from("Lock Free Singleton"),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static LOCK_FREE_SINGLETON: AtomicPtr<LockFreeSingleton> = AtomicPtr::new(ptr::null_mut());

fn get_lock_free_singleton() -> &'static LockFreeSingleton {
    let ptr = LOCK_FREE_SINGLETON.load(Ordering::Acquire);
    if !ptr.is_null() {
        unsafe { &*ptr }
    } else {
        let new_singleton = Box::new(LockFreeSingleton::new());
        let new_ptr = Box::into_raw(new_singleton);
        
        match LOCK_FREE_SINGLETON.compare_exchange(
            ptr::null_mut(),
            new_ptr,
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            Ok(_) => unsafe { &*new_ptr },
            Err(actual_ptr) => {
                // 另一个线程已经初始化了
                unsafe {
                    let _ = Box::from_raw(new_ptr);
                    &*actual_ptr
                }
            }
        }
    }
}

// 泛型单例
struct GenericSingleton<T> {
    data: T,
}

impl<T> GenericSingleton<T> {
    fn new(data: T) -> Self {
        Self { data }
    }
    
    fn get_data(&self) -> &T {
        &self.data
    }
}

// 配置单例
struct ConfigSingleton {
    database_url: String,
    api_key: String,
    timeout: u64,
}

impl ConfigSingleton {
    fn new() -> Self {
        Self {
            database_url: String::from("postgresql://localhost:5432/mydb"),
            api_key: String::from("secret_key"),
            timeout: 30,
        }
    }
    
    fn get_database_url(&self) -> &str {
        &self.database_url
    }
    
    fn get_api_key(&self) -> &str {
        &self.api_key
    }
    
    fn get_timeout(&self) -> u64 {
        self.timeout
    }
    
    fn update_timeout(&mut self, timeout: u64) {
        self.timeout = timeout;
    }
}

// 线程安全的配置单例
lazy_static::lazy_static! {
    static ref CONFIG_SINGLETON: Arc<Mutex<ConfigSingleton>> = 
        Arc::new(Mutex::new(ConfigSingleton::new()));
}

fn get_config_singleton() -> Arc<Mutex<ConfigSingleton>> {
    Arc::clone(&CONFIG_SINGLETON)
}

// 连接池单例
struct ConnectionPool {
    connections: Vec<String>,
    max_connections: usize,
}

impl ConnectionPool {
    fn new(max_connections: usize) -> Self {
        let mut connections = Vec::new();
        for i in 0..max_connections {
            connections.push(format!("connection_{}", i));
        }
        
        Self {
            connections,
            max_connections,
        }
    }
    
    fn get_connection(&mut self) -> Option<String> {
        self.connections.pop()
    }
    
    fn return_connection(&mut self, connection: String) {
        if self.connections.len() < self.max_connections {
            self.connections.push(connection);
        }
    }
    
    fn available_connections(&self) -> usize {
        self.connections.len()
    }
}

lazy_static::lazy_static! {
    static ref CONNECTION_POOL: Arc<Mutex<ConnectionPool>> = 
        Arc::new(Mutex::new(ConnectionPool::new(10)));
}

fn get_connection_pool() -> Arc<Mutex<ConnectionPool>> {
    Arc::clone(&CONNECTION_POOL)
}
```

## Haskell实现示例

```haskell
import Control.Concurrent.MVar
import Control.Monad.IO.Class
import Data.IORef
import System.IO.Unsafe

-- 基本单例
data Singleton = Singleton
    { singletonData :: String
    }

-- 全局单例实例
singletonInstance :: Singleton
singletonInstance = Singleton "Haskell Singleton"

getSingleton :: Singleton
getSingleton = singletonInstance

-- 使用IORef的线程安全单例
newtype ThreadSafeSingleton = ThreadSafeSingleton
    { tsData :: String
    }

-- 全局IORef
{-# NOINLINE singletonRef #-}
singletonRef :: IORef (Maybe ThreadSafeSingleton)
singletonRef = unsafePerformIO $ newIORef Nothing

getThreadSafeSingleton :: IO ThreadSafeSingleton
getThreadSafeSingleton = do
    maybeSingleton <- readIORef singletonRef
    case maybeSingleton of
        Just singleton -> return singleton
        Nothing -> do
            let newSingleton = ThreadSafeSingleton "Thread Safe Singleton"
            writeIORef singletonRef (Just newSingleton)
            return newSingleton

-- 使用MVar的线程安全单例
newtype MVarSingleton = MVarSingleton
    { mvData :: String
    }

-- 全局MVar
{-# NOINLINE singletonMVar #-}
singletonMVar :: MVar MVarSingleton
singletonMVar = unsafePerformIO $ newEmptyMVar

getMVarSingleton :: IO MVarSingleton
getMVarSingleton = do
    maybeSingleton <- tryReadMVar singletonMVar
    case maybeSingleton of
        Just singleton -> return singleton
        Nothing -> do
            let newSingleton = MVarSingleton "MVar Singleton"
            tryPutMVar singletonMVar newSingleton
            return newSingleton

-- 配置单例
data Config = Config
    { databaseUrl :: String
    , apiKey :: String
    , timeout :: Int
    }

configInstance :: Config
configInstance = Config
    { databaseUrl = "postgresql://localhost:5432/mydb"
    , apiKey = "secret_key"
    , timeout = 30
    }

getConfig :: Config
getConfig = configInstance

-- 连接池单例
data ConnectionPool = ConnectionPool
    { connections :: [String]
    , maxConnections :: Int
    }

connectionPoolInstance :: ConnectionPool
connectionPoolInstance = ConnectionPool
    { connections = map (\i -> "connection_" ++ show i) [0..9]
    , maxConnections = 10
    }

getConnectionPool :: ConnectionPool
getConnectionPool = connectionPoolInstance

-- 线程安全的连接池
newtype ThreadSafeConnectionPool = ThreadSafeConnectionPool
    { tsConnections :: MVar [String]
    }

{-# NOINLINE connectionPoolMVar #-}
connectionPoolMVar :: MVar ThreadSafeConnectionPool
connectionPoolMVar = unsafePerformIO $ do
    connections <- newMVar (map (\i -> "connection_" ++ show i) [0..9])
    newMVar (ThreadSafeConnectionPool connections)

getThreadSafeConnectionPool :: IO ThreadSafeConnectionPool
getThreadSafeConnectionPool = readMVar connectionPoolMVar

getConnection :: ThreadSafeConnectionPool -> IO (Maybe String)
getConnection pool = do
    connections <- takeMVar (tsConnections pool)
    case connections of
        [] -> do
            putMVar (tsConnections pool) []
            return Nothing
        (conn:rest) -> do
            putMVar (tsConnections pool) rest
            return (Just conn)

returnConnection :: ThreadSafeConnectionPool -> String -> IO ()
returnConnection pool connection = do
    connections <- takeMVar (tsConnections pool)
    let maxConnections = 10
    if length connections < maxConnections
        then putMVar (tsConnections pool) (connection : connections)
        else putMVar (tsConnections pool) connections
```

## Lean实现思路

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- 单例类定义
structure Singleton where
  data : String

-- 全局单例实例
def singletonInstance : Singleton :=
  { data := "Lean Singleton" }

def getSingleton : Singleton :=
  singletonInstance

-- 配置单例
structure Config where
  databaseUrl : String
  apiKey : String
  timeout : Nat

def configInstance : Config :=
  { databaseUrl := "postgresql://localhost:5432/mydb"
  , apiKey := "secret_key"
  , timeout := 30
  }

def getConfig : Config :=
  configInstance

-- 连接池单例
structure ConnectionPool where
  connections : List String
  maxConnections : Nat

def connectionPoolInstance : ConnectionPool :=
  { connections := List.range 10 |>.map (fun i => s!"connection_{i}")
  , maxConnections := 10
  }

def getConnectionPool : ConnectionPool :=
  connectionPoolInstance

-- 线程安全单例（概念性实现）
structure ThreadSafeSingleton where
  data : String
  mutex : Bool -- 简化的互斥锁表示

def threadSafeSingletonInstance : ThreadSafeSingleton :=
  { data := "Thread Safe Singleton"
  , mutex := false
  }

def getThreadSafeSingleton : ThreadSafeSingleton :=
  threadSafeSingletonInstance
```

## 应用场景

### 1. 配置管理

- **应用配置**: 全局配置信息
- **数据库连接**: 连接池管理
- **日志系统**: 日志记录器

### 2. 资源管理

- **缓存系统**: 全局缓存实例
- **线程池**: 线程池管理
- **连接池**: 数据库连接池

### 3. 服务管理

- **API客户端**: HTTP客户端实例
- **消息队列**: 消息队列连接
- **文件系统**: 文件系统访问

### 4. 状态管理

- **游戏状态**: 游戏全局状态
- **用户会话**: 用户会话管理
- **系统状态**: 系统运行状态

## 最佳实践

### 1. 线程安全

- 使用原子操作或锁机制
- 避免竞态条件
- 考虑性能影响

### 2. 延迟初始化

- 使用懒加载模式
- 避免不必要的资源消耗
- 处理初始化失败

### 3. 资源管理

- 正确释放资源
- 避免内存泄漏
- 处理异常情况

### 4. 测试策略

- 单元测试单例行为
- 并发测试线程安全
- 性能测试开销

## 性能考虑

### 1. 内存使用

- 单例实例大小
- 内存分配开销
- 垃圾回收影响

### 2. 并发性能

- 锁竞争开销
- 原子操作性能
- 缓存一致性

### 3. 初始化开销

- 延迟初始化成本
- 资源预分配
- 初始化失败处理

## 总结

单例模式是确保类唯一实例的重要设计模式。通过合理选择实现方式，可以平衡线程安全、性能和资源使用，为应用程序提供可靠的全局访问点。
