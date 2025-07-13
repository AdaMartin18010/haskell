# 双重检查锁定模式（Double-Checked Locking Pattern）

## 概述

双重检查锁定模式是一种并发设计模式，用于减少获取锁的开销，通过两次检查来确保线程安全，同时避免不必要的同步开销。

## 理论基础

- **延迟初始化**：只在需要时创建对象
- **双重检查**：先无锁检查，再锁定检查
- **内存屏障**：确保可见性和有序性

## Rust实现示例

```rust
use std::sync::{Arc, Mutex, Once};
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 使用Once实现的双重检查锁定
struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        Self {
            data: "单例数据".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static mut INSTANCE: *const Singleton = ptr::null();
static INIT: Once = Once::new();

fn get_instance() -> &'static Singleton {
    unsafe {
        INIT.call_once(|| {
            let instance = Box::new(Singleton::new());
            INSTANCE = Box::into_raw(instance);
        });
        &*INSTANCE
    }
}

// 使用AtomicPtr实现的双重检查锁定
struct AtomicSingleton {
    data: String,
}

impl AtomicSingleton {
    fn new() -> Self {
        Self {
            data: "原子单例数据".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static ATOMIC_INSTANCE: AtomicPtr<AtomicSingleton> = AtomicPtr::new(ptr::null_mut());

fn get_atomic_instance() -> &'static AtomicSingleton {
    // 第一次检查（无锁）
    let instance = ATOMIC_INSTANCE.load(Ordering::Acquire);
    if !instance.is_null() {
        return unsafe { &*instance };
    }
    
    // 创建新实例
    let new_instance = Box::new(AtomicSingleton::new());
    let new_ptr = Box::into_raw(new_instance);
    
    // 尝试原子地设置实例
    match ATOMIC_INSTANCE.compare_exchange(
        ptr::null_mut(),
        new_ptr,
        Ordering::Acquire,
        Ordering::Relaxed,
    ) {
        Ok(_) => {
            // 成功设置，返回新实例
            unsafe { &*new_ptr }
        }
        Err(existing_ptr) => {
            // 另一个线程已经设置了实例，清理我们的实例
            unsafe {
                let _ = Box::from_raw(new_ptr);
                &*existing_ptr
            }
        }
    }
}

// 使用Mutex实现的双重检查锁定
struct MutexSingleton {
    data: String,
}

impl MutexSingleton {
    fn new() -> Self {
        Self {
            data: "互斥锁单例数据".to_string(),
        }
    }
    
    fn get_data(&self) -> &str {
        &self.data
    }
}

static MUTEX_INSTANCE: Mutex<Option<Arc<MutexSingleton>>> = Mutex::new(None);

fn get_mutex_instance() -> Arc<MutexSingleton> {
    // 第一次检查（无锁）
    if let Some(instance) = MUTEX_INSTANCE.lock().unwrap().as_ref() {
        return instance.clone();
    }
    
    // 锁定并再次检查
    let mut guard = MUTEX_INSTANCE.lock().unwrap();
    if let Some(instance) = guard.as_ref() {
        return instance.clone();
    }
    
    // 创建新实例
    let new_instance = Arc::new(MutexSingleton::new());
    *guard = Some(new_instance.clone());
    new_instance
}

// 测试函数
fn test_singleton() {
    let instance1 = get_instance();
    let instance2 = get_instance();
    println!("Once单例: {}", instance1.get_data());
    assert!(std::ptr::eq(instance1, instance2));
    
    let atomic_instance1 = get_atomic_instance();
    let atomic_instance2 = get_atomic_instance();
    println!("原子单例: {}", atomic_instance1.get_data());
    assert!(std::ptr::eq(atomic_instance1, atomic_instance2));
    
    let mutex_instance1 = get_mutex_instance();
    let mutex_instance2 = get_mutex_instance();
    println!("互斥锁单例: {}", mutex_instance1.get_data());
    assert!(Arc::ptr_eq(&mutex_instance1, &mutex_instance2));
}

fn main() {
    test_singleton();
    println!("所有单例测试通过！");
}
```

## Haskell实现示例

```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

-- 使用IORef实现的双重检查锁定
data Singleton = Singleton { data :: String }

newSingleton :: Singleton
newSingleton = Singleton "单例数据"

getData :: Singleton -> String
getData = data

instanceRef :: IORef (Maybe Singleton)
instanceRef = unsafePerformIO $ newIORef Nothing

getInstance :: IO Singleton
getInstance = do
    maybeInstance <- readIORef instanceRef
    case maybeInstance of
        Just instance -> return instance
        Nothing -> do
            -- 创建新实例
            let newInstance = newSingleton
            writeIORef instanceRef (Just newInstance)
            return newInstance

-- 使用STM实现的双重检查锁定
instanceTVar :: TVar (Maybe Singleton)
instanceTVar = unsafePerformIO $ newTVarIO Nothing

getInstanceSTM :: IO Singleton
getInstanceSTM = do
    maybeInstance <- readTVarIO instanceTVar
    case maybeInstance of
        Just instance -> return instance
        Nothing -> do
            -- 使用STM确保原子性
            atomically $ do
                maybeInstance' <- readTVar instanceTVar
                case maybeInstance' of
                    Just instance -> return instance
                    Nothing -> do
                        let newInstance = newSingleton
                        writeTVar instanceTVar (Just newInstance)
                        return newInstance

-- 使用MVar实现的双重检查锁定
instanceMVar :: MVar (Maybe Singleton)
instanceMVar = unsafePerformIO $ newEmptyMVar

getInstanceMVar :: IO Singleton
getInstanceMVar = do
    maybeInstance <- tryReadMVar instanceMVar
    case maybeInstance of
        Just (Just instance) -> return instance
        _ -> do
            -- 尝试创建新实例
            let newInstance = newSingleton
            tryPutMVar instanceMVar (Just newInstance)
            -- 再次尝试读取
            maybeInstance' <- readMVar instanceMVar
            case maybeInstance' of
                Just instance -> return instance
                Nothing -> error "无法创建单例"

-- 测试函数
testSingleton :: IO ()
testSingleton = do
    instance1 <- getInstance
    instance2 <- getInstance
    putStrLn $ "IORef单例: " ++ getData instance1
    putStrLn $ "实例相等: " ++ show (instance1 == instance2)
    
    stmInstance1 <- getInstanceSTM
    stmInstance2 <- getInstanceSTM
    putStrLn $ "STM单例: " ++ getData stmInstance1
    putStrLn $ "实例相等: " ++ show (stmInstance1 == stmInstance2)
    
    mvarInstance1 <- getInstanceMVar
    mvarInstance2 <- getInstanceMVar
    putStrLn $ "MVar单例: " ++ getData mvarInstance1
    putStrLn $ "实例相等: " ++ show (mvarInstance1 == mvarInstance2)

main :: IO ()
main = do
    testSingleton
    putStrLn "所有单例测试完成！"
```

## Lean实现思路

```lean
-- 单例结构
structure Singleton where
  data : String

def newSingleton : Singleton := { data := "单例数据" }

def getData (singleton : Singleton) : String := singleton.data

-- 使用IO实现的双重检查锁定
def instanceRef : IO (Option Singleton) :=
  pure none

def getInstance : IO Singleton := do
  maybeInstance ← instanceRef
  match maybeInstance with
  | some instance => pure instance
  | none => do
    let newInstance := newSingleton
    -- 这里应该更新instanceRef，但简化处理
    pure newInstance

-- 使用STM实现的双重检查锁定
def instanceTVar : IO (TVar (Option Singleton)) :=
  newTVarIO none

def getInstanceSTM : IO Singleton := do
  tvar ← instanceTVar
  maybeInstance ← readTVarIO tvar
  match maybeInstance with
  | some instance => pure instance
  | none => do
    atomically $ do
      maybeInstance' ← readTVar tvar
      match maybeInstance' with
      | some instance => pure instance
      | none => do
        let newInstance := newSingleton
        writeTVar tvar (some newInstance)
        pure newInstance
```

## 应用场景

- 单例模式实现
- 延迟初始化
- 缓存管理
- 连接池初始化

## 最佳实践

- 确保内存屏障正确
- 避免ABA问题
- 考虑性能开销
- 实现优雅关闭
