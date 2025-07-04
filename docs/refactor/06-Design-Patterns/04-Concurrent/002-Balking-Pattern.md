# 犹豫模式（Balking Pattern）

## 概述
犹豫模式是一种并发设计模式，当对象处于不适当的状态时，立即返回而不执行操作。这种模式用于防止对象在不适当的状态下执行操作。

## 理论基础
- **状态检查**：在执行操作前检查对象状态
- **快速失败**：状态不当时立即返回
- **状态保护**：防止对象在不适当状态下被操作

## Rust实现示例
```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

struct BalkingObject {
    state: Arc<Mutex<ObjectState>>,
}

#[derive(Clone, PartialEq)]
enum ObjectState {
    Ready,
    Busy,
    Closed,
}

impl BalkingObject {
    fn new() -> Self {
        Self {
            state: Arc::new(Mutex::new(ObjectState::Ready)),
        }
    }
    
    fn request(&self) -> Result<String, String> {
        let mut state_guard = self.state.lock().unwrap();
        
        match *state_guard {
            ObjectState::Ready => {
                *state_guard = ObjectState::Busy;
                drop(state_guard); // 释放锁
                
                // 执行操作
                thread::sleep(Duration::from_millis(100));
                println!("请求已处理");
                
                // 恢复状态
                if let Ok(mut state) = self.state.lock() {
                    *state = ObjectState::Ready;
                }
                
                Ok("请求成功".to_string())
            }
            ObjectState::Busy => {
                Err("对象正忙，请求被拒绝".to_string())
            }
            ObjectState::Closed => {
                Err("对象已关闭，无法处理请求".to_string())
            }
        }
    }
    
    fn close(&self) -> Result<(), String> {
        let mut state_guard = self.state.lock().unwrap();
        
        match *state_guard {
            ObjectState::Ready => {
                *state_guard = ObjectState::Closed;
                Ok(())
            }
            ObjectState::Busy => {
                Err("对象正忙，无法关闭".to_string())
            }
            ObjectState::Closed => {
                Err("对象已经关闭".to_string())
            }
        }
    }
    
    fn get_state(&self) -> ObjectState {
        if let Ok(state) = self.state.lock() {
            state.clone()
        } else {
            ObjectState::Closed
        }
    }
}

fn main() {
    let object = Arc::new(BalkingObject::new());
    
    // 创建多个线程同时请求
    let mut handles = vec![];
    
    for i in 0..5 {
        let object_clone = Arc::clone(&object);
        let handle = thread::spawn(move || {
            match object_clone.request() {
                Ok(result) => println!("线程 {}: {}", i, result),
                Err(error) => println!("线程 {}: {}", i, error),
            }
        });
        handles.push(handle);
    }
    
    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 尝试关闭对象
    match object.close() {
        Ok(_) => println!("对象已关闭"),
        Err(error) => println!("关闭失败: {}", error),
    }
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef

data ObjectState = Ready | Busy | Closed deriving (Eq, Show)

data BalkingObject = BalkingObject (TVar ObjectState)

newBalkingObject :: IO BalkingObject
newBalkingObject = do
    state <- newTVarIO Ready
    return $ BalkingObject state

request :: BalkingObject -> IO (Either String String)
request (BalkingObject stateVar) = do
    result <- atomically $ do
        state <- readTVar stateVar
        case state of
            Ready -> do
                writeTVar stateVar Busy
                return $ Right "请求成功"
            Busy -> return $ Left "对象正忙，请求被拒绝"
            Closed -> return $ Left "对象已关闭，无法处理请求"
    
    case result of
        Right _ -> do
            -- 模拟处理时间
            threadDelay 100000
            putStrLn "请求已处理"
            -- 恢复状态
            atomically $ writeTVar stateVar Ready
            return result
        Left _ -> return result

close :: BalkingObject -> IO (Either String ())
close (BalkingObject stateVar) = do
    atomically $ do
        state <- readTVar stateVar
        case state of
            Ready -> do
                writeTVar stateVar Closed
                return $ Right ()
            Busy -> return $ Left "对象正忙，无法关闭"
            Closed -> return $ Left "对象已经关闭"

getState :: BalkingObject -> IO ObjectState
getState (BalkingObject stateVar) = readTVarIO stateVar

worker :: BalkingObject -> Int -> IO ()
worker object id = do
    result <- request object
    case result of
        Right success -> putStrLn $ "线程 " ++ show id ++ ": " ++ success
        Left error -> putStrLn $ "线程 " ++ show id ++ ": " ++ error

main = do
    object <- newBalkingObject
    
    -- 创建多个线程同时请求
    let workers = map (worker object) [1..5]
    mapM_ forkIO workers
    
    -- 等待一段时间
    threadDelay 1000000
    
    -- 尝试关闭对象
    result <- close object
    case result of
        Right _ -> putStrLn "对象已关闭"
        Left error -> putStrLn $ "关闭失败: " ++ error
```

## Lean实现思路
```lean
inductive ObjectState where
  | Ready
  | Busy
  | Closed

structure BalkingObject where
  state : ObjectState

def newBalkingObject : IO BalkingObject :=
  pure { state := ObjectState.Ready }

def request (object : BalkingObject) : IO (Sum String String) :=
  match object.state with
  | ObjectState.Ready => do
      IO.println "请求已处理"
      pure (Sum.inr "请求成功")
  | ObjectState.Busy => 
      pure (Sum.inl "对象正忙，请求被拒绝")
  | ObjectState.Closed => 
      pure (Sum.inl "对象已关闭，无法处理请求")

def close (object : BalkingObject) : IO (Sum String Unit) :=
  match object.state with
  | ObjectState.Ready => 
      pure (Sum.inr ())
  | ObjectState.Busy => 
      pure (Sum.inl "对象正忙，无法关闭")
  | ObjectState.Closed => 
      pure (Sum.inl "对象已经关闭")

def getState (object : BalkingObject) : ObjectState :=
  object.state
```

## 应用场景
- 资源池管理
- 连接池控制
- 服务状态管理
- 缓存状态控制

## 最佳实践
- 明确状态转换规则
- 提供状态查询接口
- 实现优雅关闭
- 记录状态变化日志 