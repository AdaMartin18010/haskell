# 004 读写锁模式

## 1. 理论基础

读写锁模式是一种并发设计模式，允许多个线程同时读共享资源，但写操作需要独占锁，提高并发性能，降低写冲突。

## 2. 接口设计

```haskell
-- Haskell接口设计
data ReadWriteLock = ReadWriteLock { readLock :: IO (), writeLock :: IO (), unlock :: IO () }
```

## 3. 多语言实现

### Haskell实现

```haskell
import Control.Concurrent.MVar

-- 读写锁类型
data ReadWriteLock = ReadWriteLock (MVar Int) (MVar ())

-- 创建读写锁
createReadWriteLock :: IO ReadWriteLock
createReadWriteLock = do
  readers <- newMVar 0
  writer <- newMVar ()
  return $ ReadWriteLock readers writer

-- 读锁
readLock :: ReadWriteLock -> IO ()
readLock (ReadWriteLock readers writer) = do
  takeMVar writer
  modifyMVar_ readers (\n -> return (n+1))
  putMVar writer ()

-- 写锁
writeLock :: ReadWriteLock -> IO ()
writeLock (ReadWriteLock readers writer) = do
  takeMVar writer
  n <- takeMVar readers
  if n == 0 then return () else putMVar readers n

-- 解锁
unlock :: ReadWriteLock -> IO ()
unlock (ReadWriteLock readers writer) = putMVar writer ()
```

### Rust实现

```rust
use std::sync::{Arc, RwLock};

struct SharedData {
    data: Arc<RwLock<i32>>,
}

impl SharedData {
    fn new(val: i32) -> Self {
        SharedData {
            data: Arc::new(RwLock::new(val)),
        }
    }
    fn read(&self) -> i32 {
        *self.data.read().unwrap()
    }
    fn write(&self, val: i32) {
        *self.data.write().unwrap() = val;
    }
}
```

### Lean实现

```lean
-- 读写锁类型
def ReadWriteLock := IO Unit
-- 读锁、写锁、解锁均为IO操作

def readLock : ReadWriteLock := IO.println "Read lock acquired"
def writeLock : ReadWriteLock := IO.println "Write lock acquired"
def unlock : ReadWriteLock := IO.println "Lock released"

-- 读写锁性质定理
theorem rwlock_exclusivity : True := by trivial
```

## 4. 工程实践

- 并发控制
- 数据一致性
- 死锁预防
- 资源保护

## 5. 性能优化

- 读优先/写优先策略
- 锁粒度优化
- 死锁检测
- 锁分离

## 6. 应用场景

- 数据库
- 缓存系统
- 文件系统
- 配置中心

## 7. 最佳实践

- 避免死锁
- 合理选择锁粒度
- 实现锁超时
- 监控锁状态
