# 分布式锁模式（Distributed Lock Pattern）

## 概述
分布式锁模式是一种分布式系统设计模式，用于在分布式环境中实现互斥访问，确保同一时间只有一个进程或线程能够访问共享资源。

## 理论基础
- **互斥性**：同一时间只有一个客户端持有锁
- **防死锁**：锁必须能够自动释放
- **容错性**：在节点故障时仍能正常工作

## Rust实现示例
```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::time::sleep;
use uuid::Uuid;

// 锁状态
#[derive(Debug, Clone, PartialEq)]
enum LockState {
    Locked,
    Unlocked,
}

// 分布式锁
struct DistributedLock {
    id: String,
    resource: String,
    owner: Option<String>,
    state: Arc<Mutex<LockState>>,
    created_at: Instant,
    expires_at: Option<Instant>,
}

impl DistributedLock {
    fn new(resource: String, ttl: Option<Duration>) -> Self {
        let expires_at = ttl.map(|duration| Instant::now() + duration);
        Self {
            id: Uuid::new_v4().to_string(),
            resource,
            owner: None,
            state: Arc::new(Mutex::new(LockState::Unlocked)),
            created_at: Instant::now(),
            expires_at,
        }
    }
    
    async fn acquire(&mut self, client_id: String, timeout: Duration) -> Result<bool, String> {
        let start_time = Instant::now();
        
        while start_time.elapsed() < timeout {
            let mut state = self.state.lock().unwrap();
            
            match *state {
                LockState::Unlocked => {
                    // 检查是否过期
                    if let Some(expires_at) = self.expires_at {
                        if Instant::now() > expires_at {
                            return Err("锁已过期".to_string());
                        }
                    }
                    
                    *state = LockState::Locked;
                    self.owner = Some(client_id.clone());
                    println!("客户端 {} 获得锁 {}", client_id, self.resource);
                    return Ok(true);
                }
                LockState::Locked => {
                    // 检查是否是锁的拥有者
                    if let Some(ref owner) = self.owner {
                        if owner == &client_id {
                            return Ok(true);
                        }
                    }
                }
            }
            
            drop(state);
            sleep(Duration::from_millis(10)).await;
        }
        
        Err("获取锁超时".to_string())
    }
    
    async fn release(&mut self, client_id: String) -> Result<bool, String> {
        let mut state = self.state.lock().unwrap();
        
        match *state {
            LockState::Locked => {
                if let Some(ref owner) = self.owner {
                    if owner == &client_id {
                        *state = LockState::Unlocked;
                        self.owner = None;
                        println!("客户端 {} 释放锁 {}", client_id, self.resource);
                        return Ok(true);
                    } else {
                        return Err("不是锁的拥有者".to_string());
                    }
                }
                Err("锁状态异常".to_string())
            }
            LockState::Unlocked => Ok(false),
        }
    }
    
    fn is_expired(&self) -> bool {
        if let Some(expires_at) = self.expires_at {
            Instant::now() > expires_at
        } else {
            false
        }
    }
    
    fn get_owner(&self) -> Option<String> {
        self.owner.clone()
    }
}

// 基于Redis的分布式锁
struct RedisDistributedLock {
    redis_client: Arc<Mutex<HashMap<String, String>>>,
    lock_prefix: String,
}

impl RedisDistributedLock {
    fn new() -> Self {
        Self {
            redis_client: Arc::new(Mutex::new(HashMap::new())),
            lock_prefix: "lock:".to_string(),
        }
    }
    
    async fn acquire(&self, resource: String, client_id: String, ttl: Duration) -> Result<bool, String> {
        let lock_key = format!("{}{}", self.lock_prefix, resource);
        let mut redis = self.redis_client.lock().unwrap();
        
        // 检查锁是否存在
        if let Some(existing_client) = redis.get(&lock_key) {
            if existing_client == &client_id {
                return Ok(true); // 已经是锁的拥有者
            }
            return Ok(false); // 锁被其他客户端持有
        }
        
        // 尝试获取锁
        redis.insert(lock_key, client_id);
        Ok(true)
    }
    
    async fn release(&self, resource: String, client_id: String) -> Result<bool, String> {
        let lock_key = format!("{}{}", self.lock_prefix, resource);
        let mut redis = self.redis_client.lock().unwrap();
        
        if let Some(existing_client) = redis.get(&lock_key) {
            if existing_client == &client_id {
                redis.remove(&lock_key);
                return Ok(true);
            } else {
                return Err("不是锁的拥有者".to_string());
            }
        }
        
        Ok(false)
    }
}

// 基于ZooKeeper的分布式锁
struct ZookeeperDistributedLock {
    zk_client: Arc<Mutex<HashMap<String, Vec<String>>>>,
    lock_prefix: String,
}

impl ZookeeperDistributedLock {
    fn new() -> Self {
        Self {
            zk_client: Arc::new(Mutex::new(HashMap::new())),
            lock_prefix: "/locks/".to_string(),
        }
    }
    
    async fn acquire(&self, resource: String, client_id: String) -> Result<bool, String> {
        let lock_path = format!("{}{}", self.lock_prefix, resource);
        let mut zk = self.zk_client.lock().unwrap();
        
        // 检查是否已存在锁
        if let Some(children) = zk.get(&lock_path) {
            if children.is_empty() {
                // 创建锁节点
                let lock_node = format!("{}/{}", lock_path, client_id);
                children.push(lock_node);
                return Ok(true);
            } else {
                // 检查是否是锁的拥有者
                let lock_node = format!("{}/{}", lock_path, client_id);
                if children.contains(&lock_node) {
                    return Ok(true);
                }
                return Ok(false);
            }
        } else {
            // 创建锁路径
            zk.insert(lock_path.clone(), vec![format!("{}/{}", lock_path, client_id)]);
            return Ok(true);
        }
    }
    
    async fn release(&self, resource: String, client_id: String) -> Result<bool, String> {
        let lock_path = format!("{}{}", self.lock_prefix, resource);
        let mut zk = self.zk_client.lock().unwrap();
        
        if let Some(children) = zk.get_mut(&lock_path) {
            let lock_node = format!("{}/{}", lock_path, client_id);
            if let Some(pos) = children.iter().position(|node| node == &lock_node) {
                children.remove(pos);
                return Ok(true);
            }
        }
        
        Ok(false)
    }
}

// 基于数据库的分布式锁
struct DatabaseDistributedLock {
    db_client: Arc<Mutex<HashMap<String, LockRecord>>>,
}

#[derive(Debug, Clone)]
struct LockRecord {
    resource: String,
    client_id: String,
    acquired_at: Instant,
    expires_at: Option<Instant>,
}

impl DatabaseDistributedLock {
    fn new() -> Self {
        Self {
            db_client: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn acquire(&self, resource: String, client_id: String, ttl: Duration) -> Result<bool, String> {
        let mut db = self.db_client.lock().unwrap();
        
        if let Some(record) = db.get(&resource) {
            // 检查是否过期
            if let Some(expires_at) = record.expires_at {
                if Instant::now() > expires_at {
                    // 锁已过期，可以重新获取
                    let new_record = LockRecord {
                        resource: resource.clone(),
                        client_id: client_id.clone(),
                        acquired_at: Instant::now(),
                        expires_at: Some(Instant::now() + ttl),
                    };
                    db.insert(resource, new_record);
                    return Ok(true);
                }
                
                // 检查是否是锁的拥有者
                if record.client_id == client_id {
                    return Ok(true);
                }
                
                return Ok(false);
            }
        }
        
        // 创建新锁
        let record = LockRecord {
            resource: resource.clone(),
            client_id: client_id.clone(),
            acquired_at: Instant::now(),
            expires_at: Some(Instant::now() + ttl),
        };
        db.insert(resource, record);
        Ok(true)
    }
    
    async fn release(&self, resource: String, client_id: String) -> Result<bool, String> {
        let mut db = self.db_client.lock().unwrap();
        
        if let Some(record) = db.get(&resource) {
            if record.client_id == client_id {
                db.remove(&resource);
                return Ok(true);
            } else {
                return Err("不是锁的拥有者".to_string());
            }
        }
        
        Ok(false)
    }
}

// 锁管理器
struct LockManager {
    locks: Arc<Mutex<HashMap<String, Arc<Mutex<DistributedLock>>>>>,
    redis_lock: Arc<RedisDistributedLock>,
    zk_lock: Arc<ZookeeperDistributedLock>,
    db_lock: Arc<DatabaseDistributedLock>,
}

impl LockManager {
    fn new() -> Self {
        Self {
            locks: Arc::new(Mutex::new(HashMap::new())),
            redis_lock: Arc::new(RedisDistributedLock::new()),
            zk_lock: Arc::new(ZookeeperDistributedLock::new()),
            db_lock: Arc::new(DatabaseDistributedLock::new()),
        }
    }
    
    async fn acquire_lock(&self, resource: String, client_id: String, lock_type: LockType) -> Result<bool, String> {
        match lock_type {
            LockType::Memory => {
                let mut locks = self.locks.lock().unwrap();
                let lock = locks.entry(resource.clone()).or_insert_with(|| {
                    Arc::new(Mutex::new(DistributedLock::new(resource.clone(), Some(Duration::from_secs(30))))
                });
                
                let mut lock_guard = lock.lock().unwrap();
                lock_guard.acquire(client_id, Duration::from_secs(5)).await
            }
            LockType::Redis => {
                self.redis_lock.acquire(resource, client_id, Duration::from_secs(30)).await
            }
            LockType::Zookeeper => {
                self.zk_lock.acquire(resource, client_id).await
            }
            LockType::Database => {
                self.db_lock.acquire(resource, client_id, Duration::from_secs(30)).await
            }
        }
    }
    
    async fn release_lock(&self, resource: String, client_id: String, lock_type: LockType) -> Result<bool, String> {
        match lock_type {
            LockType::Memory => {
                let locks = self.locks.lock().unwrap();
                if let Some(lock) = locks.get(&resource) {
                    let mut lock_guard = lock.lock().unwrap();
                    lock_guard.release(client_id).await
                } else {
                    Ok(false)
                }
            }
            LockType::Redis => {
                self.redis_lock.release(resource, client_id).await
            }
            LockType::Zookeeper => {
                self.zk_lock.release(resource, client_id).await
            }
            LockType::Database => {
                self.db_lock.release(resource, client_id).await
            }
        }
    }
}

#[derive(Debug, Clone)]
enum LockType {
    Memory,
    Redis,
    Zookeeper,
    Database,
}

#[tokio::main]
async fn main() {
    let lock_manager = Arc::new(LockManager::new());
    
    // 测试内存锁
    println!("=== 内存锁测试 ===");
    let client1 = "client-1".to_string();
    let client2 = "client-2".to_string();
    let resource = "shared-resource".to_string();
    
    // 客户端1获取锁
    match lock_manager.acquire_lock(resource.clone(), client1.clone(), LockType::Memory).await {
        Ok(success) => println!("客户端1获取锁: {}", success),
        Err(error) => println!("客户端1获取锁失败: {}", error),
    }
    
    // 客户端2尝试获取锁
    match lock_manager.acquire_lock(resource.clone(), client2.clone(), LockType::Memory).await {
        Ok(success) => println!("客户端2获取锁: {}", success),
        Err(error) => println!("客户端2获取锁失败: {}", error),
    }
    
    // 客户端1释放锁
    match lock_manager.release_lock(resource.clone(), client1.clone(), LockType::Memory).await {
        Ok(success) => println!("客户端1释放锁: {}", success),
        Err(error) => println!("客户端1释放锁失败: {}", error),
    }
    
    // 客户端2再次尝试获取锁
    match lock_manager.acquire_lock(resource.clone(), client2.clone(), LockType::Memory).await {
        Ok(success) => println!("客户端2获取锁: {}", success),
        Err(error) => println!("客户端2获取锁失败: {}", error),
    }
    
    // 测试Redis锁
    println!("\n=== Redis锁测试 ===");
    match lock_manager.acquire_lock("redis-resource".to_string(), client1.clone(), LockType::Redis).await {
        Ok(success) => println!("Redis锁获取: {}", success),
        Err(error) => println!("Redis锁获取失败: {}", error),
    }
    
    // 测试ZooKeeper锁
    println!("\n=== ZooKeeper锁测试 ===");
    match lock_manager.acquire_lock("zk-resource".to_string(), client1.clone(), LockType::Zookeeper).await {
        Ok(success) => println!("ZooKeeper锁获取: {}", success),
        Err(error) => println!("ZooKeeper锁获取失败: {}", error),
    }
    
    // 测试数据库锁
    println!("\n=== 数据库锁测试 ===");
    match lock_manager.acquire_lock("db-resource".to_string(), client1.clone(), LockType::Database).await {
        Ok(success) => println!("数据库锁获取: {}", success),
        Err(error) => println!("数据库锁获取失败: {}", error),
    }
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Data.IORef
import Data.Map as M
import Data.Time
import System.Random
import Text.Printf

-- 锁状态
data LockState = Locked | Unlocked deriving (Eq, Show)

-- 分布式锁
data DistributedLock = DistributedLock
    { lockId :: String
    , lockResource :: String
    , lockOwner :: Maybe String
    , lockState :: TVar LockState
    , lockCreatedAt :: UTCTime
    , lockExpiresAt :: Maybe UTCTime
    }

newDistributedLock :: String -> Maybe Int -> IO DistributedLock
newDistributedLock resource ttlSeconds = do
    now <- getCurrentTime
    state <- newTVarIO Unlocked
    expiresAt <- case ttlSeconds of
        Just seconds -> do
            let expiresAt = addUTCTime (fromIntegral seconds) now
            return $ Just expiresAt
        Nothing -> return Nothing
    return $ DistributedLock (show $ randomRIO (0, 1000000)) resource Nothing state now expiresAt

isExpired :: DistributedLock -> IO Bool
isExpired lock = do
    now <- getCurrentTime
    case lockExpiresAt lock of
        Just expiresAt -> return $ now > expiresAt
        Nothing -> return False

acquireLock :: DistributedLock -> String -> Int -> IO (Either String Bool)
acquireLock lock clientId timeoutSeconds = do
    startTime <- getCurrentTime
    let timeoutDuration = fromIntegral timeoutSeconds
    
    let loop = do
        currentTime <- getCurrentTime
        if diffUTCTime currentTime startTime > timeoutDuration
            then return $ Left "获取锁超时"
            else do
                expired <- isExpired lock
                if expired
                    then return $ Left "锁已过期"
                    else do
                        atomically $ do
                            state <- readTVar (lockState lock)
                            case state of
                                Unlocked -> do
                                    writeTVar (lockState lock) Locked
                                    return $ Right True
                                Locked -> do
                                    owner <- readIORef (lockOwner lock)
                                    case owner of
                                        Just ownerId -> 
                                            if ownerId == clientId
                                                then return $ Right True
                                                else return $ Right False
                                        Nothing -> return $ Right False
                
                result <- atomically $ do
                    state <- readTVar (lockState lock)
                    case state of
                        Unlocked -> do
                            writeTVar (lockState lock) Locked
                            return $ Right True
                        Locked -> do
                            owner <- readIORef (lockOwner lock)
                            case owner of
                                Just ownerId -> 
                                    if ownerId == clientId
                                        then return $ Right True
                                        else return $ Right False
                                Nothing -> return $ Right False
                
                case result of
                    Right True -> return result
                    Right False -> do
                        threadDelay 10000 -- 10ms
                        loop
                    Left error -> return $ Left error
    
    loop

releaseLock :: DistributedLock -> String -> IO (Either String Bool)
releaseLock lock clientId = do
    atomically $ do
        state <- readTVar (lockState lock)
        case state of
            Locked -> do
                owner <- readIORef (lockOwner lock)
                case owner of
                    Just ownerId -> 
                        if ownerId == clientId
                            then do
                                writeTVar (lockState lock) Unlocked
                                writeIORef (lockOwner lock) Nothing
                                return $ Right True
                            else return $ Left "不是锁的拥有者"
                    Nothing -> return $ Left "锁状态异常"
            Unlocked -> return $ Right False

-- Redis分布式锁
data RedisDistributedLock = RedisDistributedLock
    { redisClient :: TVar (M.Map String String)
    , lockPrefix :: String
    }

newRedisDistributedLock :: IO RedisDistributedLock
newRedisDistributedLock = do
    client <- newTVarIO M.empty
    return $ RedisDistributedLock client "lock:"

acquireRedisLock :: RedisDistributedLock -> String -> String -> Int -> IO (Either String Bool)
acquireRedisLock redisLock resource clientId ttlSeconds = do
    let lockKey = lockPrefix redisLock ++ resource
    atomically $ do
        redis <- readTVar (redisClient redisLock)
        case M.lookup lockKey redis of
            Just existingClient -> 
                if existingClient == clientId
                    then return $ Right True
                    else return $ Right False
            Nothing -> do
                writeTVar (redisClient redisLock) (M.insert lockKey clientId redis)
                return $ Right True

releaseRedisLock :: RedisDistributedLock -> String -> String -> IO (Either String Bool)
releaseRedisLock redisLock resource clientId = do
    let lockKey = lockPrefix redisLock ++ resource
    atomically $ do
        redis <- readTVar (redisClient redisLock)
        case M.lookup lockKey redis of
            Just existingClient -> 
                if existingClient == clientId
                    then do
                        writeTVar (redisClient redisLock) (M.delete lockKey redis)
                        return $ Right True
                    else return $ Left "不是锁的拥有者"
            Nothing -> return $ Right False

-- ZooKeeper分布式锁
data ZookeeperDistributedLock = ZookeeperDistributedLock
    { zkClient :: TVar (M.Map String [String])
    , zkLockPrefix :: String
    }

newZookeeperDistributedLock :: IO ZookeeperDistributedLock
newZookeeperDistributedLock = do
    client <- newTVarIO M.empty
    return $ ZookeeperDistributedLock client "/locks/"

acquireZookeeperLock :: ZookeeperDistributedLock -> String -> String -> IO (Either String Bool)
acquireZookeeperLock zkLock resource clientId = do
    let lockPath = zkLockPrefix zkLock ++ resource
    atomically $ do
        zk <- readTVar (zkClient zkLock)
        case M.lookup lockPath zk of
            Just children -> 
                if null children
                    then do
                        let lockNode = lockPath ++ "/" ++ clientId
                        writeTVar (zkClient zkLock) (M.insert lockPath (lockNode : children) zk)
                        return $ Right True
                    else do
                        let lockNode = lockPath ++ "/" ++ clientId
                        if lockNode `elem` children
                            then return $ Right True
                            else return $ Right False
            Nothing -> do
                let lockNode = lockPath ++ "/" ++ clientId
                writeTVar (zkClient zkLock) (M.insert lockPath [lockNode] zk)
                return $ Right True

releaseZookeeperLock :: ZookeeperDistributedLock -> String -> String -> IO (Either String Bool)
releaseZookeeperLock zkLock resource clientId = do
    let lockPath = zkLockPrefix zkLock ++ resource
    atomically $ do
        zk <- readTVar (zkClient zkLock)
        case M.lookup lockPath zk of
            Just children -> do
                let lockNode = lockPath ++ "/" ++ clientId
                let newChildren = filter (/= lockNode) children
                writeTVar (zkClient zkLock) (M.insert lockPath newChildren zk)
                return $ Right True
            Nothing -> return $ Right False

-- 锁管理器
data LockManager = LockManager
    { locks :: TVar (M.Map String DistributedLock)
    , redisLock :: RedisDistributedLock
    , zkLock :: ZookeeperDistributedLock
    }

newLockManager :: IO LockManager
newLockManager = do
    locks <- newTVarIO M.empty
    redisLock <- newRedisDistributedLock
    zkLock <- newZookeeperDistributedLock
    return $ LockManager locks redisLock zkLock

data LockType = Memory | Redis | Zookeeper deriving (Show)

acquireLockManager :: LockManager -> String -> String -> LockType -> Int -> IO (Either String Bool)
acquireLockManager manager resource clientId lockType ttlSeconds = do
    case lockType of
        Memory -> do
            atomically $ do
                locks <- readTVar (locks manager)
                case M.lookup resource locks of
                    Just lock -> do
                        result <- liftIO $ acquireLock lock clientId 5
                        return result
                    Nothing -> do
                        lock <- liftIO $ newDistributedLock resource (Just ttlSeconds)
                        writeTVar (locks manager) (M.insert resource lock locks)
                        liftIO $ acquireLock lock clientId 5
        Redis -> acquireRedisLock (redisLock manager) resource clientId ttlSeconds
        Zookeeper -> acquireZookeeperLock (zkLock manager) resource clientId

releaseLockManager :: LockManager -> String -> String -> LockType -> IO (Either String Bool)
releaseLockManager manager resource clientId lockType = do
    case lockType of
        Memory -> do
            atomically $ do
                locks <- readTVar (locks manager)
                case M.lookup resource locks of
                    Just lock -> liftIO $ releaseLock lock clientId
                    Nothing -> return $ Right False
        Redis -> releaseRedisLock (redisLock manager) resource clientId
        Zookeeper -> releaseZookeeperLock (zkLock manager) resource clientId

-- 测试函数
testDistributedLock :: IO ()
testDistributedLock = do
    putStrLn "=== 分布式锁测试 ==="
    
    manager <- newLockManager
    let client1 = "client-1"
    let client2 = "client-2"
    let resource = "shared-resource"
    
    -- 客户端1获取锁
    result1 <- acquireLockManager manager resource client1 Memory 30
    case result1 of
        Right success -> putStrLn $ "客户端1获取锁: " ++ show success
        Left error -> putStrLn $ "客户端1获取锁失败: " ++ error
    
    -- 客户端2尝试获取锁
    result2 <- acquireLockManager manager resource client2 Memory 30
    case result2 of
        Right success -> putStrLn $ "客户端2获取锁: " ++ show success
        Left error -> putStrLn $ "客户端2获取锁失败: " ++ error
    
    -- 客户端1释放锁
    result3 <- releaseLockManager manager resource client1 Memory
    case result3 of
        Right success -> putStrLn $ "客户端1释放锁: " ++ show success
        Left error -> putStrLn $ "客户端1释放锁失败: " ++ error
    
    -- 客户端2再次尝试获取锁
    result4 <- acquireLockManager manager resource client2 Memory 30
    case result4 of
        Right success -> putStrLn $ "客户端2获取锁: " ++ show success
        Left error -> putStrLn $ "客户端2获取锁失败: " ++ error

testRedisLock :: IO ()
testRedisLock = do
    putStrLn "\n=== Redis锁测试 ==="
    
    manager <- newLockManager
    let client1 = "client-1"
    let resource = "redis-resource"
    
    result <- acquireLockManager manager resource client1 Redis 30
    case result of
        Right success -> putStrLn $ "Redis锁获取: " ++ show success
        Left error -> putStrLn $ "Redis锁获取失败: " ++ error

testZookeeperLock :: IO ()
testZookeeperLock = do
    putStrLn "\n=== ZooKeeper锁测试 ==="
    
    manager <- newLockManager
    let client1 = "client-1"
    let resource = "zk-resource"
    
    result <- acquireLockManager manager resource client1 Zookeeper 30
    case result of
        Right success -> putStrLn $ "ZooKeeper锁获取: " ++ show success
        Left error -> putStrLn $ "ZooKeeper锁获取失败: " ++ error

main :: IO ()
main = do
    testDistributedLock
    testRedisLock
    testZookeeperLock
```

## Lean实现思路
```lean
-- 锁状态
inductive LockState where
  | Locked
  | Unlocked

-- 分布式锁
structure DistributedLock where
  lockId : String
  lockResource : String
  lockOwner : Option String
  lockState : LockState
  lockCreatedAt : Nat -- 简化时间表示
  lockExpiresAt : Option Nat

def newDistributedLock (resource : String) (ttlSeconds : Option Nat) : DistributedLock :=
  { lockId := "lock-" ++ toString (hash resource)
  , lockResource := resource
  , lockOwner := none
  , lockState := LockState.Unlocked
  , lockCreatedAt := 0 -- 简化实现
  , lockExpiresAt := ttlSeconds
  }

def isExpired (lock : DistributedLock) (currentTime : Nat) : Bool :=
  match lock.lockExpiresAt with
  | some expiresAt => currentTime > expiresAt
  | none => false

def acquireLock (lock : DistributedLock) (clientId : String) (currentTime : Nat) : Sum String (DistributedLock × Bool) :=
  if isExpired lock currentTime
    then Sum.inl "锁已过期"
    else
      match lock.lockState with
      | LockState.Unlocked => 
          let updatedLock := { lock with 
              lockState := LockState.Locked
            , lockOwner := some clientId
            }
          Sum.inr (updatedLock, true)
      | LockState.Locked => 
          match lock.lockOwner with
          | some ownerId => 
              if ownerId = clientId
                then Sum.inr (lock, true)
                else Sum.inr (lock, false)
          | none => Sum.inr (lock, false)

def releaseLock (lock : DistributedLock) (clientId : String) : Sum String (DistributedLock × Bool) :=
  match lock.lockState with
  | LockState.Locked => 
      match lock.lockOwner with
      | some ownerId => 
          if ownerId = clientId
            then 
              let updatedLock := { lock with 
                  lockState := LockState.Unlocked
                , lockOwner := none
                }
              Sum.inr (updatedLock, true)
            else Sum.inl "不是锁的拥有者"
      | none => Sum.inl "锁状态异常"
  | LockState.Unlocked => Sum.inr (lock, false)

-- Redis分布式锁
structure RedisDistributedLock where
  redisClient : Map String String
  lockPrefix : String

def newRedisDistributedLock : RedisDistributedLock :=
  { redisClient := Map.empty
  , lockPrefix := "lock:"
  }

def acquireRedisLock (redisLock : RedisDistributedLock) (resource : String) (clientId : String) : Sum String (RedisDistributedLock × Bool) :=
  let lockKey := redisLock.lockPrefix ++ resource
  match redisLock.redisClient.find? lockKey with
  | some existingClient => 
      if existingClient = clientId
        then Sum.inr (redisLock, true)
        else Sum.inr (redisLock, false)
  | none => 
      let updatedClient := redisLock.redisClient.insert lockKey clientId
      let updatedLock := { redisLock with redisClient := updatedClient }
      Sum.inr (updatedLock, true)

def releaseRedisLock (redisLock : RedisDistributedLock) (resource : String) (clientId : String) : Sum String (RedisDistributedLock × Bool) :=
  let lockKey := redisLock.lockPrefix ++ resource
  match redisLock.redisClient.find? lockKey with
  | some existingClient => 
      if existingClient = clientId
        then 
          let updatedClient := redisLock.redisClient.erase lockKey
          let updatedLock := { redisLock with redisClient := updatedClient }
          Sum.inr (updatedLock, true)
        else Sum.inl "不是锁的拥有者"
  | none => Sum.inr (redisLock, false)

-- ZooKeeper分布式锁
structure ZookeeperDistributedLock where
  zkClient : Map String (List String)
  zkLockPrefix : String

def newZookeeperDistributedLock : ZookeeperDistributedLock :=
  { zkClient := Map.empty
  , zkLockPrefix := "/locks/"
  }

def acquireZookeeperLock (zkLock : ZookeeperDistributedLock) (resource : String) (clientId : String) : Sum String (ZookeeperDistributedLock × Bool) :=
  let lockPath := zkLock.zkLockPrefix ++ resource
  match zkLock.zkClient.find? lockPath with
  | some children => 
      if children.isEmpty
        then 
          let lockNode := lockPath ++ "/" ++ clientId
          let updatedChildren := lockNode :: children
          let updatedClient := zkLock.zkClient.insert lockPath updatedChildren
          let updatedLock := { zkLock with zkClient := updatedClient }
          Sum.inr (updatedLock, true)
        else 
          let lockNode := lockPath ++ "/" ++ clientId
          if children.contains lockNode
            then Sum.inr (zkLock, true)
            else Sum.inr (zkLock, false)
  | none => 
      let lockNode := lockPath ++ "/" ++ clientId
      let updatedClient := zkLock.zkClient.insert lockPath [lockNode]
      let updatedLock := { zkLock with zkClient := updatedClient }
      Sum.inr (updatedLock, true)

def releaseZookeeperLock (zkLock : ZookeeperDistributedLock) (resource : String) (clientId : String) : Sum String (ZookeeperDistributedLock × Bool) :=
  let lockPath := zkLock.zkLockPrefix ++ resource
  match zkLock.zkClient.find? lockPath with
  | some children => 
      let lockNode := lockPath ++ "/" ++ clientId
      let updatedChildren := children.filter fun child => child != lockNode
      let updatedClient := zkLock.zkClient.insert lockPath updatedChildren
      let updatedLock := { zkLock with zkClient := updatedClient }
      Sum.inr (updatedLock, true)
  | none => Sum.inr (zkLock, false)

-- 锁管理器
structure LockManager where
  locks : Map String DistributedLock
  redisLock : RedisDistributedLock
  zkLock : ZookeeperDistributedLock

def newLockManager : LockManager :=
  { locks := Map.empty
  , redisLock := newRedisDistributedLock
  , zkLock := newZookeeperDistributedLock
  }

inductive LockType where
  | Memory
  | Redis
  | Zookeeper

def acquireLockManager (manager : LockManager) (resource : String) (clientId : String) (lockType : LockType) : Sum String (LockManager × Bool) :=
  match lockType with
  | LockType.Memory => 
      match manager.locks.find? resource with
      | some lock => 
          match acquireLock lock clientId 0 with
          | Sum.inl error => Sum.inl error
          | Sum.inr (updatedLock, success) => 
              let updatedLocks := manager.locks.insert resource updatedLock
              let updatedManager := { manager with locks := updatedLocks }
              Sum.inr (updatedManager, success)
      | none => 
          let newLock := newDistributedLock resource (some 30)
          match acquireLock newLock clientId 0 with
          | Sum.inl error => Sum.inl error
          | Sum.inr (updatedLock, success) => 
              let updatedLocks := manager.locks.insert resource updatedLock
              let updatedManager := { manager with locks := updatedLocks }
              Sum.inr (updatedManager, success)
  | LockType.Redis => 
      match acquireRedisLock manager.redisLock resource clientId with
      | Sum.inl error => Sum.inl error
      | Sum.inr (updatedRedisLock, success) => 
          let updatedManager := { manager with redisLock := updatedRedisLock }
          Sum.inr (updatedManager, success)
  | LockType.Zookeeper => 
      match acquireZookeeperLock manager.zkLock resource clientId with
      | Sum.inl error => Sum.inl error
      | Sum.inr (updatedZkLock, success) => 
          let updatedManager := { manager with zkLock := updatedZkLock }
          Sum.inr (updatedManager, success)
```

## 应用场景
- 分布式资源管理
- 数据库连接池
- 分布式任务调度
- 分布式计数器

## 最佳实践
- 设置合理的超时时间
- 实现锁的自动续期
- 避免死锁
- 监控锁的使用情况