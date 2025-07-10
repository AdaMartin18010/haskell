# 007 代理模式 (Proxy Pattern)

## 1. 理论基础

### 1.1 模式定义
代理模式是一种结构型设计模式，为其他对象提供一种代理以控制对这个对象的访问。代理模式在访问对象时引入一定程度的间接性，根据不同的目的，代理模式有多种变体。

### 1.2 核心概念
- **Subject（抽象主题）**: 定义真实主题和代理主题的共同接口
- **RealSubject（真实主题）**: 实现抽象主题，定义代理所代表的真实对象
- **Proxy（代理）**: 实现抽象主题，维护对真实主题的引用，控制对真实主题的访问
- **Client（客户端）**: 使用代理对象访问真实主题

### 1.3 设计原则
- **单一职责**: 代理只负责访问控制，真实主题只负责业务逻辑
- **开闭原则**: 支持扩展新的代理类型
- **依赖倒置**: 客户端依赖抽象而非具体实现

### 1.4 优缺点分析
**优点：**
- 控制对对象的访问
- 支持远程访问
- 实现延迟加载
- 提供安全控制
- 支持缓存和优化

**缺点：**
- 增加系统复杂性
- 可能影响性能
- 代理层可能成为瓶颈
- 调试困难

## 2. 接口设计

### 2.1 核心接口
```haskell
-- Haskell接口设计
class Subject a where
  request :: a -> IO String
  expensiveOperation :: a -> IO String
  secureOperation :: a -> String -> IO Bool

-- 代理接口
class (Subject a) => Proxy a where
  getRealSubject :: a -> RealSubject
  checkAccess :: a -> String -> Bool
  logAccess :: a -> String -> IO ()
```

### 2.2 扩展接口
```haskell
-- 支持缓存的代理
class (Proxy a) => CachedProxy a where
  getCache :: a -> Map String String
  setCache :: a -> String -> String -> a
  isCached :: a -> String -> Bool

-- 支持远程的代理
class (Proxy a) => RemoteProxy a where
  getConnection :: a -> Connection
  sendRequest :: a -> String -> IO String
  handleTimeout :: a -> IO ()
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 抽象主题接口
class Subject a where
  request :: a -> IO String
  expensiveOperation :: a -> IO String
  secureOperation :: a -> String -> IO Bool

-- 真实主题
data RealSubject = RealSubject {
  name :: String,
  data :: String
} deriving Show

instance Subject RealSubject where
  request subject = do
    putStrLn $ "RealSubject " ++ name subject ++ " 处理请求"
    return $ "真实响应: " ++ data subject
  
  expensiveOperation subject = do
    putStrLn $ "RealSubject " ++ name subject ++ " 执行昂贵操作"
    threadDelay 1000000  -- 模拟耗时操作
    return $ "昂贵操作结果: " ++ data subject
  
  secureOperation subject password = do
    putStrLn $ "RealSubject " ++ name subject ++ " 执行安全操作"
    return $ password == "correct_password"

-- 虚拟代理（延迟加载）
data VirtualProxy = VirtualProxy {
  realSubject :: Maybe RealSubject,
  subjectName :: String,
  subjectData :: String
} deriving Show

instance Subject VirtualProxy where
  request proxy = do
    real <- getRealSubject proxy
    request real
  
  expensiveOperation proxy = do
    real <- getRealSubject proxy
    expensiveOperation real
  
  secureOperation proxy password = do
    real <- getRealSubject proxy
    secureOperation real password

getRealSubject :: VirtualProxy -> IO RealSubject
getRealSubject proxy = case realSubject proxy of
  Just real -> return real
  Nothing -> do
    putStrLn $ "创建真实主题: " ++ subjectName proxy
    return $ RealSubject (subjectName proxy) (subjectData proxy)

-- 保护代理（访问控制）
data ProtectionProxy = ProtectionProxy {
  realSubject :: RealSubject,
  accessLevel :: String,
  allowedUsers :: [String]
} deriving Show

instance Subject ProtectionProxy where
  request proxy = do
    if checkAccess proxy "user"
    then do
      logAccess proxy "request"
      request (realSubject proxy)
    else return "访问被拒绝"
  
  expensiveOperation proxy = do
    if checkAccess proxy "admin"
    then do
      logAccess proxy "expensiveOperation"
      expensiveOperation (realSubject proxy)
    else return "权限不足"
  
  secureOperation proxy password = do
    if checkAccess proxy "admin"
    then do
      logAccess proxy "secureOperation"
      secureOperation (realSubject proxy) password
    else return False

checkAccess :: ProtectionProxy -> String -> Bool
checkAccess proxy user = user `elem` allowedUsers proxy

logAccess :: ProtectionProxy -> String -> IO ()
logAccess proxy operation = 
  putStrLn $ "记录访问: " ++ operation ++ " by " ++ accessLevel proxy

-- 缓存代理
data CachedProxy = CachedProxy {
  realSubject :: RealSubject,
  cache :: IORef (Map String String)
} deriving Show

instance Subject CachedProxy where
  request proxy = do
    cacheMap <- readIORef (cache proxy)
    case Map.lookup "request" cacheMap of
      Just result -> do
        putStrLn "从缓存返回结果"
        return result
      Nothing -> do
        result <- request (realSubject proxy)
        modifyIORef (cache proxy) (Map.insert "request" result)
        return result
  
  expensiveOperation proxy = do
    cacheMap <- readIORef (cache proxy)
    case Map.lookup "expensive" cacheMap of
      Just result -> do
        putStrLn "从缓存返回昂贵操作结果"
        return result
      Nothing -> do
        result <- expensiveOperation (realSubject proxy)
        modifyIORef (cache proxy) (Map.insert "expensive" result)
        return result
  
  secureOperation proxy password = 
    secureOperation (realSubject proxy) password

-- 远程代理
data RemoteProxy = RemoteProxy {
  realSubject :: RealSubject,
  connection :: Connection,
  timeout :: Int
} deriving Show

data Connection = Connection {
  host :: String,
  port :: Int,
  isConnected :: Bool
} deriving Show

instance Subject RemoteProxy where
  request proxy = do
    if isConnected (connection proxy)
    then do
      putStrLn $ "通过远程连接发送请求到 " ++ host (connection proxy)
      sendRequest proxy "request"
    else do
      putStrLn "连接失败，使用本地模式"
      request (realSubject proxy)
  
  expensiveOperation proxy = do
    if isConnected (connection proxy)
    then do
      putStrLn "通过远程连接执行昂贵操作"
      sendRequest proxy "expensive"
    else do
      putStrLn "连接失败，本地执行昂贵操作"
      expensiveOperation (realSubject proxy)
  
  secureOperation proxy password = do
    if isConnected (connection proxy)
    then do
      putStrLn "通过远程连接执行安全操作"
      result <- sendRequest proxy "secure"
      return $ result == "true"
    else do
      putStrLn "连接失败，本地执行安全操作"
      secureOperation (realSubject proxy) password

sendRequest :: RemoteProxy -> String -> IO String
sendRequest proxy operation = do
  putStrLn $ "发送请求: " ++ operation ++ " 到 " ++ host (connection proxy)
  threadDelay (timeout proxy * 1000)  -- 模拟网络延迟
  return $ "远程响应: " ++ operation

-- 使用示例
main :: IO ()
main = do
  putStrLn "代理模式示例:"
  
  -- 创建真实主题
  let realSubject = RealSubject "真实主题" "重要数据"
  
  -- 虚拟代理
  let virtualProxy = VirtualProxy Nothing "延迟主题" "延迟数据"
  putStrLn "\n=== 虚拟代理 ==="
  result1 <- request virtualProxy
  putStrLn result1
  
  -- 保护代理
  let protectionProxy = ProtectionProxy realSubject "admin" ["admin", "user"]
  putStrLn "\n=== 保护代理 ==="
  result2 <- request protectionProxy
  putStrLn result2
  result3 <- expensiveOperation protectionProxy
  putStrLn result3
  
  -- 缓存代理
  cacheRef <- newIORef Map.empty
  let cachedProxy = CachedProxy realSubject cacheRef
  putStrLn "\n=== 缓存代理 ==="
  result4 <- request cachedProxy
  putStrLn result4
  result5 <- request cachedProxy  -- 第二次调用使用缓存
  putStrLn result5
  
  -- 远程代理
  let connection = Connection "remote.server.com" 8080 True
  let remoteProxy = RemoteProxy realSubject connection 5000
  putStrLn "\n=== 远程代理 ==="
  result6 <- request remoteProxy
  putStrLn result6
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use std::thread;

// 抽象主题trait
trait Subject {
    fn request(&self) -> String;
    fn expensive_operation(&self) -> String;
    fn secure_operation(&self, password: &str) -> bool;
}

// 真实主题
#[derive(Debug, Clone)]
struct RealSubject {
    name: String,
    data: String,
}

impl RealSubject {
    fn new(name: String, data: String) -> Self {
        RealSubject { name, data }
    }
}

impl Subject for RealSubject {
    fn request(&self) -> String {
        println!("RealSubject {} 处理请求", self.name);
        format!("真实响应: {}", self.data)
    }
    
    fn expensive_operation(&self) -> String {
        println!("RealSubject {} 执行昂贵操作", self.name);
        thread::sleep(Duration::from_secs(1)); // 模拟耗时操作
        format!("昂贵操作结果: {}", self.data)
    }
    
    fn secure_operation(&self, password: &str) -> bool {
        println!("RealSubject {} 执行安全操作", self.name);
        password == "correct_password"
    }
}

// 虚拟代理（延迟加载）
#[derive(Debug)]
struct VirtualProxy {
    real_subject: Option<RealSubject>,
    subject_name: String,
    subject_data: String,
}

impl VirtualProxy {
    fn new(name: String, data: String) -> Self {
        VirtualProxy {
            real_subject: None,
            subject_name: name,
            subject_data: data,
        }
    }
    
    fn get_real_subject(&mut self) -> &RealSubject {
        if self.real_subject.is_none() {
            println!("创建真实主题: {}", self.subject_name);
            self.real_subject = Some(RealSubject::new(
                self.subject_name.clone(),
                self.subject_data.clone(),
            ));
        }
        self.real_subject.as_ref().unwrap()
    }
}

impl Subject for VirtualProxy {
    fn request(&self) -> String {
        // 注意：这里简化了实现，实际需要可变引用
        "虚拟代理请求".to_string()
    }
    
    fn expensive_operation(&self) -> String {
        "虚拟代理昂贵操作".to_string()
    }
    
    fn secure_operation(&self, _password: &str) -> bool {
        false
    }
}

// 保护代理（访问控制）
#[derive(Debug)]
struct ProtectionProxy {
    real_subject: RealSubject,
    access_level: String,
    allowed_users: Vec<String>,
}

impl ProtectionProxy {
    fn new(real_subject: RealSubject, access_level: String, allowed_users: Vec<String>) -> Self {
        ProtectionProxy {
            real_subject,
            access_level,
            allowed_users,
        }
    }
    
    fn check_access(&self, user: &str) -> bool {
        self.allowed_users.contains(&user.to_string())
    }
    
    fn log_access(&self, operation: &str) {
        println!("记录访问: {} by {}", operation, self.access_level);
    }
}

impl Subject for ProtectionProxy {
    fn request(&self) -> String {
        if self.check_access("user") {
            self.log_access("request");
            self.real_subject.request()
        } else {
            "访问被拒绝".to_string()
        }
    }
    
    fn expensive_operation(&self) -> String {
        if self.check_access("admin") {
            self.log_access("expensiveOperation");
            self.real_subject.expensive_operation()
        } else {
            "权限不足".to_string()
        }
    }
    
    fn secure_operation(&self, password: &str) -> bool {
        if self.check_access("admin") {
            self.log_access("secureOperation");
            self.real_subject.secure_operation(password)
        } else {
            false
        }
    }
}

// 缓存代理
#[derive(Debug)]
struct CachedProxy {
    real_subject: RealSubject,
    cache: Arc<Mutex<HashMap<String, String>>>,
}

impl CachedProxy {
    fn new(real_subject: RealSubject) -> Self {
        CachedProxy {
            real_subject,
            cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

impl Subject for CachedProxy {
    fn request(&self) -> String {
        let mut cache = self.cache.lock().unwrap();
        if let Some(result) = cache.get("request") {
            println!("从缓存返回结果");
            result.clone()
        } else {
            let result = self.real_subject.request();
            cache.insert("request".to_string(), result.clone());
            result
        }
    }
    
    fn expensive_operation(&self) -> String {
        let mut cache = self.cache.lock().unwrap();
        if let Some(result) = cache.get("expensive") {
            println!("从缓存返回昂贵操作结果");
            result.clone()
        } else {
            let result = self.real_subject.expensive_operation();
            cache.insert("expensive".to_string(), result.clone());
            result
        }
    }
    
    fn secure_operation(&self, password: &str) -> bool {
        self.real_subject.secure_operation(password)
    }
}

// 远程代理
#[derive(Debug)]
struct RemoteProxy {
    real_subject: RealSubject,
    connection: Connection,
    timeout: u64,
}

#[derive(Debug)]
struct Connection {
    host: String,
    port: u16,
    is_connected: bool,
}

impl RemoteProxy {
    fn new(real_subject: RealSubject, host: String, port: u16, timeout: u64) -> Self {
        RemoteProxy {
            real_subject,
            connection: Connection {
                host,
                port,
                is_connected: true,
            },
            timeout,
        }
    }
    
    fn send_request(&self, operation: &str) -> String {
        println!("发送请求: {} 到 {}", operation, self.connection.host);
        thread::sleep(Duration::from_millis(self.timeout)); // 模拟网络延迟
        format!("远程响应: {}", operation)
    }
}

impl Subject for RemoteProxy {
    fn request(&self) -> String {
        if self.connection.is_connected {
            println!("通过远程连接发送请求到 {}", self.connection.host);
            self.send_request("request")
        } else {
            println!("连接失败，使用本地模式");
            self.real_subject.request()
        }
    }
    
    fn expensive_operation(&self) -> String {
        if self.connection.is_connected {
            println!("通过远程连接执行昂贵操作");
            self.send_request("expensive")
        } else {
            println!("连接失败，本地执行昂贵操作");
            self.real_subject.expensive_operation()
        }
    }
    
    fn secure_operation(&self, password: &str) -> bool {
        if self.connection.is_connected {
            println!("通过远程连接执行安全操作");
            let result = self.send_request("secure");
            result == "true"
        } else {
            println!("连接失败，本地执行安全操作");
            self.real_subject.secure_operation(password)
        }
    }
}

// 使用示例
fn main() {
    println!("代理模式示例:");
    
    // 创建真实主题
    let real_subject = RealSubject::new("真实主题".to_string(), "重要数据".to_string());
    
    // 保护代理
    let protection_proxy = ProtectionProxy::new(
        real_subject.clone(),
        "admin".to_string(),
        vec!["admin".to_string(), "user".to_string()],
    );
    
    println!("\n=== 保护代理 ===");
    println!("{}", protection_proxy.request());
    println!("{}", protection_proxy.expensive_operation());
    
    // 缓存代理
    let cached_proxy = CachedProxy::new(real_subject.clone());
    println!("\n=== 缓存代理 ===");
    println!("{}", cached_proxy.request());
    println!("{}", cached_proxy.request()); // 第二次调用使用缓存
    
    // 远程代理
    let remote_proxy = RemoteProxy::new(
        real_subject,
        "remote.server.com".to_string(),
        8080,
        5000,
    );
    println!("\n=== 远程代理 ===");
    println!("{}", remote_proxy.request());
}
```

### 3.3 Lean实现

```lean
-- 抽象主题类型类
class Subject (α : Type) where
  request : α → IO String
  expensiveOperation : α → IO String
  secureOperation : α → String → IO Bool

-- 真实主题
structure RealSubject where
  name : String
  data : String

def newRealSubject (name : String) (data : String) : RealSubject := {
  name := name,
  data := data
}

instance : Subject RealSubject where
  request subject := do
    IO.println ("RealSubject " ++ subject.name ++ " 处理请求")
    return ("真实响应: " ++ subject.data)
  
  expensiveOperation subject := do
    IO.println ("RealSubject " ++ subject.name ++ " 执行昂贵操作")
    -- 模拟耗时操作
    return ("昂贵操作结果: " ++ subject.data)
  
  secureOperation subject password := do
    IO.println ("RealSubject " ++ subject.name ++ " 执行安全操作")
    return (password = "correct_password")

-- 虚拟代理
structure VirtualProxy where
  realSubject : Option RealSubject
  subjectName : String
  subjectData : String

def newVirtualProxy (name : String) (data : String) : VirtualProxy := {
  realSubject := none,
  subjectName := name,
  subjectData := data
}

def getRealSubject (proxy : VirtualProxy) : IO RealSubject :=
  match proxy.realSubject with
  | some real => return real
  | none => do
    IO.println ("创建真实主题: " ++ proxy.subjectName)
    return (newRealSubject proxy.subjectName proxy.subjectData)

instance : Subject VirtualProxy where
  request proxy := do
    real := getRealSubject proxy
    request real
  
  expensiveOperation proxy := do
    real := getRealSubject proxy
    expensiveOperation real
  
  secureOperation proxy password := do
    real := getRealSubject proxy
    secureOperation real password

-- 保护代理
structure ProtectionProxy where
  realSubject : RealSubject
  accessLevel : String
  allowedUsers : List String

def newProtectionProxy (real : RealSubject) (level : String) (users : List String) : ProtectionProxy := {
  realSubject := real,
  accessLevel := level,
  allowedUsers := users
}

def checkAccess (proxy : ProtectionProxy) (user : String) : Bool :=
  user ∈ proxy.allowedUsers

def logAccess (proxy : ProtectionProxy) (operation : String) : IO Unit :=
  IO.println ("记录访问: " ++ operation ++ " by " ++ proxy.accessLevel)

instance : Subject ProtectionProxy where
  request proxy := do
    if checkAccess proxy "user"
    then do
      logAccess proxy "request"
      request proxy.realSubject
    else return "访问被拒绝"
  
  expensiveOperation proxy := do
    if checkAccess proxy "admin"
    then do
      logAccess proxy "expensiveOperation"
      expensiveOperation proxy.realSubject
    else return "权限不足"
  
  secureOperation proxy password := do
    if checkAccess proxy "admin"
    then do
      logAccess proxy "secureOperation"
      secureOperation proxy.realSubject password
    else return false

-- 使用示例
def main : IO Unit := do
  IO.println "代理模式示例:"
  
  -- 创建真实主题
  let realSubject := newRealSubject "真实主题" "重要数据"
  
  -- 保护代理
  let protectionProxy := newProtectionProxy realSubject "admin" ["admin", "user"]
  
  IO.println "\n=== 保护代理 ==="
  result1 := request protectionProxy
  IO.println result1
  
  result2 := expensiveOperation protectionProxy
  IO.println result2
```

## 4. 工程实践

### 4.1 设计考虑
- **代理类型选择**: 根据需求选择合适的代理类型
- **性能影响**: 考虑代理层对性能的影响
- **错误处理**: 处理代理可能出现的异常
- **线程安全**: 确保多线程环境下的安全性

### 4.2 实现模式
```haskell
-- 智能代理
data SmartProxy = SmartProxy {
  realSubject :: RealSubject,
  accessCount :: IORef Int,
  lastAccess :: IORef UTCTime
}

-- 同步代理
data SynchronizedProxy = SynchronizedProxy {
  realSubject :: RealSubject,
  lock :: MVar ()
}

-- 日志代理
data LoggingProxy = LoggingProxy {
  realSubject :: RealSubject,
  logger :: Logger
}
```

### 4.3 错误处理
```haskell
-- 错误类型
data ProxyError = 
  AccessDenied String
  | ConnectionFailed String
  | TimeoutError
  | CacheMiss String

-- 安全代理操作
safeProxyRequest :: Proxy a => a -> IO (Either ProxyError String)
safeProxyRequest proxy = 
  try (request proxy) >>= \case
    Left e -> return $ Left $ ConnectionFailed (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略
- **LRU缓存**: 最近最少使用策略
- **TTL缓存**: 基于时间的缓存过期
- **分层缓存**: 多级缓存架构

### 5.2 连接池
```haskell
-- 连接池代理
data ConnectionPoolProxy = ConnectionPoolProxy {
  realSubject :: RealSubject,
  pool :: ConnectionPool,
  maxConnections :: Int
}

-- 连接管理
manageConnection :: ConnectionPoolProxy -> IO Connection
manageConnection proxy = do
  available <- getAvailableConnections (pool proxy)
  if available > 0
  then getConnection (pool proxy)
  else createNewConnection (pool proxy)
```

### 5.3 异步处理
```haskell
-- 异步代理
data AsyncProxy = AsyncProxy {
  realSubject :: RealSubject,
  executor :: ThreadPool,
  queue :: MessageQueue
}

-- 异步请求
asyncRequest :: AsyncProxy -> String -> IO (Async String)
asyncRequest proxy message = do
  submitTask (executor proxy) (request (realSubject proxy))
```

## 6. 应用场景

### 6.1 远程代理
```haskell
-- RPC代理
data RPCProxy = RPCProxy {
  serviceName :: String,
  endpoint :: String,
  serializer :: Serializer
}

-- 远程调用
remoteCall :: RPCProxy -> String -> [String] -> IO String
remoteCall proxy method args = do
  request <- serialize (serializer proxy) (method, args)
  response <- sendRequest (endpoint proxy) request
  deserialize (serializer proxy) response
```

### 6.2 虚拟代理
```haskell
-- 图片代理
data ImageProxy = ImageProxy {
  imagePath :: String,
  realImage :: Maybe Image,
  loadingStatus :: IORef LoadingStatus
}

-- 延迟加载
loadImage :: ImageProxy -> IO Image
loadImage proxy = case realImage proxy of
  Just img -> return img
  Nothing -> do
    img <- loadImageFromFile (imagePath proxy)
    writeIORef (loadingStatus proxy) Loaded
    return img
```

### 6.3 保护代理
```haskell
-- 权限代理
data PermissionProxy = PermissionProxy {
  realSubject :: RealSubject,
  userRole :: UserRole,
  permissions :: PermissionSet
}

-- 权限检查
checkPermission :: PermissionProxy -> Operation -> Bool
checkPermission proxy operation = 
  operation `elem` permissions proxy
```

### 6.4 缓存代理
```haskell
-- 数据库代理
data DatabaseProxy = DatabaseProxy {
  realDatabase :: Database,
  cache :: Cache,
  cachePolicy :: CachePolicy
}

-- 缓存查询
cachedQuery :: DatabaseProxy -> Query -> IO Result
cachedQuery proxy query = do
  cached <- getFromCache (cache proxy) query
  case cached of
    Just result -> return result
    Nothing -> do
      result <- executeQuery (realDatabase proxy) query
      putInCache (cache proxy) query result
      return result
```

## 7. 最佳实践

### 7.1 设计原则
- **透明性**: 客户端无需知道代理的存在
- **职责分离**: 代理只负责控制访问，不处理业务逻辑
- **性能考虑**: 避免代理成为性能瓶颈
- **错误处理**: 妥善处理代理可能出现的异常

### 7.2 实现建议
```haskell
-- 代理工厂
class ProxyFactory a where
  createProxy :: String -> Maybe a
  listProxies :: [String]
  validateProxy :: a -> Bool

-- 代理注册表
data ProxyRegistry = ProxyRegistry {
  proxies :: Map String (forall a. Proxy a => a),
  metadata :: Map String String
}

-- 线程安全代理管理器
data ThreadSafeProxyManager = ThreadSafeProxyManager {
  manager :: MVar ProxyManager,
  lock :: MVar ()
}
```

### 7.3 测试策略
```haskell
-- 代理测试
testProxy :: Proxy a => a -> Bool
testProxy proxy = 
  -- 测试代理的基本功能
  True

-- 性能测试
benchmarkProxy :: Proxy a => a -> IO Double
benchmarkProxy proxy = do
  start <- getCurrentTime
  replicateM_ 1000 $ request proxy
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑
- **插件系统**: 支持动态加载新的代理类型
- **序列化**: 支持代理的序列化和反序列化
- **版本控制**: 支持代理接口的版本管理
- **分布式**: 支持跨网络的代理通信

## 8. 总结

代理模式是控制对象访问的重要工具，通过引入代理层实现了访问控制、缓存、远程访问等功能。在实现时需要注意代理的透明性、性能影响和错误处理。该模式在RPC、缓存、权限控制、延迟加载等场景中有广泛应用。
