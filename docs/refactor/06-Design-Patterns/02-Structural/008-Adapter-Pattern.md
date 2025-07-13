# 适配器模式 (Adapter Pattern)

## 1. 理论基础

### 1.1 模式定义

适配器模式是一种结构型设计模式，它允许不兼容的接口能够协同工作。适配器模式通过包装一个已存在的类，提供一个不同的接口，使得原本由于接口不兼容而不能一起工作的类可以一起工作。

### 1.2 形式化定义

```lean
-- 适配器模式的形式化定义
inductive AdapterPattern : Type
| ObjectAdapter : Adaptee → Target → Adapter
| ClassAdapter : Adaptee → Target → Adapter

-- 接口兼容性关系
inductive InterfaceCompatibility : Interface → Interface → Prop
| DirectCompatible : Π (i1 i2 : Interface), 
    InterfaceSignature i1 = InterfaceSignature i2 → 
    InterfaceCompatibility i1 i2
| AdapterCompatible : Π (i1 i2 : Interface) (a : Adapter),
    AdapterAdapts a i1 i2 → 
    InterfaceCompatibility i1 i2

-- 适配器正确性定理
theorem adapter_correctness (adaptee : Adaptee) (target : Target) :
  ∀ (adapter : Adapter),
  AdapterPattern.ObjectAdapter adaptee target adapter →
  ∀ (request : Request),
  TargetResponse (target, request) = 
  AdapterResponse (adapter, AdapteeRequest adaptee request)
```

### 1.3 语义模型

```haskell
-- 适配器模式的语义模型
data AdapterSemantics = AdapterSemantics
  { sourceInterface :: Interface
  , targetInterface :: Interface
  , transformation :: Request -> Response
  , invariants :: [Invariant]
  }

-- 接口语义
data Interface = Interface
  { interfaceName :: String
  , methods :: [Method]
  , contracts :: [Contract]
  }

-- 适配器转换函数
type AdapterTransform = Request -> Either Error Response

-- 适配器正确性验证
validateAdapter :: AdapterSemantics -> Bool
validateAdapter semantics = 
  all validateInvariant (invariants semantics) &&
  validateTransformation (transformation semantics)
```

## 2. 设计原则

### 2.1 核心原则

1. **单一职责原则**：适配器只负责接口转换
2. **开闭原则**：对扩展开放，对修改关闭
3. **依赖倒置原则**：依赖抽象而非具体实现
4. **接口隔离原则**：提供精确的接口定义

### 2.2 设计约束

```rust
// 适配器设计约束
trait AdapterConstraints {
    // 保持原有功能不变
    fn preserves_functionality(&self) -> bool;
    
    // 最小化性能开销
    fn performance_overhead(&self) -> Duration;
    
    // 保持接口一致性
    fn interface_consistency(&self) -> bool;
    
    // 支持可扩展性
    fn extensibility_score(&self) -> f64;
}
```

## 3. 多语言实现

### 3.1 Rust实现

#### 3.1.1 对象适配器

```rust
use std::collections::HashMap;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};

// 目标接口
#[async_trait]
pub trait TargetInterface {
    async fn request(&self, data: &RequestData) -> Result<ResponseData, Error>;
    fn get_metadata(&self) -> HashMap<String, String>;
}

// 被适配的类
pub struct Adaptee {
    internal_state: HashMap<String, String>,
}

impl Adaptee {
    pub fn new() -> Self {
        let mut state = HashMap::new();
        state.insert("version".to_string(), "1.0".to_string());
        Adaptee { internal_state: state }
    }
    
    pub async fn specific_request(&self, data: &RequestData) -> Result<ResponseData, Error> {
        // 原有的特定实现
        Ok(ResponseData {
            content: format!("Adaptee response: {:?}", data),
            timestamp: chrono::Utc::now(),
        })
    }
    
    pub fn get_internal_state(&self) -> &HashMap<String, String> {
        &self.internal_state
    }
}

// 适配器实现
pub struct ObjectAdapter {
    adaptee: Adaptee,
    configuration: AdapterConfig,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct AdapterConfig {
    pub timeout: Duration,
    pub retry_count: u32,
    pub cache_enabled: bool,
}

impl ObjectAdapter {
    pub fn new(adaptee: Adaptee, config: AdapterConfig) -> Self {
        ObjectAdapter { adaptee, configuration: config }
    }
    
    fn transform_request(&self, data: &RequestData) -> RequestData {
        // 请求转换逻辑
        RequestData {
            id: data.id.clone(),
            content: format!("Transformed: {}", data.content),
            metadata: data.metadata.clone(),
        }
    }
    
    fn transform_response(&self, response: ResponseData) -> ResponseData {
        // 响应转换逻辑
        ResponseData {
            content: format!("Adapter: {}", response.content),
            timestamp: response.timestamp,
        }
    }
}

#[async_trait]
impl TargetInterface for ObjectAdapter {
    async fn request(&self, data: &RequestData) -> Result<ResponseData, Error> {
        let transformed_request = self.transform_request(data);
        
        // 使用配置进行请求处理
        let response = if self.configuration.cache_enabled {
            self.cached_request(&transformed_request).await?
        } else {
            self.adaptee.specific_request(&transformed_request).await?
        };
        
        Ok(self.transform_response(response))
    }
    
    fn get_metadata(&self) -> HashMap<String, String> {
        let mut metadata = self.adaptee.get_internal_state().clone();
        metadata.insert("adapter_type".to_string(), "object".to_string());
        metadata.insert("timeout".to_string(), self.configuration.timeout.as_millis().to_string());
        metadata
    }
}

impl ObjectAdapter {
    async fn cached_request(&self, data: &RequestData) -> Result<ResponseData, Error> {
        // 缓存实现
        self.adaptee.specific_request(data).await
    }
}
```

#### 3.1.2 类适配器

```rust
// 类适配器通过继承实现
pub trait AdapteeInterface {
    fn specific_request(&self, data: &RequestData) -> Result<ResponseData, Error>;
    fn get_internal_state(&self) -> HashMap<String, String>;
}

pub struct ClassAdapter {
    internal_state: HashMap<String, String>,
    configuration: AdapterConfig,
}

impl ClassAdapter {
    pub fn new(config: AdapterConfig) -> Self {
        let mut state = HashMap::new();
        state.insert("version".to_string(), "1.0".to_string());
        ClassAdapter { internal_state: state, configuration: config }
    }
}

impl AdapteeInterface for ClassAdapter {
    fn specific_request(&self, data: &RequestData) -> Result<ResponseData, Error> {
        // 继承的特定实现
        Ok(ResponseData {
            content: format!("Class adapter response: {:?}", data),
            timestamp: chrono::Utc::now(),
        })
    }
    
    fn get_internal_state(&self) -> HashMap<String, String> {
        self.internal_state.clone()
    }
}

#[async_trait]
impl TargetInterface for ClassAdapter {
    async fn request(&self, data: &RequestData) -> Result<ResponseData, Error> {
        // 适配器逻辑
        let response = self.specific_request(data)?;
        Ok(ResponseData {
            content: format!("Class adapter: {}", response.content),
            timestamp: response.timestamp,
        })
    }
    
    fn get_metadata(&self) -> HashMap<String, String> {
        let mut metadata = self.get_internal_state();
        metadata.insert("adapter_type".to_string(), "class".to_string());
        metadata
    }
}
```

### 3.2 Haskell实现

#### 3.2.1 函数式适配器

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.IO.Class
import Data.Time.Clock
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T

-- 目标接口类型类
class TargetInterface a where
    request :: MonadIO m => a -> RequestData -> m (Either Error ResponseData)
    getMetadata :: a -> Map String String

-- 被适配的类型
data Adaptee = Adaptee
    { adapteeState :: Map String String
    , adapteeVersion :: Text
    }

-- 适配器配置
data AdapterConfig = AdapterConfig
    { timeout :: NominalDiffTime
    , retryCount :: Int
    , cacheEnabled :: Bool
    }

-- 对象适配器
data ObjectAdapter = ObjectAdapter
    { adaptee :: Adaptee
    , config :: AdapterConfig
    }

-- 请求和响应数据类型
data RequestData = RequestData
    { requestId :: Text
    , requestContent :: Text
    , requestMetadata :: Map String String
    }

data ResponseData = ResponseData
    { responseContent :: Text
    , responseTimestamp :: UTCTime
    }

data Error = Error
    { errorMessage :: Text
    , errorCode :: Int
    }

-- 适配器实现
instance TargetInterface ObjectAdapter where
    request adapter reqData = do
        let transformedRequest = transformRequest adapter reqData
        response <- if cacheEnabled (config adapter)
                   then cachedRequest adapter transformedRequest
                   else specificRequest (adaptee adapter) transformedRequest
        return $ fmap (transformResponse adapter) response
    
    getMetadata adapter = 
        let baseMetadata = adapteeState (adaptee adapter)
            adapterMetadata = Map.fromList
                [ ("adapter_type", "object")
                , ("timeout", show $ timeout (config adapter))
                , ("retry_count", show $ retryCount (config adapter))
                ]
        in Map.union baseMetadata adapterMetadata

-- 转换函数
transformRequest :: ObjectAdapter -> RequestData -> RequestData
transformRequest adapter req = req
    { requestContent = T.append "Transformed: " (requestContent req)
    }

transformResponse :: ObjectAdapter -> ResponseData -> ResponseData
transformResponse adapter resp = resp
    { responseContent = T.append "Adapter: " (responseContent resp)
    }

-- 特定请求实现
specificRequest :: MonadIO m => Adaptee -> RequestData -> m (Either Error ResponseData)
specificRequest adaptee reqData = do
    now <- liftIO getCurrentTime
    return $ Right ResponseData
        { responseContent = T.append "Adaptee response: " (requestContent reqData)
        , responseTimestamp = now
        }

-- 缓存请求实现
cachedRequest :: MonadIO m => ObjectAdapter -> RequestData -> m (Either Error ResponseData)
cachedRequest adapter reqData = specificRequest (adaptee adapter) reqData

-- 工厂函数
createObjectAdapter :: Adaptee -> AdapterConfig -> ObjectAdapter
createObjectAdapter adaptee config = ObjectAdapter adaptee config

-- 默认配置
defaultAdapterConfig :: AdapterConfig
defaultAdapterConfig = AdapterConfig
    { timeout = 30.0
    , retryCount = 3
    , cacheEnabled = True
    }
```

#### 3.2.2 类型类适配器

```haskell
-- 类型类适配器
class AdapteeInterface a where
    specificRequest :: MonadIO m => a -> RequestData -> m (Either Error ResponseData)
    getInternalState :: a -> Map String String

instance AdapteeInterface Adaptee where
    specificRequest adaptee reqData = do
        now <- liftIO getCurrentTime
        return $ Right ResponseData
            { responseContent = T.append "Class adapter response: " (requestContent reqData)
            , responseTimestamp = now
            }
    
    getInternalState = adapteeState

-- 类适配器
data ClassAdapter = ClassAdapter
    { classAdapterState :: Map String String
    , classAdapterConfig :: AdapterConfig
    }

instance AdapteeInterface ClassAdapter where
    specificRequest adapter reqData = do
        now <- liftIO getCurrentTime
        return $ Right ResponseData
            { responseContent = T.append "Class adapter specific: " (requestContent reqData)
            , responseTimestamp = now
            }
    
    getInternalState = classAdapterState

instance TargetInterface ClassAdapter where
    request adapter reqData = do
        response <- specificRequest adapter reqData
        return $ fmap (transformClassResponse adapter) response
    
    getMetadata adapter = 
        let baseMetadata = getInternalState adapter
            adapterMetadata = Map.fromList
                [ ("adapter_type", "class")
                , ("timeout", show $ timeout (classAdapterConfig adapter))
                ]
        in Map.union baseMetadata adapterMetadata

transformClassResponse :: ClassAdapter -> ResponseData -> ResponseData
transformClassResponse adapter resp = resp
    { responseContent = T.append "Class adapter: " (responseContent resp)
    }
```

### 3.3 Lean实现

#### 3.3.1 形式化适配器

```lean
import Lean.Data.HashMap
import Lean.Data.Json
import System.Time

-- 接口定义
class TargetInterface (α : Type) where
  request : α → RequestData → IO (Except Error ResponseData)
  getMetadata : α → HashMap String String

-- 被适配的类型
structure Adaptee where
  state : HashMap String String
  version : String

-- 适配器配置
structure AdapterConfig where
  timeout : Nat
  retryCount : Nat
  cacheEnabled : Bool

-- 对象适配器
structure ObjectAdapter where
  adaptee : Adaptee
  config : AdapterConfig

-- 数据类型
structure RequestData where
  id : String
  content : String
  metadata : HashMap String String

structure ResponseData where
  content : String
  timestamp : IO.Prim.Real

structure Error where
  message : String
  code : Nat

-- 转换函数
def transformRequest (adapter : ObjectAdapter) (req : RequestData) : RequestData :=
  { req with content := "Transformed: " ++ req.content }

def transformResponse (adapter : ObjectAdapter) (resp : ResponseData) : ResponseData :=
  { resp with content := "Adapter: " ++ resp.content }

-- 特定请求实现
def specificRequest (adaptee : Adaptee) (req : RequestData) : IO (Except Error ResponseData) := do
  let timestamp ← IO.monoMsNow
  return Except.ok {
    content := "Adaptee response: " ++ req.content
    timestamp := timestamp
  }

-- 缓存请求实现
def cachedRequest (adapter : ObjectAdapter) (req : RequestData) : IO (Except Error ResponseData) :=
  specificRequest adapter.adaptee req

-- 适配器实现
instance : TargetInterface ObjectAdapter where
  request adapter req := do
    let transformedReq := transformRequest adapter req
    let response ← if adapter.config.cacheEnabled
                   then cachedRequest adapter transformedReq
                   else specificRequest adapter.adaptee transformedReq
    return response.map (transformResponse adapter)
  
  getMetadata adapter :=
    let baseMetadata := adapter.adaptee.state
    let adapterMetadata := HashMap.ofList [
      ("adapter_type", "object"),
      ("timeout", toString adapter.config.timeout),
      ("retry_count", toString adapter.config.retryCount)
    ]
    HashMap.union baseMetadata adapterMetadata

-- 类适配器
structure ClassAdapter where
  state : HashMap String String
  config : AdapterConfig

class AdapteeInterface (α : Type) where
  specificRequest : α → RequestData → IO (Except Error ResponseData)
  getInternalState : α → HashMap String String

instance : AdapteeInterface ClassAdapter where
  specificRequest adapter req := do
    let timestamp ← IO.monoMsNow
    return Except.ok {
      content := "Class adapter response: " ++ req.content
      timestamp := timestamp
    }
  
  getInternalState := ClassAdapter.state

instance : TargetInterface ClassAdapter where
  request adapter req := do
    let response ← specificRequest adapter req
    return response.map fun resp => {
      resp with content := "Class adapter: " ++ resp.content
    }
  
  getMetadata adapter :=
    let baseMetadata := getInternalState adapter
    let adapterMetadata := HashMap.ofList [
      ("adapter_type", "class"),
      ("timeout", toString adapter.config.timeout)
    ]
    HashMap.union baseMetadata adapterMetadata
```

## 4. 工程实践

### 4.1 架构设计

```rust
// 适配器架构设计
pub mod adapter {
    pub mod core {
        pub trait AdapterCore {
            fn validate_configuration(&self) -> Result<(), AdapterError>;
            fn initialize(&mut self) -> Result<(), AdapterError>;
            fn shutdown(&mut self) -> Result<(), AdapterError>;
        }
    }
    
    pub mod factory {
        use super::core::AdapterCore;
        
        pub trait AdapterFactory {
            type Adapter: AdapterCore;
            
            fn create_adapter(&self, config: &AdapterConfig) -> Result<Self::Adapter, AdapterError>;
            fn validate_config(&self, config: &AdapterConfig) -> Result<(), AdapterError>;
        }
    }
    
    pub mod registry {
        use std::collections::HashMap;
        use super::factory::AdapterFactory;
        
        pub struct AdapterRegistry {
            factories: HashMap<String, Box<dyn AdapterFactory>>,
        }
        
        impl AdapterRegistry {
            pub fn new() -> Self {
                AdapterRegistry { factories: HashMap::new() }
            }
            
            pub fn register_factory<F: AdapterFactory + 'static>(
                &mut self, 
                name: String, 
                factory: F
            ) {
                self.factories.insert(name, Box::new(factory));
            }
            
            pub fn create_adapter(
                &self, 
                name: &str, 
                config: &AdapterConfig
            ) -> Result<Box<dyn AdapterCore>, AdapterError> {
                if let Some(factory) = self.factories.get(name) {
                    factory.create_adapter(config)
                } else {
                    Err(AdapterError::FactoryNotFound(name.to_string()))
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
pub struct AdapterConfig {
    pub timeout: Duration,
    pub retry_count: u32,
    pub cache_enabled: bool,
    pub cache_ttl: Duration,
    pub max_connections: u32,
    pub connection_pool_size: u32,
    pub logging_level: LogLevel,
    pub metrics_enabled: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

impl Default for AdapterConfig {
    fn default() -> Self {
        AdapterConfig {
            timeout: Duration::from_secs(30),
            retry_count: 3,
            cache_enabled: true,
            cache_ttl: Duration::from_secs(300),
            max_connections: 100,
            connection_pool_size: 10,
            logging_level: LogLevel::Info,
            metrics_enabled: true,
        }
    }
}
```

### 4.3 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AdapterError {
    #[error("Configuration error: {0}")]
    Configuration(String),
    
    #[error("Connection error: {0}")]
    Connection(String),
    
    #[error("Timeout error: {0}")]
    Timeout(String),
    
    #[error("Transformation error: {0}")]
    Transformation(String),
    
    #[error("Factory not found: {0}")]
    FactoryNotFound(String),
    
    #[error("Validation error: {0}")]
    Validation(String),
}

impl AdapterError {
    pub fn is_retryable(&self) -> bool {
        matches!(self, 
            AdapterError::Connection(_) | 
            AdapterError::Timeout(_)
        )
    }
    
    pub fn error_code(&self) -> u32 {
        match self {
            AdapterError::Configuration(_) => 1001,
            AdapterError::Connection(_) => 1002,
            AdapterError::Timeout(_) => 1003,
            AdapterError::Transformation(_) => 1004,
            AdapterError::FactoryNotFound(_) => 1005,
            AdapterError::Validation(_) => 1006,
        }
    }
}
```

## 5. 性能优化

### 5.1 缓存策略

```rust
use std::collections::HashMap;
use std::sync::RwLock;
use std::time::{Duration, Instant};

pub struct AdapterCache {
    cache: RwLock<HashMap<String, CachedItem>>,
    ttl: Duration,
    max_size: usize,
}

struct CachedItem {
    data: ResponseData,
    timestamp: Instant,
}

impl AdapterCache {
    pub fn new(ttl: Duration, max_size: usize) -> Self {
        AdapterCache {
            cache: RwLock::new(HashMap::new()),
            ttl,
            max_size,
        }
    }
    
    pub fn get(&self, key: &str) -> Option<ResponseData> {
        let cache = self.cache.read().unwrap();
        if let Some(item) = cache.get(key) {
            if item.timestamp.elapsed() < self.ttl {
                return Some(item.data.clone());
            }
        }
        None
    }
    
    pub fn set(&self, key: String, data: ResponseData) {
        let mut cache = self.cache.write().unwrap();
        
        // 清理过期项
        cache.retain(|_, item| item.timestamp.elapsed() < self.ttl);
        
        // 检查大小限制
        if cache.len() >= self.max_size {
            // 移除最旧的项
            let oldest_key = cache.iter()
                .min_by_key(|(_, item)| item.timestamp)
                .map(|(k, _)| k.clone());
            
            if let Some(key_to_remove) = oldest_key {
                cache.remove(&key_to_remove);
            }
        }
        
        cache.insert(key, CachedItem {
            data,
            timestamp: Instant::now(),
        });
    }
}
```

### 5.2 连接池

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

pub struct ConnectionPool {
    semaphore: Arc<Semaphore>,
    max_connections: usize,
}

impl ConnectionPool {
    pub fn new(max_connections: usize) -> Self {
        ConnectionPool {
            semaphore: Arc::new(Semaphore::new(max_connections)),
            max_connections,
        }
    }
    
    pub async fn acquire(&self) -> Result<ConnectionGuard, AdapterError> {
        let permit = self.semaphore.acquire().await
            .map_err(|_| AdapterError::Connection("Failed to acquire connection".to_string()))?;
        
        Ok(ConnectionGuard { permit })
    }
}

pub struct ConnectionGuard<'a> {
    permit: tokio::sync::SemaphorePermit<'a>,
}

impl<'a> Drop for ConnectionGuard<'a> {
    fn drop(&mut self) {
        // 自动释放连接
    }
}
```

## 6. 应用场景

### 6.1 数据库适配器

```rust
// 数据库适配器示例
pub trait DatabaseInterface {
    async fn query(&self, sql: &str) -> Result<QueryResult, DatabaseError>;
    async fn execute(&self, sql: &str) -> Result<ExecuteResult, DatabaseError>;
    async fn transaction<F, R>(&self, f: F) -> Result<R, DatabaseError>
    where F: FnOnce(&dyn DatabaseInterface) -> Result<R, DatabaseError>;
}

pub struct PostgresAdapter {
    connection: postgres::Client,
    cache: AdapterCache,
}

#[async_trait]
impl DatabaseInterface for PostgresAdapter {
    async fn query(&self, sql: &str) -> Result<QueryResult, DatabaseError> {
        // 检查缓存
        if let Some(cached) = self.cache.get(sql) {
            return Ok(cached);
        }
        
        // 执行查询
        let result = self.connection.query(sql, &[]).await
            .map_err(|e| DatabaseError::Query(e.to_string()))?;
        
        // 缓存结果
        let query_result = QueryResult::from_rows(result);
        self.cache.set(sql.to_string(), query_result.clone());
        
        Ok(query_result)
    }
    
    async fn execute(&self, sql: &str) -> Result<ExecuteResult, DatabaseError> {
        let result = self.connection.execute(sql, &[]).await
            .map_err(|e| DatabaseError::Execute(e.to_string()))?;
        
        Ok(ExecuteResult { affected_rows: result })
    }
    
    async fn transaction<F, R>(&self, f: F) -> Result<R, DatabaseError>
    where F: FnOnce(&dyn DatabaseInterface) -> Result<R, DatabaseError>
    {
        let mut transaction = self.connection.transaction().await
            .map_err(|e| DatabaseError::Transaction(e.to_string()))?;
        
        let result = f(&PostgresAdapter { 
            connection: transaction.client().clone(),
            cache: self.cache.clone(),
        })?;
        
        transaction.commit().await
            .map_err(|e| DatabaseError::Transaction(e.to_string()))?;
        
        Ok(result)
    }
}
```

### 6.2 API适配器

```rust
// API适配器示例
pub trait ApiInterface {
    async fn get(&self, path: &str) -> Result<ApiResponse, ApiError>;
    async fn post(&self, path: &str, data: &ApiRequest) -> Result<ApiResponse, ApiError>;
    async fn put(&self, path: &str, data: &ApiRequest) -> Result<ApiResponse, ApiError>;
    async fn delete(&self, path: &str) -> Result<ApiResponse, ApiError>;
}

pub struct RestApiAdapter {
    client: reqwest::Client,
    base_url: String,
    auth_token: Option<String>,
    cache: AdapterCache,
}

#[async_trait]
impl ApiInterface for RestApiAdapter {
    async fn get(&self, path: &str) -> Result<ApiResponse, ApiError> {
        let url = format!("{}{}", self.base_url, path);
        
        // 检查缓存
        if let Some(cached) = self.cache.get(&url) {
            return Ok(cached);
        }
        
        let mut request = self.client.get(&url);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await
            .map_err(|e| ApiError::Network(e.to_string()))?;
        
        let api_response = ApiResponse::from_response(response).await?;
        
        // 缓存响应
        self.cache.set(url, api_response.clone());
        
        Ok(api_response)
    }
    
    async fn post(&self, path: &str, data: &ApiRequest) -> Result<ApiResponse, ApiError> {
        let url = format!("{}{}", self.base_url, path);
        
        let mut request = self.client.post(&url)
            .json(data);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await
            .map_err(|e| ApiError::Network(e.to_string()))?;
        
        ApiResponse::from_response(response).await
    }
    
    async fn put(&self, path: &str, data: &ApiRequest) -> Result<ApiResponse, ApiError> {
        let url = format!("{}{}", self.base_url, path);
        
        let mut request = self.client.put(&url)
            .json(data);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await
            .map_err(|e| ApiError::Network(e.to_string()))?;
        
        ApiResponse::from_response(response).await
    }
    
    async fn delete(&self, path: &str) -> Result<ApiResponse, ApiError> {
        let url = format!("{}{}", self.base_url, path);
        
        let mut request = self.client.delete(&url);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await
            .map_err(|e| ApiError::Network(e.to_string()))?;
        
        ApiResponse::from_response(response).await
    }
}
```

## 7. 最佳实践

### 7.1 设计原则

1. **保持简单**：适配器应该简单明了，避免过度复杂
2. **单一职责**：每个适配器只负责一个特定的接口转换
3. **可测试性**：设计适配器时要考虑可测试性
4. **可扩展性**：支持配置驱动的适配器设计

### 7.2 性能考虑

1. **缓存策略**：合理使用缓存减少重复转换
2. **连接池**：对于网络适配器使用连接池
3. **异步处理**：支持异步操作提高并发性能
4. **资源管理**：正确管理内存和连接资源

### 7.3 错误处理

1. **错误转换**：将底层错误转换为统一的错误类型
2. **重试机制**：实现智能重试策略
3. **降级处理**：提供降级方案保证系统可用性
4. **监控告警**：建立完善的监控和告警机制

### 7.4 安全考虑

1. **输入验证**：验证所有输入数据
2. **权限控制**：实现适当的权限控制
3. **数据加密**：对敏感数据进行加密
4. **审计日志**：记录关键操作日志

## 8. 总结

适配器模式是一个强大的结构型设计模式，它通过提供统一的接口来解决系统集成中的兼容性问题。通过本文档的详细阐述，我们建立了：

1. **完整的理论基础**：包括形式化定义和语义模型
2. **多语言实现**：Rust、Haskell、Lean的完整实现
3. **工程实践**：包括架构设计、配置管理、错误处理
4. **性能优化**：缓存策略、连接池等优化方案
5. **应用场景**：数据库适配器、API适配器等实际应用
6. **最佳实践**：设计原则、性能考虑、安全考虑等

这些内容为适配器模式的实际应用提供了全面的指导，确保在实际项目中能够正确、高效地使用适配器模式。
