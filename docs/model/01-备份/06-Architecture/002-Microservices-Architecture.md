# 微服务架构

## 概述

微服务架构是一种软件架构模式，将应用程序构建为一组小型、独立的服务。本文档探讨函数式编程在微服务架构中的应用，以及如何使用Haskell、Rust和Lean构建可靠的微服务系统。

## 微服务架构原则

### 1. 服务边界设计

```haskell
-- 领域边界清晰定义
{-# LANGUAGE GADTs #-}

-- 服务接口定义
data ServiceInterface m where
  UserService :: UserServiceAPI m => ServiceInterface m
  OrderService :: OrderServiceAPI m => ServiceInterface m
  PaymentService :: PaymentServiceAPI m => ServiceInterface m

-- 用户服务API
class Monad m => UserServiceAPI m where
  createUser :: CreateUserRequest -> m (Either UserError User)
  getUser :: UserId -> m (Maybe User)
  updateUser :: UserId -> UpdateUserRequest -> m (Either UserError User)
  deleteUser :: UserId -> m (Either UserError ())

-- 订单服务API
class Monad m => OrderServiceAPI m where
  createOrder :: CreateOrderRequest -> m (Either OrderError Order)
  getOrder :: OrderId -> m (Maybe Order)
  listUserOrders :: UserId -> m [Order]
  updateOrderStatus :: OrderId -> OrderStatus -> m (Either OrderError Order)

-- 服务依赖图
data ServiceDependency = ServiceDependency
  { fromService :: ServiceName
  , toService :: ServiceName
  , dependencyType :: DependencyType
  } deriving (Show, Eq)

data DependencyType = Synchronous | Asynchronous | EventDriven
  deriving (Show, Eq)

newtype ServiceName = ServiceName Text deriving (Show, Eq)

-- 循环依赖检测
detectCycles :: [ServiceDependency] -> [ServiceName]
detectCycles deps = 
  let graph = buildGraph deps
  in findCycles graph

buildGraph :: [ServiceDependency] -> Map ServiceName [ServiceName]
buildGraph = foldr addEdge Map.empty
  where
    addEdge (ServiceDependency from to _) = 
      Map.insertWith (++) from [to]
```

### 2. 数据隔离

```rust
// 每个服务的数据库抽象
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use sqlx::{Database, Pool};

// 数据访问层抽象
#[async_trait]
pub trait Repository<T> {
    type Error;
    type Id;
    
    async fn create(&self, entity: T) -> Result<T, Self::Error>;
    async fn find_by_id(&self, id: Self::Id) -> Result<Option<T>, Self::Error>;
    async fn update(&self, entity: T) -> Result<T, Self::Error>;
    async fn delete(&self, id: Self::Id) -> Result<(), Self::Error>;
}

// 用户仓储实现
pub struct UserRepository {
    pool: Pool<sqlx::Postgres>,
}

#[async_trait]
impl Repository<User> for UserRepository {
    type Error = sqlx::Error;
    type Id = UserId;
    
    async fn create(&self, user: User) -> Result<User, Self::Error> {
        sqlx::query_as!(
            User,
            "INSERT INTO users (id, email, name) VALUES ($1, $2, $3) RETURNING *",
            user.id.0,
            user.email,
            user.name
        )
        .fetch_one(&self.pool)
        .await
    }
    
    async fn find_by_id(&self, id: Self::Id) -> Result<Option<User>, Self::Error> {
        sqlx::query_as!(
            User,
            "SELECT * FROM users WHERE id = $1",
            id.0
        )
        .fetch_optional(&self.pool)
        .await
    }
    
    async fn update(&self, user: User) -> Result<User, Self::Error> {
        sqlx::query_as!(
            User,
            "UPDATE users SET email = $2, name = $3 WHERE id = $1 RETURNING *",
            user.id.0,
            user.email,
            user.name
        )
        .fetch_one(&self.pool)
        .await
    }
    
    async fn delete(&self, id: Self::Id) -> Result<(), Self::Error> {
        sqlx::query!(
            "DELETE FROM users WHERE id = $1",
            id.0
        )
        .execute(&self.pool)
        .await?;
        Ok(())
    }
}

// 数据库连接管理
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub database: String,
    pub username: String,
    pub password: String,
    pub max_connections: u32,
}

impl DatabaseConfig {
    pub async fn create_pool(&self) -> Result<Pool<sqlx::Postgres>, sqlx::Error> {
        let connection_string = format!(
            "postgres://{}:{}@{}:{}/{}",
            self.username, self.password, self.host, self.port, self.database
        );
        
        sqlx::postgres::PgPoolOptions::new()
            .max_connections(self.max_connections)
            .connect(&connection_string)
            .await
    }
}
```

## 服务间通信

### 1. 同步通信

```haskell
-- HTTP客户端
{-# LANGUAGE OverloadedStrings #-}

import Network.HTTP.Simple
import Data.Aeson

-- 服务发现
data ServiceRegistry = ServiceRegistry
  { services :: Map ServiceName ServiceEndpoint
  , healthChecks :: Map ServiceName HealthStatus
  } deriving (Show)

data ServiceEndpoint = ServiceEndpoint
  { host :: Text
  , port :: Int
  , protocol :: Protocol
  } deriving (Show)

data Protocol = HTTP | HTTPS deriving (Show)
data HealthStatus = Healthy | Unhealthy | Unknown deriving (Show)

-- 服务客户端
class Monad m => ServiceClient m where
  callService :: ServiceName -> RequestPath -> RequestBody -> m (Either ServiceError ResponseBody)
  
data ServiceError = 
  ServiceUnavailable |
  NetworkError Text |
  DeserializationError Text |
  Timeout
  deriving (Show)

-- HTTP服务调用
callUserService :: UserId -> IO (Either ServiceError User)
callUserService userId = do
  registry <- getServiceRegistry
  case Map.lookup "user-service" (services registry) of
    Nothing -> return $ Left ServiceUnavailable
    Just endpoint -> do
      request <- parseRequest $ buildURL endpoint ("/users/" <> show userId)
      response <- httpJSON request
      return $ case getResponseStatusCode response of
        200 -> Right $ getResponseBody response
        404 -> Left ServiceUnavailable
        _ -> Left $ NetworkError "Unexpected status code"

-- 熔断器模式
data CircuitBreakerState = Closed | Open | HalfOpen
  deriving (Show, Eq)

data CircuitBreaker = CircuitBreaker
  { state :: CircuitBreakerState
  , failureCount :: Int
  , failureThreshold :: Int
  , timeout :: NominalDiffTime
  , lastFailureTime :: Maybe UTCTime
  } deriving (Show)

-- 熔断器逻辑
executeWithCircuitBreaker :: CircuitBreaker -> IO a -> IO (Either ServiceError a)
executeWithCircuitBreaker breaker action = 
  case state breaker of
    Open -> checkTimeout breaker
    Closed -> executeAction breaker action
    HalfOpen -> executeAction breaker action
  where
    checkTimeout cb = do
      now <- getCurrentTime
      case lastFailureTime cb of
        Just lastFailure | diffUTCTime now lastFailure > timeout cb ->
          executeAction cb { state = HalfOpen } action
        _ -> return $ Left ServiceUnavailable
    
    executeAction cb action = do
      result <- try action
      case result of
        Right value -> return $ Right value
        Left _ -> return $ Left ServiceUnavailable
```

### 2. 异步通信

```rust
// 事件驱动架构
use serde::{Deserialize, Serialize};
use tokio::sync::mpsc;
use std::collections::HashMap;

// 领域事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DomainEvent {
    UserCreated {
        user_id: UserId,
        email: String,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
    UserUpdated {
        user_id: UserId,
        changes: UserChanges,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
    OrderPlaced {
        order_id: OrderId,
        user_id: UserId,
        total_amount: Decimal,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
    PaymentProcessed {
        payment_id: PaymentId,
        order_id: OrderId,
        amount: Decimal,
        status: PaymentStatus,
        timestamp: chrono::DateTime<chrono::Utc>,
    },
}

// 事件发布器
#[async_trait]
pub trait EventPublisher {
    async fn publish(&self, event: DomainEvent) -> Result<(), PublishError>;
    async fn publish_batch(&self, events: Vec<DomainEvent>) -> Result<(), PublishError>;
}

// 事件订阅器
#[async_trait]
pub trait EventSubscriber {
    async fn subscribe(&self, event_type: &str) -> Result<mpsc::Receiver<DomainEvent>, SubscribeError>;
    async fn unsubscribe(&self, subscription_id: &str) -> Result<(), SubscribeError>;
}

// Redis事件总线实现
pub struct RedisEventBus {
    client: redis::Client,
    connection: redis::aio::Connection,
}

impl RedisEventBus {
    pub async fn new(redis_url: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        let connection = client.get_async_connection().await?;
        
        Ok(Self { client, connection })
    }
}

#[async_trait]
impl EventPublisher for RedisEventBus {
    async fn publish(&self, event: DomainEvent) -> Result<(), PublishError> {
        let event_type = match &event {
            DomainEvent::UserCreated { .. } => "user.created",
            DomainEvent::UserUpdated { .. } => "user.updated",
            DomainEvent::OrderPlaced { .. } => "order.placed",
            DomainEvent::PaymentProcessed { .. } => "payment.processed",
        };
        
        let serialized = serde_json::to_string(&event)
            .map_err(|e| PublishError::SerializationError(e.to_string()))?;
        
        redis::cmd("PUBLISH")
            .arg(event_type)
            .arg(serialized)
            .query_async(&mut self.connection)
            .await
            .map_err(|e| PublishError::TransportError(e.to_string()))?;
        
        Ok(())
    }
    
    async fn publish_batch(&self, events: Vec<DomainEvent>) -> Result<(), PublishError> {
        let mut pipeline = redis::pipe();
        
        for event in events {
            let event_type = match &event {
                DomainEvent::UserCreated { .. } => "user.created",
                DomainEvent::UserUpdated { .. } => "user.updated", 
                DomainEvent::OrderPlaced { .. } => "order.placed",
                DomainEvent::PaymentProcessed { .. } => "payment.processed",
            };
            
            let serialized = serde_json::to_string(&event)
                .map_err(|e| PublishError::SerializationError(e.to_string()))?;
            
            pipeline.cmd("PUBLISH").arg(event_type).arg(serialized);
        }
        
        pipeline.query_async(&mut self.connection)
            .await
            .map_err(|e| PublishError::TransportError(e.to_string()))?;
        
        Ok(())
    }
}

// 事件处理器
#[async_trait]
pub trait EventHandler {
    async fn handle(&self, event: DomainEvent) -> Result<(), EventHandlingError>;
    fn event_types(&self) -> Vec<&'static str>;
}

// 用户服务事件处理器
pub struct UserEventHandler {
    user_repository: Arc<dyn Repository<User, Error = sqlx::Error, Id = UserId>>,
    notification_service: Arc<dyn NotificationService>,
}

#[async_trait]
impl EventHandler for UserEventHandler {
    async fn handle(&self, event: DomainEvent) -> Result<(), EventHandlingError> {
        match event {
            DomainEvent::UserCreated { user_id, email, .. } => {
                // 发送欢迎邮件
                self.notification_service
                    .send_welcome_email(&email)
                    .await
                    .map_err(|e| EventHandlingError::ServiceError(e.to_string()))?;
                
                // 更新用户统计
                // ...
                
                Ok(())
            }
            DomainEvent::OrderPlaced { user_id, total_amount, .. } => {
                // 更新用户订单历史
                // ...
                
                Ok(())
            }
            _ => Ok(()), // 忽略不相关的事件
        }
    }
    
    fn event_types(&self) -> Vec<&'static str> {
        vec!["user.created", "order.placed"]
    }
}

// 错误类型
#[derive(Debug, thiserror::Error)]
pub enum PublishError {
    #[error("Serialization error: {0}")]
    SerializationError(String),
    #[error("Transport error: {0}")]
    TransportError(String),
}

#[derive(Debug, thiserror::Error)]
pub enum SubscribeError {
    #[error("Connection error: {0}")]
    ConnectionError(String),
    #[error("Invalid event type: {0}")]
    InvalidEventType(String),
}

#[derive(Debug, thiserror::Error)]
pub enum EventHandlingError {
    #[error("Service error: {0}")]
    ServiceError(String),
    #[error("Data error: {0}")]
    DataError(String),
}
```

## 数据一致性

### 1. Saga模式

```haskell
-- Saga编排模式
{-# LANGUAGE GADTs, TypeFamilies #-}

-- Saga步骤定义
data SagaStep m where
  Step :: (Show a, Show b) => Text -> (a -> m (Either err b)) -> (b -> m ()) -> SagaStep m

-- Saga定义
data Saga m = Saga
  { sagaId :: SagaId
  , steps :: [SagaStep m]
  , compensations :: [m ()]
  } deriving (Show)

newtype SagaId = SagaId Text deriving (Show, Eq)

-- Saga执行器
class Monad m => SagaExecutor m where
  executeSaga :: Saga m -> m (Either SagaError SagaResult)
  
data SagaError = 
  StepFailed Text |
  CompensationFailed Text |
  SagaTimeout
  deriving (Show)

data SagaResult = SagaCompleted | SagaCompensated
  deriving (Show)

-- 订单处理Saga
orderProcessingSaga :: UserId -> OrderData -> Saga IO
orderProcessingSaga userId orderData = Saga
  { sagaId = SagaId "order-processing"
  , steps = 
    [ Step "validate-user" (validateUser userId) (const $ return ())
    , Step "create-order" (createOrder orderData) cancelOrder
    , Step "process-payment" (processPayment orderData) refundPayment
    , Step "update-inventory" (updateInventory orderData) restoreInventory
    , Step "send-confirmation" (sendConfirmation userId) (const $ return ())
    ]
  , compensations = []
  }

-- Saga步骤实现
validateUser :: UserId -> IO (Either UserError User)
validateUser userId = do
  -- 调用用户服务验证用户
  result <- callService "user-service" ("/users/" <> show userId) ""
  case result of
    Right user -> return $ Right user
    Left err -> return $ Left $ UserNotFound userId

createOrder :: OrderData -> IO (Either OrderError Order)
createOrder orderData = do
  -- 调用订单服务创建订单
  result <- callService "order-service" "/orders" (encode orderData)
  case result of
    Right order -> return $ Right order
    Left err -> return $ Left $ OrderCreationFailed err

processPayment :: OrderData -> IO (Either PaymentError PaymentResult)
processPayment orderData = do
  -- 调用支付服务处理支付
  result <- callService "payment-service" "/payments" (encode orderData)
  case result of
    Right payment -> return $ Right payment
    Left err -> return $ Left $ PaymentFailed err

-- 补偿操作
cancelOrder :: Order -> IO ()
cancelOrder order = do
  void $ callService "order-service" ("/orders/" <> show (orderId order) <> "/cancel") ""

refundPayment :: PaymentResult -> IO ()
refundPayment payment = do
  void $ callService "payment-service" ("/payments/" <> show (paymentId payment) <> "/refund") ""

restoreInventory :: InventoryUpdate -> IO ()
restoreInventory update = do
  void $ callService "inventory-service" "/inventory/restore" (encode update)
```

### 2. 事件溯源

```rust
// 事件溯源实现
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

// 事件存储
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    pub aggregate_id: AggregateId,
    pub event_type: String,
    pub event_data: serde_json::Value,
    pub event_version: u64,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub metadata: BTreeMap<String, String>,
}

// 聚合根
pub trait Aggregate {
    type Event;
    type Error;
    
    fn apply_event(&mut self, event: &Self::Event) -> Result<(), Self::Error>;
    fn get_uncommitted_events(&self) -> &[Self::Event];
    fn mark_events_as_committed(&mut self);
}

// 事件存储接口
#[async_trait]
pub trait EventStore {
    async fn save_events(
        &self,
        aggregate_id: &AggregateId,
        events: &[Event],
        expected_version: Option<u64>,
    ) -> Result<(), EventStoreError>;
    
    async fn get_events(
        &self,
        aggregate_id: &AggregateId,
        from_version: Option<u64>,
    ) -> Result<Vec<Event>, EventStoreError>;
    
    async fn get_all_events_from(
        &self,
        checkpoint: Option<u64>,
    ) -> Result<Vec<Event>, EventStoreError>;
}

// 聚合仓储
pub struct EventSourcedRepository<T> {
    event_store: Arc<dyn EventStore>,
    _phantom: PhantomData<T>,
}

impl<T> EventSourcedRepository<T>
where
    T: Aggregate + Default,
{
    pub fn new(event_store: Arc<dyn EventStore>) -> Self {
        Self {
            event_store,
            _phantom: PhantomData,
        }
    }
    
    pub async fn get_by_id(&self, id: &AggregateId) -> Result<Option<T>, EventStoreError> {
        let events = self.event_store.get_events(id, None).await?;
        
        if events.is_empty() {
            return Ok(None);
        }
        
        let mut aggregate = T::default();
        for event in events {
            // 反序列化事件并应用到聚合
            let domain_event = self.deserialize_event(&event)?;
            aggregate.apply_event(&domain_event)
                .map_err(|_| EventStoreError::AggregateError)?;
        }
        
        Ok(Some(aggregate))
    }
    
    pub async fn save(&self, aggregate: &mut T, id: &AggregateId) -> Result<(), EventStoreError> {
        let uncommitted_events = aggregate.get_uncommitted_events();
        
        if uncommitted_events.is_empty() {
            return Ok(());
        }
        
        // 序列化事件
        let events: Vec<Event> = uncommitted_events
            .iter()
            .enumerate()
            .map(|(i, event)| self.serialize_event(id, event, i as u64))
            .collect::<Result<Vec<_>, _>>()?;
        
        // 保存事件
        self.event_store.save_events(id, &events, None).await?;
        
        // 标记事件为已提交
        aggregate.mark_events_as_committed();
        
        Ok(())
    }
    
    fn serialize_event(&self, aggregate_id: &AggregateId, event: &T::Event, version: u64) -> Result<Event, EventStoreError> {
        // 实现事件序列化逻辑
        todo!()
    }
    
    fn deserialize_event(&self, event: &Event) -> Result<T::Event, EventStoreError> {
        // 实现事件反序列化逻辑
        todo!()
    }
}

// 投影
#[async_trait]
pub trait Projection {
    async fn handle_event(&mut self, event: &Event) -> Result<(), ProjectionError>;
}

// 用户投影示例
pub struct UserProjection {
    database: Arc<sqlx::PgPool>,
}

#[async_trait]
impl Projection for UserProjection {
    async fn handle_event(&mut self, event: &Event) -> Result<(), ProjectionError> {
        match event.event_type.as_str() {
            "UserCreated" => {
                let user_data: UserCreatedData = serde_json::from_value(event.event_data.clone())
                    .map_err(|e| ProjectionError::DeserializationError(e.to_string()))?;
                
                sqlx::query!(
                    "INSERT INTO user_projection (id, email, name, created_at) VALUES ($1, $2, $3, $4)",
                    event.aggregate_id.0,
                    user_data.email,
                    user_data.name,
                    event.timestamp
                )
                .execute(&*self.database)
                .await
                .map_err(|e| ProjectionError::DatabaseError(e.to_string()))?;
            }
            "UserUpdated" => {
                let update_data: UserUpdatedData = serde_json::from_value(event.event_data.clone())
                    .map_err(|e| ProjectionError::DeserializationError(e.to_string()))?;
                
                sqlx::query!(
                    "UPDATE user_projection SET email = $2, name = $3, updated_at = $4 WHERE id = $1",
                    event.aggregate_id.0,
                    update_data.email,
                    update_data.name,
                    event.timestamp
                )
                .execute(&*self.database)
                .await
                .map_err(|e| ProjectionError::DatabaseError(e.to_string()))?;
            }
            _ => {} // 忽略不相关的事件
        }
        
        Ok(())
    }
}

// 错误类型
#[derive(Debug, thiserror::Error)]
pub enum EventStoreError {
    #[error("Concurrency conflict")]
    ConcurrencyConflict,
    #[error("Aggregate error")]
    AggregateError,
    #[error("Serialization error: {0}")]
    SerializationError(String),
}

#[derive(Debug, thiserror::Error)]
pub enum ProjectionError {
    #[error("Database error: {0}")]
    DatabaseError(String),
    #[error("Deserialization error: {0}")]
    DeserializationError(String),
}
```

## 可观测性

### 1. 分布式追踪

```haskell
-- 分布式追踪实现
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID

-- 追踪上下文
data TraceContext = TraceContext
  { traceId :: TraceId
  , spanId :: SpanId
  , parentSpanId :: Maybe SpanId
  , baggage :: Map Text Text
  } deriving (Show)

newtype TraceId = TraceId UUID.UUID deriving (Show, Eq)
newtype SpanId = SpanId UUID.UUID deriving (Show, Eq)

-- Span定义
data Span = Span
  { spanTraceId :: TraceId
  , spanId :: SpanId
  , spanParentId :: Maybe SpanId
  , operationName :: Text
  , startTime :: UTCTime
  , endTime :: Maybe UTCTime
  , tags :: Map Text Text
  , logs :: [LogEntry]
  } deriving (Show)

data LogEntry = LogEntry
  { timestamp :: UTCTime
  , fields :: Map Text Text
  } deriving (Show)

-- 追踪Monad
newtype TracedT m a = TracedT { runTracedT :: ReaderT TraceContext m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader TraceContext)

-- 追踪操作
class Monad m => Traced m where
  startSpan :: Text -> m Span
  finishSpan :: Span -> m ()
  addTag :: Text -> Text -> m ()
  addLog :: Text -> m ()
  getCurrentContext :: m TraceContext

instance MonadIO m => Traced (TracedT m) where
  startSpan name = do
    context <- ask
    spanId <- liftIO $ SpanId <$> UUID.nextRandom
    startTime <- liftIO getCurrentTime
    let span = Span
          { spanTraceId = traceId context
          , spanId = spanId
          , spanParentId = Just (spanId context)
          , operationName = name
          , startTime = startTime
          , endTime = Nothing
          , tags = Map.empty
          , logs = []
          }
    return span

-- HTTP中间件追踪
traceHttpRequest :: Traced m => Request -> m Response -> m Response
traceHttpRequest req action = do
  span <- startSpan ("HTTP " <> requestMethod req <> " " <> requestPath req)
  addTag "http.method" (requestMethod req)
  addTag "http.url" (requestPath req)
  
  startTime <- liftIO getCurrentTime
  result <- action `catch` \ex -> do
    addTag "error" "true"
    addLog ("Exception: " <> show ex)
    throwM ex
  
  endTime <- liftIO getCurrentTime
  addTag "http.status_code" (show $ responseStatus result)
  addTag "duration_ms" (show $ diffUTCTime endTime startTime * 1000)
  
  finishSpan span
  return result
```

### 2. 指标收集

```rust
// Prometheus指标收集
use prometheus::{Counter, Histogram, Gauge, Registry};
use std::sync::Arc;
use tokio::time::Instant;

// 服务指标
#[derive(Clone)]
pub struct ServiceMetrics {
    request_counter: Counter,
    request_duration: Histogram,
    active_connections: Gauge,
    error_counter: Counter,
}

impl ServiceMetrics {
    pub fn new(registry: &Registry) -> Result<Self, prometheus::Error> {
        let request_counter = Counter::new(
            "http_requests_total",
            "Total number of HTTP requests",
        )?;
        registry.register(Box::new(request_counter.clone()))?;
        
        let request_duration = Histogram::with_opts(
            prometheus::HistogramOpts::new(
                "http_request_duration_seconds",
                "HTTP request duration in seconds",
            ).buckets(vec![0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0]),
        )?;
        registry.register(Box::new(request_duration.clone()))?;
        
        let active_connections = Gauge::new(
            "active_connections",
            "Number of active connections",
        )?;
        registry.register(Box::new(active_connections.clone()))?;
        
        let error_counter = Counter::new(
            "http_errors_total",
            "Total number of HTTP errors",
        )?;
        registry.register(Box::new(error_counter.clone()))?;
        
        Ok(Self {
            request_counter,
            request_duration,
            active_connections,
            error_counter,
        })
    }
    
    pub fn record_request(&self, duration: f64, status_code: u16) {
        self.request_counter.inc();
        self.request_duration.observe(duration);
        
        if status_code >= 400 {
            self.error_counter.inc();
        }
    }
    
    pub fn increment_active_connections(&self) {
        self.active_connections.inc();
    }
    
    pub fn decrement_active_connections(&self) {
        self.active_connections.dec();
    }
}

// 指标中间件
pub async fn metrics_middleware<B>(
    request: axum::http::Request<B>,
    next: axum::middleware::Next<B>,
) -> axum::response::Response {
    let start = Instant::now();
    let method = request.method().clone();
    let path = request.uri().path().to_string();
    
    // 从请求扩展中获取指标
    let metrics = request.extensions().get::<Arc<ServiceMetrics>>().cloned();
    
    if let Some(metrics) = &metrics {
        metrics.increment_active_connections();
    }
    
    let response = next.run(request).await;
    let duration = start.elapsed().as_secs_f64();
    let status_code = response.status().as_u16();
    
    if let Some(metrics) = &metrics {
        metrics.record_request(duration, status_code);
        metrics.decrement_active_connections();
    }
    
    response
}

// 健康检查端点
pub async fn health_check() -> axum::response::Json<serde_json::Value> {
    axum::response::Json(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339(),
        "uptime": get_uptime_seconds(),
        "version": env!("CARGO_PKG_VERSION")
    }))
}

// 指标端点
pub async fn metrics_endpoint(
    registry: axum::extract::Extension<Arc<Registry>>,
) -> Result<String, (axum::http::StatusCode, String)> {
    let encoder = prometheus::TextEncoder::new();
    let metric_families = registry.gather();
    
    encoder.encode_to_string(&metric_families)
        .map_err(|e| (
            axum::http::StatusCode::INTERNAL_SERVER_ERROR,
            format!("Failed to encode metrics: {}", e)
        ))
}
```

## 部署和运维

### 1. 容器化

```dockerfile
# 多阶段构建Dockerfile (Rust服务)
FROM rust:1.70 as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 构建发布版本
RUN cargo build --release

# 运行时镜像
FROM debian:bullseye-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN useradd -r -s /bin/false appuser

# 复制二进制文件
COPY --from=builder /app/target/release/my-service /usr/local/bin/my-service

# 切换到非root用户
USER appuser

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["my-service"]
```

### 2. Kubernetes部署

```yaml
# Kubernetes部署配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: user-service
  labels:
    app: user-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: user-service
  template:
    metadata:
      labels:
        app: user-service
    spec:
      containers:
      - name: user-service
        image: myregistry/user-service:v1.0.0
        ports:
        - containerPort: 8080
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-secret
              key: url
        - name: REDIS_URL
          value: "redis://redis-service:6379"
        resources:
          requests:
            memory: "64Mi"
            cpu: "250m"
          limits:
            memory: "128Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
        volumeMounts:
        - name: config-volume
          mountPath: /etc/config
      volumes:
      - name: config-volume
        configMap:
          name: user-service-config

---
apiVersion: v1
kind: Service
metadata:
  name: user-service
spec:
  selector:
    app: user-service
  ports:
    - protocol: TCP
      port: 80
      targetPort: 8080
  type: ClusterIP

---
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: user-service-ingress
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
spec:
  rules:
  - host: api.example.com
    http:
      paths:
      - path: /users
        pathType: Prefix
        backend:
          service:
            name: user-service
            port:
              number: 80
```

## 安全性

### 1. 认证授权

```haskell
-- JWT认证
{-# LANGUAGE OverloadedStrings #-}

import qualified Web.JWT as JWT
import qualified Crypto.JWT as JOSE

-- JWT Claims
data UserClaims = UserClaims
  { userId :: UserId
  , roles :: [Role]
  , permissions :: [Permission]
  , issuer :: Text
  , audience :: Text
  , expiresAt :: UTCTime
  } deriving (Show, Generic)

instance ToJSON UserClaims
instance FromJSON UserClaims

-- 角色和权限
data Role = Admin | User | Guest deriving (Show, Eq, Generic)
data Permission = ReadUsers | WriteUsers | ReadOrders | WriteOrders
  deriving (Show, Eq, Generic)

instance ToJSON Role
instance FromJSON Role
instance ToJSON Permission  
instance FromJSON Permission

-- JWT服务
class Monad m => JWTService m where
  generateToken :: UserClaims -> m (Either JWTError Text)
  validateToken :: Text -> m (Either JWTError UserClaims)
  
data JWTError = 
  InvalidToken |
  ExpiredToken |
  InvalidSignature |
  MissingClaims
  deriving (Show)

-- 认证中间件
authenticateRequest :: JWTService m => Request -> m (Either AuthError AuthenticatedRequest)
authenticateRequest request = do
  case extractBearerToken request of
    Nothing -> return $ Left MissingToken
    Just token -> do
      result <- validateToken token
      case result of
        Left jwtErr -> return $ Left $ InvalidToken jwtErr
        Right claims -> return $ Right $ AuthenticatedRequest request claims

data AuthError = 
  MissingToken |
  InvalidToken JWTError |
  InsufficientPermissions
  deriving (Show)

data AuthenticatedRequest = AuthenticatedRequest
  { originalRequest :: Request
  , userClaims :: UserClaims
  } deriving (Show)

-- 权限检查
requirePermission :: Permission -> AuthenticatedRequest -> Either AuthError AuthenticatedRequest
requirePermission perm authReq = 
  if perm `elem` permissions (userClaims authReq)
  then Right authReq
  else Left InsufficientPermissions

-- RBAC实现
data RBAC = RBAC
  { rolePermissions :: Map Role [Permission]
  , userRoles :: Map UserId [Role]
  } deriving (Show)

hasPermission :: RBAC -> UserId -> Permission -> Bool
hasPermission rbac userId perm = 
  let userRoleList = fromMaybe [] $ Map.lookup userId (userRoles rbac)
      allPermissions = concatMap (\role -> fromMaybe [] $ Map.lookup role (rolePermissions rbac)) userRoleList
  in perm `elem` allPermissions
```

### 2. 网络安全

```rust
// TLS配置和网络安全
use rustls::{Certificate, PrivateKey, ServerConfig};
use std::fs::File;
use std::io::BufReader;

// TLS配置
pub fn create_tls_config(cert_path: &str, key_path: &str) -> Result<ServerConfig, Box<dyn std::error::Error>> {
    let cert_file = File::open(cert_path)?;
    let mut cert_reader = BufReader::new(cert_file);
    let certs = rustls_pemfile::certs(&mut cert_reader)?
        .into_iter()
        .map(Certificate)
        .collect();

    let key_file = File::open(key_path)?;
    let mut key_reader = BufReader::new(key_file);
    let keys = rustls_pemfile::pkcs8_private_keys(&mut key_reader)?
        .into_iter()
        .map(PrivateKey)
        .collect::<Vec<_>>();

    let key = keys.into_iter().next()
        .ok_or("No private key found")?;

    let config = ServerConfig::builder()
        .with_safe_defaults()
        .with_no_client_auth()
        .with_single_cert(certs, key)?;

    Ok(config)
}

// 请求限流
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct RateLimiter {
    limits: Arc<RwLock<HashMap<String, RateLimit>>>,
    requests_per_minute: usize,
    window_size: Duration,
}

struct RateLimit {
    count: usize,
    window_start: Instant,
}

impl RateLimiter {
    pub fn new(requests_per_minute: usize) -> Self {
        Self {
            limits: Arc::new(RwLock::new(HashMap::new())),
            requests_per_minute,
            window_size: Duration::from_secs(60),
        }
    }
    
    pub async fn check_rate_limit(&self, client_id: &str) -> bool {
        let mut limits = self.limits.write().await;
        let now = Instant::now();
        
        match limits.get_mut(client_id) {
            Some(rate_limit) => {
                // 检查窗口是否过期
                if now.duration_since(rate_limit.window_start) > self.window_size {
                    rate_limit.count = 1;
                    rate_limit.window_start = now;
                    true
                } else if rate_limit.count < self.requests_per_minute {
                    rate_limit.count += 1;
                    true
                } else {
                    false
                }
            }
            None => {
                limits.insert(client_id.to_string(), RateLimit {
                    count: 1,
                    window_start: now,
                });
                true
            }
        }
    }
}

// 输入验证和清理
use validator::{Validate, ValidationError};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Validate)]
pub struct CreateUserRequest {
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 2, max = 50))]
    pub name: String,
    
    #[validate(length(min = 8))]
    pub password: String,
}

// 安全头部中间件
pub async fn security_headers_middleware<B>(
    request: axum::http::Request<B>,
    next: axum::middleware::Next<B>,
) -> axum::response::Response {
    let mut response = next.run(request).await;
    let headers = response.headers_mut();
    
    // 添加安全头部
    headers.insert("X-Content-Type-Options", "nosniff".parse().unwrap());
    headers.insert("X-Frame-Options", "DENY".parse().unwrap());
    headers.insert("X-XSS-Protection", "1; mode=block".parse().unwrap());
    headers.insert("Strict-Transport-Security", "max-age=31536000; includeSubDomains".parse().unwrap());
    headers.insert("Content-Security-Policy", "default-src 'self'".parse().unwrap());
    
    response
}
```

## 总结

微服务架构在函数式编程环境中的核心优势：

1. **类型安全**: 编译时保证服务接口的正确性
2. **不可变性**: 减少并发问题和状态管理复杂性
3. **组合性**: 函数式编程的组合特性适合微服务的组合
4. **可测试性**: 纯函数易于单元测试和集成测试
5. **容错性**: 函数式错误处理机制提供更好的容错能力

通过结合现代微服务架构模式和函数式编程范式，我们能够构建更可靠、可维护和可扩展的分布式系统。
