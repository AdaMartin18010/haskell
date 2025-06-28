# 系统架构设计

## 概述

本文档介绍基于函数式编程的系统架构设计原则和实践。

## 架构设计原则

### 1. 函数式架构原则

#### 纯函数优先

```haskell
-- 纯函数设计
data User = User 
  { userId :: UserId
  , userName :: String
  , userEmail :: Email
  }

-- 纯函数：输入确定，输出确定
validateUser :: User -> Either ValidationError User
validateUser user = 
  case validateEmail (userEmail user) of
    Left err -> Left err
    Right _ -> Right user

-- 避免副作用
processUser :: User -> IO (Either ProcessError User)
processUser user = do
  -- 将副作用限制在IO monad中
  result <- validateUser user
  case result of
    Left err -> return (Left err)
    Right validUser -> saveUser validUser
```

#### 不可变性设计

```haskell
-- 不可变数据结构
data SystemState = SystemState
  { users :: Map UserId User
  , sessions :: Map SessionId Session
  , config :: SystemConfig
  }

-- 状态更新通过创建新状态
updateUser :: UserId -> User -> SystemState -> SystemState
updateUser uid user state = 
  state { users = Map.insert uid user (users state) }

-- 避免可变状态
type StateM a = StateT SystemState IO a
```

### 2. 类型驱动设计

#### 强类型系统

```haskell
-- 使用类型确保正确性
newtype UserId = UserId { unUserId :: UUID }
newtype Email = Email { unEmail :: String }
newtype Password = Password { unPassword :: String }

-- 类型安全的API
data UserAPI = UserAPI
  { createUser :: Email -> Password -> IO (Either UserError UserId)
  , getUser :: UserId -> IO (Either UserError User)
  , updateUser :: UserId -> User -> IO (Either UserError ())
  , deleteUser :: UserId -> IO (Either UserError ())
  }

-- 错误类型
data UserError = 
  UserNotFound UserId
  | InvalidEmail String
  | DuplicateEmail Email
  | DatabaseError String
```

#### 依赖注入

```haskell
-- 通过类型类定义接口
class Monad m => UserRepository m where
  saveUser :: User -> m (Either UserError UserId)
  findUser :: UserId -> m (Either UserError User)
  updateUser :: UserId -> User -> m (Either UserError ())
  deleteUser :: UserId -> m (Either UserError ())

-- 具体实现
newtype AppM a = AppM { runAppM :: ReaderT AppConfig IO a }

instance UserRepository AppM where
  saveUser user = AppM $ do
    config <- ask
    liftIO $ saveUserToDatabase config user
```

### 3. 分层架构

#### 领域层 (Domain Layer)

```haskell
-- 领域模型
data User = User
  { userId :: UserId
  , userName :: String
  , userEmail :: Email
  , userStatus :: UserStatus
  }

data UserStatus = Active | Inactive | Suspended

-- 领域服务
class Monad m => UserService m where
  registerUser :: Email -> Password -> m (Either UserError UserId)
  activateUser :: UserId -> m (Either UserError ())
  suspendUser :: UserId -> m (Either UserError ())

-- 领域事件
data UserEvent = 
  UserRegistered UserId Email
  | UserActivated UserId
  | UserSuspended UserId
```

#### 应用层 (Application Layer)

```haskell
-- 应用服务
newtype UserApplicationService m = UserApplicationService
  { userService :: UserService m
  , userRepository :: UserRepository m
  , eventPublisher :: EventPublisher m
  }

-- 用例实现
registerUserUseCase :: 
  UserApplicationService m -> 
  Email -> 
  Password -> 
  m (Either UserError UserId)
registerUserUseCase app email password = do
  userId <- userService app `registerUser` email `withPassword` password
  case userId of
    Left err -> return (Left err)
    Right uid -> do
      publishEvent (UserRegistered uid email)
      return (Right uid)
```

#### 基础设施层 (Infrastructure Layer)

```haskell
-- 数据库实现
newtype DatabaseUserRepository = DatabaseUserRepository
  { connection :: DatabaseConnection
  }

instance UserRepository DatabaseUserRepository where
  saveUser user = do
    conn <- asks connection
    liftIO $ executeQuery conn "INSERT INTO users ..." user

-- 事件发布实现
newtype KafkaEventPublisher = KafkaEventPublisher
  { producer :: KafkaProducer
  }

instance EventPublisher KafkaEventPublisher where
  publishEvent event = do
    prod <- asks producer
    liftIO $ sendMessage prod (serializeEvent event)
```

## 微服务架构

### 1. 服务拆分原则

#### 领域驱动设计 (DDD)

```haskell
-- 用户上下文
module UserContext where
  data User = User { ... }
  data UserService = UserService { ... }
  
-- 订单上下文
module OrderContext where
  data Order = Order { ... }
  data OrderService = OrderService { ... }
  
-- 支付上下文
module PaymentContext where
  data Payment = Payment { ... }
  data PaymentService = PaymentService { ... }
```

#### 服务边界

```haskell
-- 服务接口定义
data UserServiceAPI = UserServiceAPI
  { getUser :: UserId -> IO (Either UserError User)
  , createUser :: CreateUserRequest -> IO (Either UserError UserId)
  }

data OrderServiceAPI = OrderServiceAPI
  { createOrder :: CreateOrderRequest -> IO (Either OrderError OrderId)
  , getOrder :: OrderId -> IO (Either OrderError Order)
  }

-- 服务间通信
type ServiceCommunication = 
  UserServiceAPI -> OrderServiceAPI -> PaymentServiceAPI
```

### 2. 服务发现与注册

#### 服务注册

```haskell
-- 服务注册中心
class Monad m => ServiceRegistry m where
  registerService :: ServiceInfo -> m (Either RegistryError ())
  discoverService :: ServiceName -> m (Either RegistryError ServiceInfo)
  deregisterService :: ServiceId -> m (Either RegistryError ())

data ServiceInfo = ServiceInfo
  { serviceId :: ServiceId
  , serviceName :: ServiceName
  , serviceUrl :: URL
  , serviceHealth :: HealthStatus
  }
```

#### 负载均衡

```haskell
-- 负载均衡器
data LoadBalancer = LoadBalancer
  { strategy :: LoadBalancingStrategy
  , services :: [ServiceInfo]
  }

data LoadBalancingStrategy = 
  RoundRobin
  | LeastConnections
  | WeightedRoundRobin [Weight]

-- 负载均衡实现
balanceLoad :: LoadBalancer -> Request -> IO (Either LoadBalancerError ServiceInfo)
balanceLoad lb req = case strategy lb of
  RoundRobin -> roundRobinSelect (services lb)
  LeastConnections -> leastConnectionsSelect (services lb)
  WeightedRoundRobin weights -> weightedSelect (services lb) weights
```

### 3. 事件驱动架构

#### 事件总线

```haskell
-- 事件总线
class Monad m => EventBus m where
  publish :: Event -> m (Either EventBusError ())
  subscribe :: EventType -> EventHandler m -> m (Either EventBusError SubscriptionId)
  unsubscribe :: SubscriptionId -> m (Either EventBusError ())

-- 事件处理器
type EventHandler m = Event -> m (Either EventHandlerError ())

-- 事件类型
data Event = 
  UserCreated UserId
  | OrderPlaced OrderId UserId
  | PaymentProcessed PaymentId OrderId
```

#### 事件溯源

```haskell
-- 事件存储
class Monad m => EventStore m where
  appendEvent :: StreamId -> Event -> m (Either EventStoreError EventNumber)
  readEvents :: StreamId -> EventNumber -> m (Either EventStoreError [Event])
  readAllEvents :: StreamId -> m (Either EventStoreError [Event])

-- 聚合根
data UserAggregate = UserAggregate
  { userId :: UserId
  , events :: [UserEvent]
  , currentState :: UserState
  }

-- 事件应用
applyEvent :: UserAggregate -> UserEvent -> UserAggregate
applyEvent agg event = 
  agg { events = event : events agg
      , currentState = updateState (currentState agg) event
      }
```

## 分布式系统架构

### 1. 一致性模式

#### 最终一致性

```haskell
-- 最终一致性实现
data ConsistencyLevel = 
  Strong
  | Eventual
  | ReadYourWrites

-- 读写分离
class Monad m => ReadWriteSeparation m where
  write :: WriteOperation -> m (Either WriteError ())
  read :: ReadOperation -> ConsistencyLevel -> m (Either ReadError ReadResult)

-- 异步复制
data ReplicationConfig = ReplicationConfig
  { replicationFactor :: Int
  , consistencyLevel :: ConsistencyLevel
  , timeout :: Timeout
  }
```

#### CAP定理处理

```haskell
-- 分区容忍性优先
data CAPStrategy = 
  CP -- 一致性 + 分区容忍性
  | AP -- 可用性 + 分区容忍性

-- 分区检测
class Monad m => PartitionDetector m where
  detectPartition :: NodeId -> m Bool
  handlePartition :: Partition -> m PartitionResponse

-- 分区恢复
data PartitionRecovery = PartitionRecovery
  { mergeStrategy :: MergeStrategy
  , conflictResolution :: ConflictResolution
  }
```

### 2. 容错设计

#### 断路器模式

```haskell
-- 断路器状态
data CircuitBreakerState = 
  Closed
  | Open
  | HalfOpen

-- 断路器实现
data CircuitBreaker = CircuitBreaker
  { state :: IORef CircuitBreakerState
  , failureThreshold :: Int
  , timeout :: Timeout
  , failureCount :: IORef Int
  }

-- 断路器操作
runWithCircuitBreaker :: CircuitBreaker -> IO a -> IO (Either CircuitBreakerError a)
runWithCircuitBreaker cb action = do
  currentState <- readIORef (state cb)
  case currentState of
    Closed -> do
      result <- try action
      case result of
        Left _ -> incrementFailureCount cb
        Right _ -> resetFailureCount cb
      return result
    Open -> return (Left CircuitBreakerOpen)
    HalfOpen -> -- 尝试恢复逻辑
```

#### 重试机制

```haskell
-- 重试策略
data RetryStrategy = RetryStrategy
  { maxRetries :: Int
  , backoffPolicy :: BackoffPolicy
  , retryCondition :: RetryCondition
  }

data BackoffPolicy = 
  FixedDelay Timeout
  | ExponentialBackoff Timeout Timeout
  | JitteredBackoff Timeout

-- 重试实现
retryWithStrategy :: RetryStrategy -> IO a -> IO (Either RetryError a)
retryWithStrategy strategy action = 
  retryLoop strategy action 0

retryLoop :: RetryStrategy -> IO a -> Int -> IO (Either RetryError a)
retryLoop strategy action attempt = do
  result <- try action
  case result of
    Right value -> return (Right value)
    Left error -> 
      if attempt >= maxRetries strategy
      then return (Left (MaxRetriesExceeded error))
      else do
        delay <- calculateDelay strategy attempt
        threadDelay delay
        retryLoop strategy action (attempt + 1)
```

## 性能优化架构

### 1. 缓存策略

#### 多层缓存

```haskell
-- 缓存层次
data CacheLayer = 
  L1Cache -- 内存缓存
  | L2Cache -- 分布式缓存
  | L3Cache -- 持久化缓存

-- 缓存接口
class Monad m => Cache m where
  get :: Key -> m (Maybe Value)
  set :: Key -> Value -> TTL -> m ()
  delete :: Key -> m ()
  clear :: m ()

-- 缓存策略
data CacheStrategy = CacheStrategy
  { writePolicy :: WritePolicy
  , evictionPolicy :: EvictionPolicy
  , ttl :: TTL
  }

data WritePolicy = 
  WriteThrough
  | WriteBack
  | WriteAround
```

#### 缓存一致性

```haskell
-- 缓存失效策略
data InvalidationStrategy = 
  TimeBased TTL
  | EventBased [EventType]
  | Manual

-- 缓存同步
class Monad m => CacheSynchronizer m where
  invalidateCache :: CacheKey -> m ()
  updateCache :: CacheKey -> Value -> m ()
  syncCache :: CacheKey -> m ()
```

### 2. 异步处理

#### 消息队列

```haskell
-- 消息队列接口
class Monad m => MessageQueue m where
  enqueue :: QueueName -> Message -> m (Either QueueError MessageId)
  dequeue :: QueueName -> m (Either QueueError (Maybe Message))
  acknowledge :: MessageId -> m (Either QueueError ())

-- 消息处理器
type MessageHandler m = Message -> m (Either HandlerError ())

-- 消息路由
data MessageRouter = MessageRouter
  { routes :: Map MessageType QueueName
  , deadLetterQueue :: QueueName
  }
```

#### 异步任务

```haskell
-- 任务调度器
class Monad m => TaskScheduler m where
  scheduleTask :: Task -> Schedule -> m (Either SchedulerError TaskId)
  cancelTask :: TaskId -> m (Either SchedulerError ())
  getTaskStatus :: TaskId -> m (Either SchedulerError TaskStatus)

-- 任务执行器
data TaskExecutor = TaskExecutor
  { workerPool :: WorkerPool
  , taskQueue :: TaskQueue
  , resultStore :: ResultStore
  }
```

## 安全架构

### 1. 认证与授权

#### 身份认证

```haskell
-- 认证服务
class Monad m => AuthenticationService m where
  authenticate :: Credentials -> m (Either AuthError AuthToken)
  validateToken :: AuthToken -> m (Either AuthError UserInfo)
  refreshToken :: AuthToken -> m (Either AuthError AuthToken)

-- JWT实现
data JWTToken = JWTToken
  { header :: JWTHeader
  , payload :: JWTPayload
  , signature :: JWTSignature
  }

-- 密码哈希
hashPassword :: Password -> IO HashedPassword
hashPassword password = do
  salt <- generateSalt
  return $ hashWithSalt salt password
```

#### 权限控制

```haskell
-- 权限模型
data Permission = Permission
  { resource :: Resource
  , action :: Action
  , conditions :: [Condition]
  }

data Role = Role
  { roleName :: RoleName
  , permissions :: [Permission]
  }

-- 授权检查
class Monad m => AuthorizationService m where
  checkPermission :: UserId -> Permission -> m Bool
  getUserRoles :: UserId -> m [Role]
  grantPermission :: UserId -> Permission -> m (Either AuthError ())
```

### 2. 数据安全

#### 加密

```haskell
-- 加密服务
class Monad m => EncryptionService m where
  encrypt :: PlainText -> Key -> m (Either EncryptionError CipherText)
  decrypt :: CipherText -> Key -> m (Either EncryptionError PlainText)
  generateKey :: KeySize -> m (Either EncryptionError Key)

-- 敏感数据处理
newtype SensitiveData a = SensitiveData { unSensitiveData :: a }

-- 安全存储
class Monad m => SecureStorage m where
  storeSecurely :: SensitiveData a -> m (Either StorageError StorageId)
  retrieveSecurely :: StorageId -> m (Either StorageError (SensitiveData a))
```

## 监控与可观测性

### 1. 日志系统

#### 结构化日志

```haskell
-- 日志级别
data LogLevel = Debug | Info | Warn | Error | Fatal

-- 日志记录器
class Monad m => Logger m where
  log :: LogLevel -> LogMessage -> m ()
  logWithContext :: LogLevel -> LogMessage -> LogContext -> m ()

-- 日志上下文
data LogContext = LogContext
  { requestId :: RequestId
  , userId :: Maybe UserId
  , timestamp :: UTCTime
  , metadata :: Map String String
  }
```

#### 分布式追踪

```haskell
-- 追踪上下文
data TraceContext = TraceContext
  { traceId :: TraceId
  , spanId :: SpanId
  , parentSpanId :: Maybe SpanId
  }

-- 追踪服务
class Monad m => TracingService m where
  startSpan :: SpanName -> m SpanId
  endSpan :: SpanId -> m ()
  addSpanTag :: SpanId -> Tag -> m ()
  injectContext :: TraceContext -> m ()
```

### 2. 指标收集

#### 性能指标

```haskell
-- 指标类型
data Metric = 
  Counter MetricName Int
  | Gauge MetricName Double
  | Histogram MetricName [Double]

-- 指标收集器
class Monad m => MetricsCollector m where
  incrementCounter :: MetricName -> m ()
  setGauge :: MetricName -> Double -> m ()
  recordHistogram :: MetricName -> Double -> m ()
  getMetrics :: m [Metric]
```

#### 健康检查

```haskell
-- 健康状态
data HealthStatus = 
  Healthy
  | Unhealthy String
  | Degraded String

-- 健康检查服务
class Monad m => HealthCheckService m where
  checkHealth :: m HealthStatus
  registerHealthCheck :: HealthCheck -> m ()
  getHealthReport :: m HealthReport

-- 健康检查
data HealthCheck = HealthCheck
  { checkName :: String
  , checkFunction :: IO HealthStatus
  , timeout :: Timeout
  }
```

---

**相关链接**：

- [软件工程基础](../03-Software-Engineering/301-Software-Engineering-Foundations.md)
- [开发方法论](../03-Software-Engineering/302-Development-Methodologies.md)
- [架构设计模式](../03-Software-Engineering/303-Architecture-Design-Patterns.md)
