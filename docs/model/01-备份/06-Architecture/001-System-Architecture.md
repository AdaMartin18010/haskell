# 系统架构设计

## 概述

本文档介绍基于函数式编程和形式方法的现代系统架构设计模式，重点关注Haskell、Rust和Lean在大规模系统中的应用。

## 架构层次

### 1. 分层架构

```haskell
-- 传统分层架构的函数式实现
{-# LANGUAGE DerivingStrategies #-}

-- 领域层
module Domain.User where

data User = User
  { userId :: UserId
  , email :: Email
  , name :: UserName
  } deriving stock (Show, Eq)

newtype UserId = UserId Text deriving newtype (Show, Eq, Hashable)
newtype Email = Email Text deriving newtype (Show, Eq)
newtype UserName = UserName Text deriving newtype (Show, Eq)

-- 应用层
module Application.UserService where

class Monad m => UserRepository m where
  findUser :: UserId -> m (Maybe User)
  saveUser :: User -> m ()

createUser :: UserRepository m => Email -> UserName -> m (Either UserError User)
createUser email name = do
  let newUser = User (UserId "generated") email name
  saveUser newUser
  return $ Right newUser

data UserError = InvalidEmail | UserExists deriving (Show, Eq)

-- 基础设施层
module Infrastructure.UserRepo where

import Database.PostgreSQL.Simple

instance UserRepository IO where
  findUser (UserId uid) = do
    conn <- connectPostgreSQL "dbname=myapp"
    result <- query conn "SELECT * FROM users WHERE id = ?" (Only uid)
    return $ case result of
      [user] -> Just user
      _ -> Nothing
```

### 2. 六边形架构(端口适配器)

```rust
// Rust中的六边形架构
use async_trait::async_trait;
use std::collections::HashMap;

// 领域核心
#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub email: String,
    pub name: String,
}

#[derive(Debug)]
pub enum UserError {
    NotFound,
    ValidationError(String),
    DatabaseError(String),
}

// 端口(抽象接口)
#[async_trait]
pub trait UserRepository: Send + Sync {
    async fn find_by_id(&self, id: &str) -> Result<Option<User>, UserError>;
    async fn save(&self, user: &User) -> Result<(), UserError>;
}

#[async_trait]
pub trait EmailService: Send + Sync {
    async fn send_welcome_email(&self, user: &User) -> Result<(), UserError>;
}

// 应用服务(用例)
pub struct UserService<R: UserRepository, E: EmailService> {
    user_repo: R,
    email_service: E,
}

impl<R: UserRepository, E: EmailService> UserService<R, E> {
    pub fn new(user_repo: R, email_service: E) -> Self {
        Self { user_repo, email_service }
    }
    
    pub async fn create_user(&self, email: String, name: String) -> Result<User, UserError> {
        let user = User {
            id: uuid::Uuid::new_v4().to_string(),
            email,
            name,
        };
        
        self.user_repo.save(&user).await?;
        self.email_service.send_welcome_email(&user).await?;
        
        Ok(user)
    }
}

// 适配器实现
pub struct PostgresUserRepository {
    pool: sqlx::PgPool,
}

#[async_trait]
impl UserRepository for PostgresUserRepository {
    async fn find_by_id(&self, id: &str) -> Result<Option<User>, UserError> {
        let result = sqlx::query_as!(
            User,
            "SELECT id, email, name FROM users WHERE id = $1",
            id
        )
        .fetch_optional(&self.pool)
        .await
        .map_err(|e| UserError::DatabaseError(e.to_string()))?;
        
        Ok(result)
    }
    
    async fn save(&self, user: &User) -> Result<(), UserError> {
        sqlx::query!(
            "INSERT INTO users (id, email, name) VALUES ($1, $2, $3)",
            user.id, user.email, user.name
        )
        .execute(&self.pool)
        .await
        .map_err(|e| UserError::DatabaseError(e.to_string()))?;
        
        Ok(())
    }
}
```

### 3. 微服务架构

```haskell
-- 微服务通信模式
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

import Servant

-- API定义
type UserAPI = 
       "users" :> Get '[JSON] [User]
  :<|> "users" :> ReqBody '[JSON] CreateUserRequest :> Post '[JSON] User
  :<|> "users" :> Capture "id" UserId :> Get '[JSON] User

type OrderAPI = 
       "orders" :> Get '[JSON] [Order]
  :<|> "orders" :> ReqBody '[JSON] CreateOrderRequest :> Post '[JSON] Order

-- 服务间通信
data ServiceDiscovery = ServiceDiscovery
  { userServiceUrl :: Text
  , orderServiceUrl :: Text
  , paymentServiceUrl :: Text
  }

-- HTTP客户端
callUserService :: ServiceDiscovery -> UserId -> IO (Maybe User)
callUserService sd userId = do
  manager <- newManager defaultManagerSettings
  let url = userServiceUrl sd <> "/users/" <> unUserId userId
  response <- httpLBS =<< parseRequest (T.unpack url)
  return $ decode (responseBody response)

-- 事件驱动架构
data DomainEvent
  = UserCreated User
  | OrderPlaced Order
  | PaymentProcessed Payment
  deriving (Show, Generic, ToJSON, FromJSON)

-- 事件发布
publishEvent :: DomainEvent -> IO ()
publishEvent event = do
  -- 发布到消息队列(Redis/RabbitMQ/Kafka)
  putStrLn $ "Publishing event: " <> show event
```

## 并发和并行架构

### Actor模型

```rust
// Rust Actor模型实现
use tokio::sync::mpsc;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Message {
    GetUser { id: String, respond_to: mpsc::Sender<Option<User>> },
    CreateUser { user: User, respond_to: mpsc::Sender<Result<(), String>> },
    Stop,
}

pub struct UserActor {
    receiver: mpsc::Receiver<Message>,
    users: HashMap<String, User>,
}

impl UserActor {
    pub fn new(receiver: mpsc::Receiver<Message>) -> Self {
        Self {
            receiver,
            users: HashMap::new(),
        }
    }
    
    pub async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                Message::GetUser { id, respond_to } => {
                    let user = self.users.get(&id).cloned();
                    let _ = respond_to.send(user).await;
                }
                Message::CreateUser { user, respond_to } => {
                    let id = user.id.clone();
                    self.users.insert(id, user);
                    let _ = respond_to.send(Ok(())).await;
                }
                Message::Stop => break,
            }
        }
    }
}

// Actor句柄
#[derive(Clone)]
pub struct UserActorHandle {
    sender: mpsc::Sender<Message>,
}

impl UserActorHandle {
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel(32);
        let mut actor = UserActor::new(receiver);
        
        tokio::spawn(async move {
            actor.run().await;
        });
        
        Self { sender }
    }
    
    pub async fn get_user(&self, id: String) -> Option<User> {
        let (send, mut recv) = mpsc::channel(1);
        let msg = Message::GetUser { id, respond_to: send };
        
        if self.sender.send(msg).await.is_ok() {
            recv.recv().await.unwrap_or(None)
        } else {
            None
        }
    }
}
```

### STM并发控制

```haskell
-- 软件事务内存
import Control.Concurrent.STM

-- 共享状态
data BankAccount = BankAccount
  { balance :: TVar Money
  , accountId :: AccountId
  } deriving (Eq)

-- 原子转账操作
transfer :: Money -> BankAccount -> BankAccount -> STM ()
transfer amount from to = do
  fromBalance <- readTVar (balance from)
  when (fromBalance < amount) retry
  
  toBalance <- readTVar (balance to)
  writeTVar (balance from) (fromBalance - amount)
  writeTVar (balance to) (toBalance + amount)

-- 批量转账
batchTransfer :: [(Money, BankAccount, BankAccount)] -> IO ()
batchTransfer transfers = atomically $ do
  mapM_ (\(amt, from, to) -> transfer amt from to) transfers

-- 账户监控
monitorAccount :: BankAccount -> Money -> STM ()
monitorAccount account threshold = do
  currentBalance <- readTVar (balance account)
  when (currentBalance < threshold) $ do
    -- 触发告警
    unsafeIOToSTM $ putStrLn "Low balance alert!"
```

## 函数式架构模式

### Monad Transformer Stack

```haskell
-- 应用程序Monad栈
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

type AppStack = ReaderT Config (StateT AppState (ExceptT AppError IO))

newtype App a = App { unApp :: AppStack a }
  deriving ( Functor, Applicative, Monad
           , MonadReader Config, MonadState AppState
           , MonadError AppError, MonadIO )

data Config = Config
  { dbConnection :: ConnectionString
  , logLevel :: LogLevel
  , serverPort :: Port
  }

data AppState = AppState
  { requestCount :: Int
  , activeUsers :: Set UserId
  }

data AppError
  = DatabaseError Text
  | ValidationError Text
  | AuthenticationError
  deriving (Show)

-- 运行应用
runApp :: Config -> AppState -> App a -> IO (Either AppError (a, AppState))
runApp config state app = 
  runExceptT $ runStateT (runReaderT (unApp app) config) state

-- 数据库操作
dbQuery :: Query -> App [Row]
dbQuery query = do
  connStr <- asks dbConnection
  result <- liftIO $ runQuery connStr query
  case result of
    Left err -> throwError (DatabaseError err)
    Right rows -> return rows
```

### Free Monad架构

```haskell
-- Free Monad DSL
{-# LANGUAGE DeriveFunctor #-}

data DatabaseF next
  = Query Text ([Row] -> next)
  | Insert Text next
  | Update Text next
  deriving Functor

type Database = Free DatabaseF

-- DSL构造器
query :: Text -> Database [Row]
query sql = liftF $ Query sql id

insert :: Text -> Database ()
insert sql = liftF $ Insert sql ()

update :: Text -> Database ()  
update sql = liftF $ Update sql ()

-- 解释器
interpretDB :: Database a -> IO a
interpretDB = iterM go
  where
    go (Query sql next) = do
      rows <- runSQL sql  -- 实际数据库操作
      return $ next rows
    go (Insert sql next) = do
      runSQL sql
      return next
    go (Update sql next) = do
      runSQL sql
      return next

-- 测试解释器
interpretDBTest :: Database a -> State TestDB a
interpretDBTest = iterM go
  where
    go (Query sql next) = do
      rows <- gets (mockQuery sql)
      return $ next rows
    go (Insert sql next) = do
      modify (mockInsert sql)
      return next
    go (Update sql next) = do
      modify (mockUpdate sql)
      return next
```

## 错误处理架构

### 类型安全错误处理

```rust
// 分层错误处理
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DomainError {
    #[error("User not found: {id}")]
    UserNotFound { id: String },
    
    #[error("Invalid email format: {email}")]
    InvalidEmail { email: String },
    
    #[error("Business rule violation: {rule}")]
    BusinessRuleViolation { rule: String },
}

#[derive(Error, Debug)]
pub enum InfrastructureError {
    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),
    
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),
}

#[derive(Error, Debug)]
pub enum ApplicationError {
    #[error("Domain error: {0}")]
    Domain(#[from] DomainError),
    
    #[error("Infrastructure error: {0}")]
    Infrastructure(#[from] InfrastructureError),
}

// 结果类型链
pub type DomainResult<T> = Result<T, DomainError>;
pub type InfraResult<T> = Result<T, InfrastructureError>;
pub type AppResult<T> = Result<T, ApplicationError>;

// 错误恢复
pub async fn get_user_with_fallback(id: &str) -> AppResult<User> {
    match get_user_from_cache(id).await {
        Ok(user) => Ok(user),
        Err(_) => {
            // 缓存失败，尝试数据库
            match get_user_from_db(id).await {
                Ok(user) => {
                    // 更新缓存
                    let _ = update_cache(id, &user).await;
                    Ok(user)
                }
                Err(e) => Err(e.into())
            }
        }
    }
}
```

## 形式化架构验证

```lean
-- 架构不变量的形式化
structure SystemArchitecture where
  components : Set Component
  connections : Component → Component → Prop
  constraints : Set ArchConstraint

-- 层级约束
def LayeredConstraint (arch : SystemArchitecture) : Prop :=
  ∀ c1 c2, arch.connections c1 c2 → layer c1 ≤ layer c2

-- 循环依赖检测
def AcyclicConstraint (arch : SystemArchitecture) : Prop :=
  ∀ c, ¬ arch.connections c c ∧ 
  ∀ c1 c2 c3, arch.connections c1 c2 → arch.connections c2 c3 → 
             ¬ arch.connections c3 c1

-- 架构演化
def ArchitectureEvolution (old new : SystemArchitecture) : Prop :=
  -- 向后兼容性
  (∀ c ∈ old.components, c ∈ new.components) ∧
  -- 接口稳定性  
  (∀ c1 c2, old.connections c1 c2 → new.connections c1 c2)

-- 性能保证
def PerformanceInvariant (arch : SystemArchitecture) (load : Load) : Prop :=
  response_time arch load ≤ max_response_time ∧
  throughput arch load ≥ min_throughput
```

## 部署和运维架构

### 容器化部署

```dockerfile
# Haskell服务容器
FROM haskell:8.10 as builder
WORKDIR /app
COPY stack.yaml package.yaml ./
RUN stack build --dependencies-only

COPY . .
RUN stack build --copy-bins

FROM ubuntu:20.04
RUN apt-get update && apt-get install -y ca-certificates
COPY --from=builder /root/.local/bin/myapp /usr/local/bin/
EXPOSE 8080
CMD ["myapp"]
```

```yaml
# Kubernetes部署配置
apiVersion: apps/v1
kind: Deployment
metadata:
  name: user-service
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
        image: myregistry/user-service:latest
        ports:
        - containerPort: 8080
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-secret
              key: url
        resources:
          requests:
            memory: "64Mi"
            cpu: "250m"
          limits:
            memory: "128Mi"
            cpu: "500m"
```

## 总结

现代系统架构设计需要考虑：

1. **模块化**: 清晰的分层和组件边界
2. **可扩展性**: 水平和垂直扩展能力
3. **容错性**: 优雅的错误处理和恢复
4. **可维护性**: 代码的可读性和可测试性
5. **性能**: 合理的资源利用和响应时间
6. **安全性**: 多层防护和访问控制

函数式编程和形式方法为架构设计提供了强大的工具，确保系统的正确性、可靠性和可维护性。
