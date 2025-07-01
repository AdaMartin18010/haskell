# 软件开发方法论

## 概述

软件开发方法论是指导软件开发过程的系统化方法和实践。本文档介绍现代软件开发方法论，特别关注函数式编程和形式方法在敏捷开发、DevOps、领域驱动设计等方法论中的应用。

## 敏捷开发方法论

### Scrum框架

```haskell
-- Scrum过程的形式化建模
{-# LANGUAGE GADTs #-}

data SprintState = Planning | Executing | Review | Retrospective
  deriving (Show, Eq)

data UserStory = UserStory
  { storyId :: StoryId
  , title :: Text
  , description :: Text
  , acceptanceCriteria :: [Text]
  , storyPoints :: Int
  , priority :: Priority
  , status :: StoryStatus
  } deriving (Show)

data Priority = High | Medium | Low deriving (Show, Eq, Ord)
data StoryStatus = Backlog | InProgress | Testing | Done deriving (Show, Eq)

newtype StoryId = StoryId Text deriving (Show, Eq)

-- 产品待办事项列表
data ProductBacklog = ProductBacklog
  { stories :: [UserStory]
  , lastUpdated :: UTCTime
  } deriving (Show)

-- Sprint管理
data Sprint = Sprint
  { sprintId :: SprintId
  , goal :: Text
  , startDate :: UTCTime
  , endDate :: UTCTime
  , capacity :: Int  -- 团队容量(故事点)
  , selectedStories :: [UserStory]
  , currentState :: SprintState
  } deriving (Show)

newtype SprintId = SprintId Text deriving (Show, Eq)

-- Sprint计划
planSprint :: ProductBacklog -> Int -> Either PlanningError Sprint
planSprint backlog capacity = do
  let prioritizedStories = sortBy (comparing priority) (stories backlog)
      selectedStories = selectStoriesForCapacity prioritizedStories capacity []
  if sum (map storyPoints selectedStories) <= capacity
  then Right $ Sprint 
    { sprintId = SprintId "sprint-1"
    , goal = "Deliver core user features"
    , startDate = UTCTime (fromGregorian 2024 1 1) 0
    , endDate = UTCTime (fromGregorian 2024 1 15) 0
    , capacity = capacity
    , selectedStories = selectedStories
    , currentState = Planning
    }
  else Left CapacityExceeded

data PlanningError = CapacityExceeded | NoStoriesAvailable
  deriving (Show, Eq)

selectStoriesForCapacity :: [UserStory] -> Int -> [UserStory] -> [UserStory]
selectStoriesForCapacity [] _ acc = acc
selectStoriesForCapacity (s:ss) remainingCapacity acc
  | storyPoints s <= remainingCapacity = 
      selectStoriesForCapacity ss (remainingCapacity - storyPoints s) (s:acc)
  | otherwise = acc

-- 燃尽图计算
data BurndownPoint = BurndownPoint
  { date :: UTCTime
  , remainingPoints :: Int
  , completedPoints :: Int
  } deriving (Show)

calculateBurndown :: Sprint -> [BurndownPoint]
calculateBurndown sprint = 
  let totalPoints = sum $ map storyPoints (selectedStories sprint)
      sprintDays = diffDays (utctDay $ endDate sprint) (utctDay $ startDate sprint)
      idealBurnRate = fromIntegral totalPoints / fromIntegral sprintDays
  in map (\day -> BurndownPoint
    { date = addUTCTime (fromIntegral day * 86400) (startDate sprint)
    , remainingPoints = max 0 (totalPoints - floor (idealBurnRate * fromIntegral day))
    , completedPoints = min totalPoints (floor (idealBurnRate * fromIntegral day))
    }) [0..sprintDays]
```

### 极限编程(XP)实践

```rust
// 测试驱动开发(TDD)实现
use std::collections::HashMap;

// 红-绿-重构循环
#[derive(Debug, PartialEq)]
pub struct BankAccount {
    balance: i64, // 以分为单位避免浮点精度问题
    account_number: String,
}

impl BankAccount {
    pub fn new(account_number: String) -> Self {
        Self {
            balance: 0,
            account_number,
        }
    }
    
    pub fn deposit(&mut self, amount: i64) -> Result<(), AccountError> {
        if amount <= 0 {
            return Err(AccountError::InvalidAmount);
        }
        self.balance += amount;
        Ok(())
    }
    
    pub fn withdraw(&mut self, amount: i64) -> Result<(), AccountError> {
        if amount <= 0 {
            return Err(AccountError::InvalidAmount);
        }
        if self.balance < amount {
            return Err(AccountError::InsufficientFunds);
        }
        self.balance -= amount;
        Ok(())
    }
    
    pub fn balance(&self) -> i64 {
        self.balance
    }
}

#[derive(Debug, PartialEq)]
pub enum AccountError {
    InvalidAmount,
    InsufficientFunds,
}

// 配对编程结构
pub struct PairProgrammingSession {
    driver: Developer,
    navigator: Developer,
    task: String,
    start_time: std::time::Instant,
    switch_interval: std::time::Duration,
}

#[derive(Debug, Clone)]
pub struct Developer {
    name: String,
    skills: Vec<String>,
}

impl PairProgrammingSession {
    pub fn new(driver: Developer, navigator: Developer, task: String) -> Self {
        Self {
            driver,
            navigator,
            task,
            start_time: std::time::Instant::now(),
            switch_interval: std::time::Duration::from_mins(25), // 番茄工作法
        }
    }
    
    pub fn should_switch_roles(&self) -> bool {
        self.start_time.elapsed() >= self.switch_interval
    }
    
    pub fn switch_roles(&mut self) {
        std::mem::swap(&mut self.driver, &mut self.navigator);
        self.start_time = std::time::Instant::now();
    }
}

// 持续集成指标
#[derive(Debug)]
pub struct CIMetrics {
    build_success_rate: f64,
    average_build_time: std::time::Duration,
    test_coverage: f64,
    deployment_frequency: u32, // 每天部署次数
}

impl CIMetrics {
    pub fn is_healthy(&self) -> bool {
        self.build_success_rate >= 0.95 &&
        self.average_build_time <= std::time::Duration::from_mins(10) &&
        self.test_coverage >= 0.8 &&
        self.deployment_frequency >= 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TDD: 先写测试
    #[test]
    fn new_account_has_zero_balance() {
        let account = BankAccount::new("123456".to_string());
        assert_eq!(account.balance(), 0);
    }
    
    #[test]
    fn can_deposit_money() {
        let mut account = BankAccount::new("123456".to_string());
        assert!(account.deposit(100).is_ok());
        assert_eq!(account.balance(), 100);
    }
    
    #[test]
    fn cannot_deposit_negative_amount() {
        let mut account = BankAccount::new("123456".to_string());
        assert_eq!(account.deposit(-100), Err(AccountError::InvalidAmount));
    }
    
    #[test]
    fn can_withdraw_money_when_sufficient_funds() {
        let mut account = BankAccount::new("123456".to_string());
        account.deposit(100).unwrap();
        assert!(account.withdraw(50).is_ok());
        assert_eq!(account.balance(), 50);
    }
    
    #[test]
    fn cannot_withdraw_more_than_balance() {
        let mut account = BankAccount::new("123456".to_string());
        account.deposit(100).unwrap();
        assert_eq!(account.withdraw(150), Err(AccountError::InsufficientFunds));
    }
}
```

## 领域驱动设计(DDD)

### 战略设计

```haskell
-- 领域建模
{-# LANGUAGE DerivingStrategies #-}

-- 值对象
newtype Email = Email Text 
  deriving newtype (Show, Eq)
  deriving stock (Ord)

newtype UserId = UserId UUID
  deriving newtype (Show, Eq)
  deriving stock (Ord)

-- 实体
data User = User
  { userId :: UserId
  , email :: Email
  , profile :: UserProfile
  , version :: Version
  } deriving (Show, Eq)

data UserProfile = UserProfile
  { firstName :: Text
  , lastName :: Text
  , dateOfBirth :: Day
  } deriving (Show, Eq)

newtype Version = Version Int deriving newtype (Show, Eq, Num)

-- 聚合根
data OrderAggregate = OrderAggregate
  { orderId :: OrderId
  , customerId :: CustomerId
  , items :: [OrderItem]
  , status :: OrderStatus
  , totalAmount :: Money
  , events :: [DomainEvent]
  } deriving (Show, Eq)

newtype OrderId = OrderId UUID deriving newtype (Show, Eq)
newtype CustomerId = CustomerId UUID deriving newtype (Show, Eq)

data OrderItem = OrderItem
  { productId :: ProductId
  , quantity :: Quantity
  , unitPrice :: Money
  } deriving (Show, Eq)

data OrderStatus = Pending | Confirmed | Shipped | Delivered | Cancelled
  deriving (Show, Eq)

-- 领域事件
data DomainEvent
  = OrderPlaced OrderId CustomerId
  | OrderConfirmed OrderId
  | OrderShipped OrderId
  | OrderDelivered OrderId
  deriving (Show, Eq)

-- 领域服务
class Monad m => OrderService m where
  placeOrder :: CustomerId -> [OrderItem] -> m (Either OrderError OrderAggregate)
  confirmOrder :: OrderId -> m (Either OrderError OrderAggregate)
  
data OrderError
  = CustomerNotFound CustomerId
  | InvalidOrderItems
  | InsufficientInventory ProductId
  deriving (Show, Eq)

-- 仓储模式
class Monad m => OrderRepository m where
  save :: OrderAggregate -> m ()
  findById :: OrderId -> m (Maybe OrderAggregate)
  findByCustomer :: CustomerId -> m [OrderAggregate]

-- 领域事件发布
class Monad m => EventPublisher m where
  publish :: DomainEvent -> m ()

-- 应用服务
placeOrderUseCase :: (OrderService m, OrderRepository m, EventPublisher m) 
                  => CustomerId -> [OrderItem] -> m (Either OrderError OrderId)
placeOrderUseCase customerId items = do
  result <- placeOrder customerId items
  case result of
    Left err -> return $ Left err
    Right order -> do
      save order
      mapM_ publish (events order)
      return $ Right (orderId order)
```

### 战术设计

```rust
// 值对象的类型安全实现
use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Email(String);

impl Email {
    pub fn new(email: String) -> Result<Self, ValidationError> {
        if Self::is_valid_email(&email) {
            Ok(Email(email))
        } else {
            Err(ValidationError::InvalidEmail)
        }
    }
    
    fn is_valid_email(email: &str) -> bool {
        // 简化的邮箱验证
        email.contains('@') && email.contains('.')
    }
    
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Email {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Money {
    amount: i64, // 以分为单位
    currency: Currency,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Currency {
    USD,
    EUR,
    CNY,
}

impl Money {
    pub fn new(amount: i64, currency: Currency) -> Self {
        Self { amount, currency }
    }
    
    pub fn add(&self, other: &Money) -> Result<Money, MoneyError> {
        if self.currency != other.currency {
            return Err(MoneyError::CurrencyMismatch);
        }
        Ok(Money::new(self.amount + other.amount, self.currency.clone()))
    }
    
    pub fn amount(&self) -> i64 {
        self.amount
    }
    
    pub fn currency(&self) -> &Currency {
        &self.currency
    }
}

#[derive(Debug, PartialEq)]
pub enum MoneyError {
    CurrencyMismatch,
}

#[derive(Debug)]
pub enum ValidationError {
    InvalidEmail,
    InvalidPhoneNumber,
    InvalidAmount,
}

// 实体基类
pub trait Entity {
    type Id;
    fn id(&self) -> &Self::Id;
}

// 聚合根
pub trait AggregateRoot: Entity {
    type Event;
    fn uncommitted_events(&self) -> &[Self::Event];
    fn mark_events_as_committed(&mut self);
}

// 订单聚合的具体实现
#[derive(Debug)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    total_amount: Money,
    version: i32,
    uncommitted_events: Vec<OrderEvent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OrderId(uuid::Uuid);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustomerId(uuid::Uuid);

#[derive(Debug, Clone)]
pub struct OrderItem {
    product_id: ProductId,
    quantity: u32,
    unit_price: Money,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProductId(uuid::Uuid);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

#[derive(Debug, Clone)]
pub enum OrderEvent {
    OrderPlaced { order_id: OrderId, customer_id: CustomerId },
    OrderConfirmed { order_id: OrderId },
    OrderShipped { order_id: OrderId },
}

impl Entity for Order {
    type Id = OrderId;
    
    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl AggregateRoot for Order {
    type Event = OrderEvent;
    
    fn uncommitted_events(&self) -> &[Self::Event] {
        &self.uncommitted_events
    }
    
    fn mark_events_as_committed(&mut self) {
        self.uncommitted_events.clear();
    }
}

impl Order {
    pub fn place_order(
        customer_id: CustomerId,
        items: Vec<OrderItem>,
    ) -> Result<Self, OrderError> {
        if items.is_empty() {
            return Err(OrderError::EmptyOrder);
        }
        
        let order_id = OrderId(uuid::Uuid::new_v4());
        let total_amount = Self::calculate_total(&items)?;
        
        let mut order = Self {
            id: order_id.clone(),
            customer_id: customer_id.clone(),
            items,
            status: OrderStatus::Pending,
            total_amount,
            version: 1,
            uncommitted_events: vec![],
        };
        
        order.uncommitted_events.push(OrderEvent::OrderPlaced {
            order_id,
            customer_id,
        });
        
        Ok(order)
    }
    
    pub fn confirm(&mut self) -> Result<(), OrderError> {
        match self.status {
            OrderStatus::Pending => {
                self.status = OrderStatus::Confirmed;
                self.version += 1;
                self.uncommitted_events.push(OrderEvent::OrderConfirmed {
                    order_id: self.id.clone(),
                });
                Ok(())
            }
            _ => Err(OrderError::InvalidStatusTransition),
        }
    }
    
    fn calculate_total(items: &[OrderItem]) -> Result<Money, OrderError> {
        if items.is_empty() {
            return Ok(Money::new(0, Currency::USD));
        }
        
        let currency = &items[0].unit_price.currency;
        let mut total = Money::new(0, currency.clone());
        
        for item in items {
            let item_total = Money::new(
                item.unit_price.amount() * item.quantity as i64,
                item.unit_price.currency().clone(),
            );
            total = total.add(&item_total).map_err(|_| OrderError::CurrencyMismatch)?;
        }
        
        Ok(total)
    }
}

#[derive(Debug, PartialEq)]
pub enum OrderError {
    EmptyOrder,
    InvalidStatusTransition,
    CurrencyMismatch,
}
```

## DevOps与持续交付

### 基础设施即代码

```yaml
# Terraform配置
terraform {
  required_version = ">= 1.0"
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
  }
}

provider "aws" {
  region = var.aws_region
}

# VPC配置
resource "aws_vpc" "main" {
  cidr_block           = var.vpc_cidr
  enable_dns_hostnames = true
  enable_dns_support   = true
  
  tags = {
    Name        = "${var.project_name}-vpc"
    Environment = var.environment
  }
}

# 子网配置
resource "aws_subnet" "private" {
  count             = length(var.private_subnet_cidrs)
  vpc_id            = aws_vpc.main.id
  cidr_block        = var.private_subnet_cidrs[count.index]
  availability_zone = data.aws_availability_zones.available.names[count.index]
  
  tags = {
    Name = "${var.project_name}-private-${count.index + 1}"
    Type = "Private"
  }
}

# ECS集群
resource "aws_ecs_cluster" "main" {
  name = "${var.project_name}-cluster"
  
  setting {
    name  = "containerInsights"
    value = "enabled"
  }
}

# ECS服务
resource "aws_ecs_service" "app" {
  name            = "${var.project_name}-service"
  cluster         = aws_ecs_cluster.main.id
  task_definition = aws_ecs_task_definition.app.arn
  desired_count   = var.desired_count
  
  deployment_configuration {
    maximum_percent         = 200
    minimum_healthy_percent = 100
  }
  
  network_configuration {
    subnets         = aws_subnet.private[*].id
    security_groups = [aws_security_group.app.id]
  }
}

# 变量定义
variable "aws_region" {
  description = "AWS region"
  type        = string
  default     = "us-west-2"
}

variable "environment" {
  description = "Environment name"
  type        = string
  validation {
    condition     = contains(["dev", "staging", "prod"], var.environment)
    error_message = "Environment must be dev, staging, or prod."
  }
}
```

### 监控和可观测性

```haskell
-- 结构化日志和指标
{-# LANGUAGE OverloadedStrings #-}

import Data.Aeson
import Control.Monad.Logger
import System.Metrics
import System.Metrics.Counter

-- 结构化日志
data LogContext = LogContext
  { requestId :: Text
  , userId :: Maybe UserId
  , operation :: Text
  , duration :: Double
  } deriving (Generic)

instance ToJSON LogContext

-- 应用指标
data AppMetrics = AppMetrics
  { requestCounter :: Counter
  , errorCounter :: Counter
  , requestDuration :: Distribution
  , activeUsers :: Gauge
  }

-- 可观测性Monad
class Monad m => Observable m where
  logStructured :: LogLevel -> LogContext -> Text -> m ()
  incrementCounter :: Counter -> m ()
  recordDuration :: Distribution -> Double -> m ()
  updateGauge :: Gauge -> Int64 -> m ()

-- 带观测性的HTTP处理器
handleRequest :: (Observable m, MonadIO m) => Request -> m Response
handleRequest req = do
  startTime <- liftIO getCurrentTime
  requestId <- liftIO generateRequestId
  
  let context = LogContext
        { requestId = requestId
        , userId = extractUserId req
        , operation = requestPath req
        , duration = 0
        }
  
  logStructured LevelInfo context "Request started"
  incrementCounter =<< asks requestCounter
  
  result <- processRequest req `catchError` \err -> do
    logStructured LevelError context ("Request failed: " <> show err)
    incrementCounter =<< asks errorCounter
    throwError err
  
  endTime <- liftIO getCurrentTime
  let duration = realToFrac $ diffUTCTime endTime startTime
  recordDuration =<< asks requestDuration $ duration
  
  logStructured LevelInfo context { duration = duration } "Request completed"
  return result

-- 健康检查
data HealthStatus = Healthy | Unhealthy | Degraded
  deriving (Show, Eq)

data HealthCheck = HealthCheck
  { name :: Text
  , status :: HealthStatus
  , details :: Maybe Text
  , lastChecked :: UTCTime
  } deriving (Show, Generic)

instance ToJSON HealthCheck

healthCheck :: IO [HealthCheck]
healthCheck = do
  now <- getCurrentTime
  sequence
    [ checkDatabase now
    , checkRedis now
    , checkExternalAPI now
    ]

checkDatabase :: UTCTime -> IO HealthCheck
checkDatabase now = do
  result <- tryJust (guard . isIOError) $ runDB $ rawSql "SELECT 1" []
  return $ HealthCheck
    { name = "database"
    , status = case result of
        Right _ -> Healthy
        Left _ -> Unhealthy
    , details = case result of
        Right _ -> Nothing
        Left err -> Just (T.pack $ show err)
    , lastChecked = now
    }
```

```rust
// Rust可观测性实现
use opentelemetry::{trace::Tracer, global, KeyValue};
use tracing::{info, error, instrument};
use serde_json::json;
use std::time::Instant;

// 分布式追踪
#[instrument(skip(db_pool))]
pub async fn create_user(
    db_pool: &sqlx::PgPool,
    user_data: CreateUserRequest,
) -> Result<User, UserError> {
    let span = global::tracer("user-service").start("create_user");
    let _guard = span.context();
    
    // 添加追踪属性
    span.set_attribute(KeyValue::new("user.email", user_data.email.clone()));
    span.set_attribute(KeyValue::new("operation", "create_user"));
    
    info!(
        event = "user_creation_started",
        email = %user_data.email,
        "Starting user creation process"
    );
    
    let start_time = Instant::now();
    
    let result = sqlx::query_as!(
        User,
        "INSERT INTO users (email, name) VALUES ($1, $2) RETURNING *",
        user_data.email,
        user_data.name
    )
    .fetch_one(db_pool)
    .await;
    
    let duration = start_time.elapsed();
    
    match &result {
        Ok(user) => {
            info!(
                event = "user_creation_completed",
                user_id = %user.id,
                duration_ms = duration.as_millis() as u64,
                "User created successfully"
            );
            span.set_attribute(KeyValue::new("user.id", user.id.to_string()));
        }
        Err(err) => {
            error!(
                event = "user_creation_failed",
                error = %err,
                duration_ms = duration.as_millis() as u64,
                "Failed to create user"
            );
            span.set_attribute(KeyValue::new("error", true));
        }
    }
    
    // 记录指标
    metrics::histogram!("user_creation_duration", duration.as_secs_f64());
    metrics::counter!("user_creation_total", 1, "status" => if result.is_ok() { "success" } else { "error" });
    
    result.map_err(UserError::Database)
}

// 应用指标
pub struct Metrics {
    request_counter: metrics::Counter,
    error_counter: metrics::Counter,
    request_duration: metrics::Histogram,
}

impl Metrics {
    pub fn new() -> Self {
        Self {
            request_counter: metrics::counter!("http_requests_total"),
            error_counter: metrics::counter!("http_errors_total"),
            request_duration: metrics::histogram!("http_request_duration_seconds"),
        }
    }
    
    pub fn record_request(&self, method: &str, path: &str, status: u16, duration: f64) {
        self.request_counter.increment(1);
        self.request_duration.record(duration);
        
        if status >= 400 {
            self.error_counter.increment(1);
        }
        
        // 记录详细指标
        metrics::counter!("http_requests_total", 1,
            "method" => method,
            "path" => path,
            "status" => status.to_string()
        );
    }
}

// 熔断器实现
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::time::{Duration, Instant as TokioInstant};

#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    failure_threshold: u64,
    recovery_timeout: Duration,
    failure_count: Arc<AtomicU64>,
    last_failure_time: Arc<std::sync::Mutex<Option<TokioInstant>>>,
}

#[derive(Debug, PartialEq)]
pub enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u64, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            failure_count: Arc::new(AtomicU64::new(0)),
            last_failure_time: Arc::new(std::sync::Mutex::new(None)),
        }
    }
    
    pub fn state(&self) -> CircuitState {
        let failure_count = self.failure_count.load(Ordering::Relaxed);
        
        if failure_count < self.failure_threshold {
            return CircuitState::Closed;
        }
        
        let last_failure = self.last_failure_time.lock().unwrap();
        match *last_failure {
            Some(time) if time.elapsed() > self.recovery_timeout => CircuitState::HalfOpen,
            Some(_) => CircuitState::Open,
            None => CircuitState::Closed,
        }
    }
    
    pub async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: std::future::Future<Output = Result<T, E>>,
    {
        match self.state() {
            CircuitState::Open => Err(CircuitBreakerError::CircuitOpen),
            CircuitState::Closed | CircuitState::HalfOpen => {
                match f.await {
                    Ok(result) => {
                        // 重置失败计数
                        self.failure_count.store(0, Ordering::Relaxed);
                        Ok(result)
                    }
                    Err(err) => {
                        self.record_failure();
                        Err(CircuitBreakerError::CallFailed(err))
                    }
                }
            }
        }
    }
    
    fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        let mut last_failure = self.last_failure_time.lock().unwrap();
        *last_failure = Some(TokioInstant::now());
    }
}

#[derive(Debug)]
pub enum CircuitBreakerError<E> {
    CircuitOpen,
    CallFailed(E),
}
```

## 形式化开发方法

### 规约驱动开发

```lean
-- B方法和TLA+风格的规约
-- 系统状态机的形式化规约

-- 银行账户系统规约
structure BankAccountSpec where
  accounts : Set AccountId
  balances : AccountId → ℕ
  
-- 系统不变量
def AccountInvariant (state : BankAccountSpec) : Prop :=
  ∀ acc ∈ state.accounts, state.balances acc ≥ 0

-- 操作规约
def Deposit (state : BankAccountSpec) (acc : AccountId) (amount : ℕ) : BankAccountSpec :=
  { state with balances := fun a => if a = acc then state.balances a + amount else state.balances a }

def Withdraw (state : BankAccountSpec) (acc : AccountId) (amount : ℕ) : Option BankAccountSpec :=
  if state.balances acc ≥ amount then
    some { state with balances := fun a => if a = acc then state.balances a - amount else state.balances a }
  else
    none

-- 操作的前置条件和后置条件
theorem deposit_preserves_invariant (state : BankAccountSpec) (acc : AccountId) (amount : ℕ)
  (h : AccountInvariant state) :
  AccountInvariant (Deposit state acc amount) := by
  unfold AccountInvariant Deposit
  intro acc' h_mem
  simp
  split_ifs with h_eq
  · -- acc' = acc的情况
    rw [h_eq]
    linarith [h acc h_mem]
  · -- acc' ≠ acc的情况
    exact h acc' h_mem

theorem withdraw_preserves_invariant (state : BankAccountSpec) (acc : AccountId) (amount : ℕ)
  (h : AccountInvariant state) :
  ∀ new_state, Withdraw state acc amount = some new_state → AccountInvariant new_state := by
  intro new_state h_withdraw
  unfold AccountInvariant Withdraw at h_withdraw ⊢
  split at h_withdraw
  · case pos h_sufficient =>
    injection h_withdraw with h_eq
    rw [← h_eq]
    intro acc' h_mem
    simp
    split_ifs with h_eq_acc
    · rw [h_eq_acc]
      linarith [h_sufficient]
    · exact h acc' h_mem
  · case neg =>
    contradiction

-- 活性属性：系统最终会达到某个状态
def EventuallyConsistent (states : ℕ → BankAccountSpec) : Prop :=
  ∃ n, ∀ m ≥ n, ∀ acc ∈ states m |>.accounts, 
    states m |>.balances acc = states n |>.balances acc

-- 安全属性：坏事永远不会发生
def SafetyProperty (states : ℕ → BankAccountSpec) : Prop :=
  ∀ n, AccountInvariant (states n)
```

## 精益软件开发

### 价值流映射

```haskell
-- 价值流建模
data ValueStreamStep = ValueStreamStep
  { stepName :: Text
  , processTime :: Duration
  , leadTime :: Duration
  , reworkRate :: Double
  , batchSize :: Int
  } deriving (Show)

data ValueStream = ValueStream
  { steps :: [ValueStreamStep]
  , totalLeadTime :: Duration
  , totalProcessTime :: Duration
  , flowEfficiency :: Double
  } deriving (Show)

-- 计算价值流指标
calculateValueStream :: [ValueStreamStep] -> ValueStream
calculateValueStream steps = 
  let totalProcess = sum $ map processTime steps
      totalLead = sum $ map leadTime steps
      efficiency = if totalLead == 0 then 0 else realToFrac totalProcess / realToFrac totalLead
  in ValueStream
    { steps = steps
    , totalLeadTime = totalLead
    , totalProcessTime = totalProcess  
    , flowEfficiency = efficiency
    }

-- 浪费识别
data WasteType 
  = Overproduction
  | Waiting
  | Transportation
  | OverProcessing
  | Inventory
  | Motion
  | Defects
  | UnusedTalent
  deriving (Show, Eq)

data Waste = Waste
  { wasteType :: WasteType
  , description :: Text
  , impact :: WasteImpact
  , location :: Text
  } deriving (Show)

data WasteImpact = WasteImpact
  { timeLoss :: Duration
  , costImpact :: Money
  , qualityImpact :: Double
  } deriving (Show)

-- 持续改进(Kaizen)
data Improvement = Improvement
  { problemStatement :: Text
  , currentState :: Text
  , targetState :: Text
  , actions :: [Action]
  , metrics :: [Metric]
  } deriving (Show)

data Action = Action
  { actionDescription :: Text
  , responsible :: Text
  , dueDate :: Day
  , status :: ActionStatus
  } deriving (Show)

data ActionStatus = NotStarted | InProgress | Completed | Blocked
  deriving (Show, Eq)

data Metric = Metric
  { metricName :: Text
  , currentValue :: Double
  , targetValue :: Double
  , unit :: Text
  } deriving (Show)
```

## 总结

现代软件开发方法论的核心原则：

1. **迭代和增量**: 通过短周期迭代快速交付价值
2. **协作和沟通**: 团队成员之间的密切协作
3. **适应性**: 快速响应变化和反馈
4. **质量内建**: 通过自动化测试和持续集成保证质量
5. **用户中心**: 以用户价值为导向的开发
6. **持续改进**: 基于数据和反馈的持续优化

函数式编程和形式方法为这些方法论提供了：

- **类型安全**: 编译时错误检测
- **测试能力**: 属性测试和形式验证
- **并发安全**: 不可变性和纯函数
- **可维护性**: 清晰的抽象和模块化
- **可预测性**: 数学基础保证的行为一致性

通过结合现代开发方法论和函数式编程范式，我们能够构建更可靠、更可维护、更具适应性的软件系统。
