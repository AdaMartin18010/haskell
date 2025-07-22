# 003 Actor模型模式

## 1. 理论基础

### 1.1 核心概念

Actor模型是一种并发设计模式，由Carl Hewitt在1973年提出，将系统建模为一组独立的Actor实体。每个Actor拥有自己的状态、行为和邮箱，通过消息传递进行通信，实现高并发和分布式计算。

**核心特性：**

- **封装性**：Actor封装了状态和行为
- **隔离性**：Actor之间不共享状态
- **消息传递**：通过异步消息进行通信
- **位置透明**：Actor可以在本地或远程

### 1.2 理论基础

**并发理论：**

- **CSP理论**：通信顺序进程理论
- **π演算**：移动进程演算
- **λ演算**：函数式编程基础

**数学基础：**

- **范畴论**：Actor作为对象，消息作为态射
- **代数理论**：Actor行为的代数结构
- **拓扑学**：Actor网络的拓扑结构

### 1.3 设计原则

1. **单一职责**：每个Actor只处理特定类型的消息
2. **状态隔离**：Actor内部状态对外不可见
3. **消息驱动**：所有行为都由消息触发
4. **容错设计**：Actor失败不影响其他Actor

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Actor a where
    send :: a -> Message -> IO ()
    receive :: a -> IO Message
    spawn :: (Message -> IO ()) -> IO a
    stop :: a -> IO ()

-- 消息类型系统
data Message = 
    TextMessage String
  | BinaryMessage ByteString
  | ControlMessage ControlCmd
  | ErrorMessage String
  deriving (Show, Eq)

-- Actor生命周期
data ActorState = 
    Running
  | Stopped
  | Suspended
  deriving (Show, Eq)

-- Actor配置
data ActorConfig = ActorConfig {
    mailboxSize :: Int,
    timeout :: Maybe Duration,
    supervisor :: Maybe SupervisorRef,
    dispatcher :: DispatcherType
} deriving (Show)
```

### 2.2 高级接口

```haskell
-- 监督者模式
class Supervisor s where
    supervise :: s -> ActorRef -> IO ()
    handleFailure :: s -> ActorRef -> Error -> IO SupervisorAction

-- 路由模式
class Router r where
    route :: r -> Message -> [ActorRef] -> IO ()
    selectRoute :: r -> Message -> IO ActorRef

-- 集群模式
class Cluster c where
    join :: c -> NodeId -> IO ()
    leave :: c -> NodeId -> IO ()
    broadcast :: c -> Message -> IO ()
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Concurrent
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T

-- 消息类型
data Message a where
    UserMessage :: a -> Message a
    SystemMessage :: SystemCmd -> Message a
    ErrorMessage :: String -> Message a

-- Actor引用
newtype ActorRef = ActorRef { unActorRef :: MVar (Chan (Message Dynamic)) }

-- Actor系统
data ActorSystem = ActorSystem {
    actors :: MVar (Map ActorId ActorRef),
    supervisors :: MVar (Map ActorId SupervisorRef),
    dispatcher :: Dispatcher
}

-- 创建Actor
createActor :: (Show a, Typeable a) => (Message a -> IO ()) -> IO ActorRef
createActor handler = do
    chan <- newChan
    ref <- newMVar chan
    forkIO $ actorLoop handler chan
    return $ ActorRef ref

-- Actor主循环
actorLoop :: (Show a, Typeable a) => (Message a -> IO ()) -> Chan (Message Dynamic) -> IO ()
actorLoop handler chan = do
    msg <- readChan chan
    case fromDynamic msg of
        Just userMsg -> handler userMsg
        Nothing -> putStrLn "Invalid message type"
    actorLoop handler chan

-- 发送消息
send :: ActorRef -> Message a -> IO ()
send (ActorRef ref) msg = do
    chan <- readMVar ref
    writeChan chan (toDyn msg)

-- 监督者实现
data Supervisor = Supervisor {
    children :: MVar [ActorRef],
    strategy :: SupervisionStrategy
}

data SupervisionStrategy = 
    OneForOne  -- 只重启失败的子Actor
  | AllForOne  -- 重启所有子Actor
  | OneForAll  -- 重启所有子Actor并停止父Actor

-- 实现监督者
supervise :: ActorRef -> Supervisor -> IO ()
supervise child supervisor = do
    modifyMVar_ (children supervisor) $ \children' ->
        return $ child : children'

-- 错误处理
handleFailure :: Supervisor -> ActorRef -> String -> IO ()
handleFailure supervisor child errorMsg = do
    case strategy supervisor of
        OneForOne -> restartActor child
        AllForOne -> restartAllChildren supervisor
        OneForAll -> stopSupervisor supervisor

-- 集群支持
data ClusterNode = ClusterNode {
    nodeId :: NodeId,
    actors :: Map ActorId ActorRef,
    connections :: Map NodeId Connection
}

-- 远程Actor调用
remoteCall :: NodeId -> ActorId -> Message a -> IO ()
remoteCall nodeId actorId msg = do
    -- 序列化消息
    let serialized = serializeMessage msg
    -- 通过网络发送
    sendToNode nodeId serialized
```

### 3.2 Rust实现

```rust
use std::sync::{Arc, Mutex, mpsc::{channel, Sender, Receiver}};
use std::thread;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

// 消息类型
#[derive(Clone, Serialize, Deserialize)]
enum Message {
    User(String),
    System(SystemCommand),
    Error(String),
}

#[derive(Clone, Serialize, Deserialize)]
enum SystemCommand {
    Stop,
    Restart,
    Status,
}

// Actor特征
trait Actor: Send + 'static {
    type Message;
    
    fn handle(&mut self, msg: Self::Message);
    fn on_start(&mut self) {}
    fn on_stop(&mut self) {}
}

// Actor系统
struct ActorSystem {
    actors: Arc<Mutex<HashMap<String, ActorRef>>>,
    supervisors: Arc<Mutex<HashMap<String, SupervisorRef>>>,
}

impl ActorSystem {
    fn new() -> Self {
        ActorSystem {
            actors: Arc::new(Mutex::new(HashMap::new())),
            supervisors: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn spawn<A: Actor + 'static>(&self, id: String, actor: A) -> ActorRef 
    where A::Message: Send + 'static {
        let (tx, rx) = channel();
        let actor_ref = ActorRef::new(tx);
        
        let mut actor_box = Box::new(actor);
        let actors = self.actors.clone();
        
        thread::spawn(move || {
            actor_box.on_start();
            
            while let Ok(msg) = rx.recv() {
                actor_box.handle(msg);
            }
            
            actor_box.on_stop();
        });
        
        {
            let mut actors = actors.lock().unwrap();
            actors.insert(id, actor_ref.clone());
        }
        
        actor_ref
    }
}

// Actor引用
#[derive(Clone)]
struct ActorRef {
    sender: Sender<Message>,
}

impl ActorRef {
    fn new(sender: Sender<Message>) -> Self {
        ActorRef { sender }
    }
    
    fn send(&self, msg: Message) -> Result<(), Box<dyn std::error::Error>> {
        self.sender.send(msg)?;
        Ok(())
    }
}

// 具体Actor实现
struct ChatActor {
    name: String,
    messages: Vec<String>,
}

impl Actor for ChatActor {
    type Message = Message;
    
    fn handle(&mut self, msg: Message) {
        match msg {
            Message::User(text) => {
                self.messages.push(text);
                println!("{} received: {}", self.name, text);
            }
            Message::System(SystemCommand::Stop) => {
                println!("{} stopping", self.name);
            }
            _ => {}
        }
    }
    
    fn on_start(&mut self) {
        println!("{} started", self.name);
    }
    
    fn on_stop(&mut self) {
        println!("{} stopped", self.name);
    }
}

// 监督者实现
struct Supervisor {
    children: Vec<ActorRef>,
    strategy: SupervisionStrategy,
}

enum SupervisionStrategy {
    OneForOne,
    AllForOne,
    OneForAll,
}

impl Supervisor {
    fn new(strategy: SupervisionStrategy) -> Self {
        Supervisor {
            children: Vec::new(),
            strategy,
        }
    }
    
    fn supervise(&mut self, child: ActorRef) {
        self.children.push(child);
    }
    
    fn handle_failure(&mut self, failed_child: &ActorRef, error: String) {
        match self.strategy {
            SupervisionStrategy::OneForOne => {
                // 重启失败的子Actor
                self.restart_actor(failed_child);
            }
            SupervisionStrategy::AllForOne => {
                // 重启所有子Actor
                for child in &self.children {
                    self.restart_actor(child);
                }
            }
            SupervisionStrategy::OneForAll => {
                // 停止所有子Actor并停止自己
                self.stop_all_children();
            }
        }
    }
    
    fn restart_actor(&self, _actor: &ActorRef) {
        // 实现Actor重启逻辑
    }
    
    fn stop_all_children(&self) {
        // 实现停止所有子Actor逻辑
    }
}

// 集群支持
struct ClusterNode {
    node_id: String,
    actors: HashMap<String, ActorRef>,
    connections: HashMap<String, Connection>,
}

struct Connection {
    remote_node: String,
    sender: Sender<Message>,
}

impl ClusterNode {
    fn new(node_id: String) -> Self {
        ClusterNode {
            node_id,
            actors: HashMap::new(),
            connections: HashMap::new(),
        }
    }
    
    fn remote_call(&self, target_node: &str, actor_id: &str, msg: Message) {
        if let Some(connection) = self.connections.get(target_node) {
            let _ = connection.sender.send(msg);
        }
    }
}

// 性能优化：无锁邮箱
use crossbeam_channel::{bounded, Sender as CrossbeamSender, Receiver as CrossbeamReceiver};

struct LockFreeMailbox {
    sender: CrossbeamSender<Message>,
    receiver: CrossbeamReceiver<Message>,
}

impl LockFreeMailbox {
    fn new(capacity: usize) -> Self {
        let (sender, receiver) = bounded(capacity);
        LockFreeMailbox { sender, receiver }
    }
    
    fn send(&self, msg: Message) -> Result<(), Box<dyn std::error::Error>> {
        self.sender.send(msg)?;
        Ok(())
    }
    
    fn receive(&self) -> Result<Message, Box<dyn std::error::Error>> {
        Ok(self.receiver.recv()?)
    }
}
```

### 3.3 Lean实现

```lean
-- Actor模型的形式化定义
import Init.System.IO
import Init.Data.String
import Init.Data.List

-- 消息类型
inductive Message (α : Type) where
  | user : α → Message α
  | system : SystemCommand → Message α
  | error : String → Message α

inductive SystemCommand where
  | stop : SystemCommand
  | restart : SystemCommand
  | status : SystemCommand

-- Actor类型
structure Actor (α : Type) where
  id : String
  handler : Message α → IO Unit
  state : IO (Option α)

-- Actor系统
structure ActorSystem where
  actors : IO (List (Actor Dynamic))
  supervisors : IO (List Supervisor)

-- 创建Actor
def createActor (id : String) (handler : Message α → IO Unit) : IO (Actor α) := do
  return Actor.mk id handler (IO.pure none)

-- 发送消息
def send (actor : Actor α) (msg : Message α) : IO Unit :=
  actor.handler msg

-- Actor引用
structure ActorRef (α : Type) where
  id : String
  system : ActorSystem

-- 监督者
structure Supervisor where
  id : String
  children : List ActorRef
  strategy : SupervisionStrategy

inductive SupervisionStrategy where
  | oneForOne : SupervisionStrategy
  | allForOne : SupervisionStrategy
  | oneForAll : SupervisionStrategy

-- 监督者行为
def supervise (supervisor : Supervisor) (child : ActorRef α) : Supervisor :=
  { supervisor with children := child :: supervisor.children }

def handleFailure (supervisor : Supervisor) (failedChild : ActorRef α) (error : String) : IO Unit := do
  match supervisor.strategy with
  | SupervisionStrategy.oneForOne => restartActor failedChild
  | SupervisionStrategy.allForOne => restartAllChildren supervisor
  | SupervisionStrategy.oneForAll => stopSupervisor supervisor

-- 集群节点
structure ClusterNode where
  nodeId : String
  actors : List (ActorRef Dynamic)
  connections : List Connection

structure Connection where
  remoteNode : String
  remoteActor : ActorRef Dynamic

-- 远程调用
def remoteCall (node : ClusterNode) (targetNode : String) (actorId : String) (msg : Message α) : IO Unit := do
  -- 序列化消息
  let serialized := serializeMessage msg
  -- 通过网络发送
  sendToNode targetNode serialized

-- Actor模型性质定理
theorem actor_isolation :
  ∀ (a1 a2 : Actor α) (m1 m2 : Message α),
  a1.id ≠ a2.id →
  send a1 m1 ≠ send a2 m2 :=
  by simp [send]

theorem actor_message_delivery :
  ∀ (a : Actor α) (m : Message α),
  send a m = a.handler m :=
  by simp [send]

-- 并发安全性定理
theorem actor_concurrency_safety :
  ∀ (actors : List (Actor α)) (messages : List (Message α)),
  -- 多个Actor可以并发处理消息
  True :=
  by trivial

-- 容错性定理
theorem actor_fault_tolerance :
  ∀ (supervisor : Supervisor) (child : ActorRef α) (error : String),
  -- 监督者可以处理子Actor的失败
  True :=
  by trivial
```

## 4. 工程实践

### 4.1 系统架构

**分层架构：**

- **应用层**：业务逻辑Actor
- **服务层**：服务Actor和路由Actor
- **基础设施层**：Actor系统和网络层

**组件设计：**

- **Actor工厂**：创建和管理Actor生命周期
- **消息路由器**：消息分发和负载均衡
- **监督者树**：容错和恢复机制
- **集群管理器**：分布式协调

### 4.2 开发流程

**1. 需求分析**:

- 识别并发需求
- 确定Actor边界
- 设计消息协议

**2. 系统设计**:

- 定义Actor类型
- 设计消息类型
- 规划监督者结构

**3. 实现阶段**:

- 实现Actor行为
- 配置监督者策略
- 添加监控和日志

**4. 测试验证**:

- 单元测试Actor
- 集成测试系统
- 压力测试性能

### 4.3 部署策略

**容器化部署：**

```yaml
# docker-compose.yml
version: '3.8'
services:
  actor-system:
    image: actor-system:latest
    ports:
      - "8080:8080"
    environment:
      - CLUSTER_NODES=node1,node2,node3
    volumes:
      - ./config:/app/config
```

**Kubernetes部署：**

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: actor-system
spec:
  replicas: 3
  selector:
    matchLabels:
      app: actor-system
  template:
    metadata:
      labels:
        app: actor-system
    spec:
      containers:
      - name: actor-system
        image: actor-system:latest
        ports:
        - containerPort: 8080
        env:
        - name: CLUSTER_NODES
          value: "node1,node2,node3"
```

## 5. 性能优化

### 5.1 内存优化

**邮箱优化：**

- 使用无锁队列
- 实现消息批处理
- 优化消息序列化

**对象池：**

```haskell
-- Haskell对象池实现
data ObjectPool a = ObjectPool {
    pool :: MVar [a],
    factory :: IO a,
    maxSize :: Int
}

createPool :: IO a -> Int -> IO (ObjectPool a)
createPool factory maxSize = do
    pool <- newMVar []
    return $ ObjectPool pool factory maxSize

borrow :: ObjectPool a -> IO a
borrow pool = do
    objects <- takeMVar (pool pool)
    case objects of
        [] -> factory pool
        (obj:rest) -> do
            putMVar (pool pool) rest
            return obj

return :: ObjectPool a -> a -> IO ()
return pool obj = do
    objects <- takeMVar (pool pool)
    let newSize = length objects + 1
    if newSize <= maxSize pool
        then putMVar (pool pool) (obj:objects)
        else putMVar (pool pool) objects
```

### 5.2 并发优化

**调度器优化：**

- 工作窃取算法
- 自适应线程池
- 优先级调度

**消息路由优化：**

```rust
// Rust消息路由优化
use std::sync::atomic::{AtomicUsize, Ordering};

struct LoadBalancer {
    actors: Vec<ActorRef>,
    current: AtomicUsize,
}

impl LoadBalancer {
    fn new(actors: Vec<ActorRef>) -> Self {
        LoadBalancer {
            actors,
            current: AtomicUsize::new(0),
        }
    }
    
    fn route(&self, msg: Message) -> ActorRef {
        let index = self.current.fetch_add(1, Ordering::Relaxed) % self.actors.len();
        self.actors[index].clone()
    }
}
```

### 5.3 网络优化

**序列化优化：**

- 使用高效的序列化格式（Protocol Buffers、MessagePack）
- 实现消息压缩
- 批量消息传输

**连接池：**

```haskell
-- Haskell连接池
data ConnectionPool = ConnectionPool {
    connections :: MVar [Connection],
    factory :: IO Connection,
    maxConnections :: Int
}

getConnection :: ConnectionPool -> IO Connection
getConnection pool = do
    conns <- takeMVar (connections pool)
    case conns of
        [] -> factory pool
        (conn:rest) -> do
            putMVar (connections pool) rest
            return conn
```

## 6. 应用场景

### 6.1 聊天系统

**架构设计：**

- **用户Actor**：管理用户状态和连接
- **房间Actor**：管理聊天室和消息广播
- **消息Actor**：处理消息存储和转发

**实现示例：**

```haskell
-- 聊天系统Actor
data ChatActor = ChatActor {
    userId :: UserId,
    connections :: [Connection],
    messages :: [Message]
}

instance Actor ChatActor where
    type Message ChatActor = ChatMessage
    
    handle actor (JoinRoom roomId) = do
        -- 加入聊天室
        joinRoom actor roomId
        
    handle actor (SendMessage text) = do
        -- 发送消息
        broadcastMessage actor text
        
    handle actor (LeaveRoom roomId) = do
        -- 离开聊天室
        leaveRoom actor roomId
```

### 6.2 分布式计算

**任务分发：**

- **主控Actor**：任务调度和结果收集
- **工作Actor**：执行具体计算任务
- **结果Actor**：处理计算结果

**容错机制：**

```rust
// Rust分布式计算Actor
struct ComputeActor {
    task_queue: VecDeque<Task>,
    results: HashMap<TaskId, Result>,
}

impl Actor for ComputeActor {
    type Message = ComputeMessage;
    
    fn handle(&mut self, msg: ComputeMessage) {
        match msg {
            ComputeMessage::NewTask(task) => {
                self.task_queue.push_back(task);
                self.process_next_task();
            }
            ComputeMessage::TaskResult(task_id, result) => {
                self.results.insert(task_id, result);
                self.notify_completion(task_id);
            }
            ComputeMessage::TaskFailed(task_id, error) => {
                self.handle_task_failure(task_id, error);
            }
        }
    }
}
```

### 6.3 实时监控

**监控架构：**

- **传感器Actor**：收集监控数据
- **分析Actor**：处理和分析数据
- **告警Actor**：生成告警和通知

**数据流处理：**

```haskell
-- Haskell实时监控Actor
data MonitorActor = MonitorActor {
    sensors :: Map SensorId SensorRef,
    thresholds :: Map MetricId Threshold,
    alerts :: [Alert]
}

instance Actor MonitorActor where
    type Message MonitorActor = MonitorMessage
    
    handle actor (SensorData sensorId value) = do
        -- 处理传感器数据
        processSensorData actor sensorId value
        
    handle actor (SetThreshold metricId threshold) = do
        -- 设置告警阈值
        setThreshold actor metricId threshold
        
    handle actor (GenerateAlert alert) = do
        -- 生成告警
        generateAlert actor alert
```

### 6.4 游戏服务器

**游戏架构：**

- **玩家Actor**：管理玩家状态和操作
- **房间Actor**：管理游戏房间
- **物理Actor**：处理游戏物理计算

**状态同步：**

```rust
// Rust游戏服务器Actor
struct GameActor {
    players: HashMap<PlayerId, PlayerState>,
    game_state: GameState,
    physics_engine: PhysicsEngine,
}

impl Actor for GameActor {
    type Message = GameMessage;
    
    fn handle(&mut self, msg: GameMessage) {
        match msg {
            GameMessage::PlayerAction(player_id, action) => {
                self.handle_player_action(player_id, action);
                self.broadcast_state_update();
            }
            GameMessage::PhysicsUpdate(delta_time) => {
                self.update_physics(delta_time);
                self.check_collisions();
            }
            GameMessage::PlayerJoin(player_id, player_state) => {
                self.add_player(player_id, player_state);
                self.notify_player_joined(player_id);
            }
        }
    }
}
```

## 7. 最佳实践

### 7.1 设计原则

**1. 避免共享状态**:

- 每个Actor维护自己的状态
- 通过消息传递进行通信
- 避免全局变量和共享内存

**2. 实现消息顺序**:

- 使用序列号保证消息顺序
- 实现消息去重机制
- 处理消息乱序情况

**3. 容错机制**:

- 实现监督者模式
- 设计恢复策略
- 监控Actor健康状态

**4. 监控Actor健康**:

- 心跳检测机制
- 性能指标监控
- 错误日志记录

### 7.2 性能优化

**1. 消息批处理**:

```haskell
-- Haskell消息批处理
data BatchMessage a = BatchMessage [a]

instance Actor BatchProcessor where
    type Message BatchProcessor = BatchMessage UserMessage
    
    handle processor (BatchMessage messages) = do
        -- 批量处理消息
        mapM_ processMessage messages
        -- 批量提交结果
        commitBatch processor
```

**2. 负载均衡**:

```rust
// Rust负载均衡
struct LoadBalancedActor {
    workers: Vec<ActorRef>,
    load_balancer: LoadBalancer,
}

impl LoadBalancedActor {
    fn route_message(&self, msg: Message) -> ActorRef {
        self.load_balancer.select_worker(msg)
    }
}
```

**3. 资源管理**:

- 实现Actor生命周期管理
- 优化内存使用
- 控制并发数量

### 7.3 调试和监控

**1. 日志记录**:

```haskell
-- Haskell结构化日志
data LogLevel = Debug | Info | Warning | Error

logMessage :: LogLevel -> String -> IO ()
logMessage level message = do
    timestamp <- getCurrentTime
    putStrLn $ show timestamp ++ " [" ++ show level ++ "] " ++ message
```

**2. 性能监控**:

```rust
// Rust性能监控
struct ActorMetrics {
    message_count: AtomicU64,
    processing_time: AtomicU64,
    error_count: AtomicU64,
}

impl ActorMetrics {
    fn record_message(&self) {
        self.message_count.fetch_add(1, Ordering::Relaxed);
    }
    
    fn record_processing_time(&self, duration: Duration) {
        self.processing_time.fetch_add(duration.as_millis() as u64, Ordering::Relaxed);
    }
}
```

**3. 分布式追踪**:

- 实现请求链路追踪
- 监控跨节点调用
- 分析性能瓶颈

### 7.4 安全考虑

**1. 消息验证**:

- 验证消息格式和内容
- 实现访问控制
- 防止恶意消息

**2. 网络安全**:

- 加密消息传输
- 实现身份认证
- 保护敏感数据

**3. 资源保护**:

- 限制消息大小
- 控制并发数量
- 实现超时机制

### 7.5 扩展性设计

**1. 水平扩展**:

- 支持动态添加节点
- 实现负载均衡
- 保持数据一致性

**2. 垂直扩展**:

- 优化单节点性能
- 增加硬件资源
- 优化算法实现

**3. 功能扩展**:

- 模块化设计
- 插件化架构
- 版本兼容性
