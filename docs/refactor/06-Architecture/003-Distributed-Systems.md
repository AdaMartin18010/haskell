# 分布式系统

## 概述

分布式系统是由多个独立计算节点组成的系统，这些节点通过网络协作完成任务。本文档探讨函数式编程在分布式系统设计中的应用，包括一致性模型、容错机制、分布式算法等核心概念。

## 分布式系统基础

### 1. CAP定理与一致性模型

```haskell
-- 一致性模型的形式化定义
{-# LANGUAGE GADTs, TypeFamilies #-}

-- 操作类型
data Operation = Read Key | Write Key Value deriving (Show, Eq)
data Key = Key Text deriving (Show, Eq, Ord)
data Value = Value Text deriving (Show, Eq)

-- 一致性级别
data ConsistencyLevel where
  Strong :: ConsistencyLevel
  Eventual :: ConsistencyLevel  
  Causal :: ConsistencyLevel
  Sequential :: ConsistencyLevel

-- 分布式存储节点
data Node = Node
  { nodeId :: NodeId
  , nodeData :: Map Key (Value, VectorClock)
  , nodeStatus :: NodeStatus
  } deriving (Show)

newtype NodeId = NodeId Text deriving (Show, Eq, Ord)
data NodeStatus = Online | Offline | Partitioned deriving (Show, Eq)

-- 向量时钟
newtype VectorClock = VectorClock (Map NodeId Int) deriving (Show, Eq)

-- 向量时钟操作
incrementClock :: NodeId -> VectorClock -> VectorClock
incrementClock nodeId (VectorClock clocks) = 
  VectorClock $ Map.insertWith (+) nodeId 1 clocks

mergeClock :: VectorClock -> VectorClock -> VectorClock
mergeClock (VectorClock c1) (VectorClock c2) = 
  VectorClock $ Map.unionWith max c1 c2

-- 偏序关系
happensBefore :: VectorClock -> VectorClock -> Bool
happensBefore (VectorClock c1) (VectorClock c2) = 
  let allNodes = Map.keys $ Map.union c1 c2
      c1' = foldr (Map.adjust id) c1 [k | k <- allNodes, not (k `Map.member` c1)]
      c2' = foldr (Map.adjust id) c2 [k | k <- allNodes, not (k `Map.member` c2)]
  in c1' /= c2' && Map.isSubmapOfBy (<=) c1' c2'

-- 分布式存储系统
class Monad m => DistributedStore m where
  get :: ConsistencyLevel -> Key -> m (Maybe Value)
  put :: ConsistencyLevel -> Key -> Value -> m Bool
  replicate :: Key -> Value -> [NodeId] -> m [Bool]
  
-- Quorum读写
data QuorumConfig = QuorumConfig
  { replicationFactor :: Int
  , readQuorum :: Int  
  , writeQuorum :: Int
  } deriving (Show)

-- Quorum操作
quorumRead :: (DistributedStore m) => QuorumConfig -> [NodeId] -> Key -> m (Maybe Value)
quorumRead config nodes key = do
  responses <- mapM (\nodeId -> get Strong key) (take (readQuorum config) nodes)
  let successfulReads = [v | Just v <- responses]
  return $ if length successfulReads >= readQuorum config
           then listToMaybe successfulReads
           else Nothing

quorumWrite :: (DistributedStore m) => QuorumConfig -> [NodeId] -> Key -> Value -> m Bool
quorumWrite config nodes key value = do
  results <- replicate key value (take (writeQuorum config) nodes)
  return $ length (filter id results) >= writeQuorum config
```

### 2. 分布式共识算法

```rust
// Raft共识算法实现
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::time::{Duration, Instant};

#[derive(Debug, Clone, PartialEq)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub term: u64,
    pub index: u64,
    pub command: String,
    pub committed: bool,
}

#[derive(Debug)]
pub struct RaftNode {
    pub id: NodeId,
    pub state: NodeState,
    pub current_term: u64,
    pub voted_for: Option<NodeId>,
    pub log: Vec<LogEntry>,
    pub commit_index: u64,
    pub last_applied: u64,
    pub next_index: HashMap<NodeId, u64>,
    pub match_index: HashMap<NodeId, u64>,
    pub peers: Vec<NodeId>,
    pub leader_id: Option<NodeId>,
    pub election_timeout: Duration,
    pub last_heartbeat: Instant,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NodeId(pub String);

impl RaftNode {
    pub fn new(id: NodeId, peers: Vec<NodeId>) -> Self {
        Self {
            id,
            state: NodeState::Follower,
            current_term: 0,
            voted_for: None,
            log: vec![],
            commit_index: 0,
            last_applied: 0,
            next_index: HashMap::new(),
            match_index: HashMap::new(),
            peers,
            leader_id: None,
            election_timeout: Duration::from_millis(150 + rand::random::<u64>() % 150),
            last_heartbeat: Instant::now(),
        }
    }
    
    // 开始选举
    pub fn start_election(&mut self) -> Vec<VoteRequest> {
        self.state = NodeState::Candidate;
        self.current_term += 1;
        self.voted_for = Some(self.id.clone());
        self.last_heartbeat = Instant::now();
        
        let last_log_index = self.log.len() as u64;
        let last_log_term = self.log.last().map(|e| e.term).unwrap_or(0);
        
        self.peers.iter().map(|peer_id| VoteRequest {
            term: self.current_term,
            candidate_id: self.id.clone(),
            last_log_index,
            last_log_term,
            target: peer_id.clone(),
        }).collect()
    }
    
    // 处理投票请求
    pub fn handle_vote_request(&mut self, request: VoteRequest) -> VoteResponse {
        let mut vote_granted = false;
        
        if request.term > self.current_term {
            self.current_term = request.term;
            self.voted_for = None;
            self.state = NodeState::Follower;
        }
        
        if request.term == self.current_term &&
           (self.voted_for.is_none() || self.voted_for == Some(request.candidate_id.clone())) {
            
            let last_log_index = self.log.len() as u64;
            let last_log_term = self.log.last().map(|e| e.term).unwrap_or(0);
            
            if request.last_log_term > last_log_term ||
               (request.last_log_term == last_log_term && request.last_log_index >= last_log_index) {
                vote_granted = true;
                self.voted_for = Some(request.candidate_id.clone());
                self.last_heartbeat = Instant::now();
            }
        }
        
        VoteResponse {
            term: self.current_term,
            vote_granted,
            from: self.id.clone(),
        }
    }
    
    // 处理投票响应
    pub fn handle_vote_response(&mut self, response: VoteResponse) -> Option<Vec<AppendEntries>> {
        if response.term > self.current_term {
            self.current_term = response.term;
            self.voted_for = None;
            self.state = NodeState::Follower;
            return None;
        }
        
        if self.state == NodeState::Candidate && response.vote_granted {
            let votes = 1; // 简化：应该计算收到的票数
            let majority = (self.peers.len() + 1) / 2 + 1;
            
            if votes >= majority {
                self.become_leader()
            } else {
                None
            }
        } else {
            None
        }
    }
    
    // 成为领导者
    fn become_leader(&mut self) -> Option<Vec<AppendEntries>> {
        self.state = NodeState::Leader;
        self.leader_id = Some(self.id.clone());
        
        // 初始化next_index和match_index
        for peer in &self.peers {
            self.next_index.insert(peer.clone(), self.log.len() as u64 + 1);
            self.match_index.insert(peer.clone(), 0);
        }
        
        // 发送心跳
        Some(self.create_heartbeats())
    }
    
    // 创建心跳消息
    fn create_heartbeats(&self) -> Vec<AppendEntries> {
        self.peers.iter().map(|peer_id| {
            let prev_log_index = self.next_index.get(peer_id).unwrap_or(&1) - 1;
            let prev_log_term = if prev_log_index > 0 {
                self.log.get((prev_log_index - 1) as usize).map(|e| e.term).unwrap_or(0)
            } else {
                0
            };
            
            AppendEntries {
                term: self.current_term,
                leader_id: self.id.clone(),
                prev_log_index,
                prev_log_term,
                entries: vec![], // 心跳不包含条目
                leader_commit: self.commit_index,
                target: peer_id.clone(),
            }
        }).collect()
    }
    
    // 处理AppendEntries请求
    pub fn handle_append_entries(&mut self, request: AppendEntries) -> AppendEntriesResponse {
        let mut success = false;
        
        if request.term >= self.current_term {
            self.current_term = request.term;
            self.state = NodeState::Follower;
            self.leader_id = Some(request.leader_id.clone());
            self.last_heartbeat = Instant::now();
            
            // 检查日志一致性
            if request.prev_log_index == 0 || 
               (request.prev_log_index <= self.log.len() as u64 &&
                self.log.get((request.prev_log_index - 1) as usize)
                    .map(|e| e.term).unwrap_or(0) == request.prev_log_term) {
                
                success = true;
                
                // 添加新条目
                let mut log_index = request.prev_log_index as usize;
                for entry in request.entries {
                    if log_index < self.log.len() {
                        if self.log[log_index].term != entry.term {
                            self.log.truncate(log_index);
                            self.log.push(entry);
                        }
                    } else {
                        self.log.push(entry);
                    }
                    log_index += 1;
                }
                
                // 更新commit_index
                if request.leader_commit > self.commit_index {
                    self.commit_index = std::cmp::min(request.leader_commit, self.log.len() as u64);
                }
            }
        }
        
        AppendEntriesResponse {
            term: self.current_term,
            success,
            match_index: if success { request.prev_log_index + request.entries.len() as u64 } else { 0 },
            from: self.id.clone(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VoteRequest {
    pub term: u64,
    pub candidate_id: NodeId,
    pub last_log_index: u64,
    pub last_log_term: u64,
    pub target: NodeId,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VoteResponse {
    pub term: u64,
    pub vote_granted: bool,
    pub from: NodeId,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntries {
    pub term: u64,
    pub leader_id: NodeId,
    pub prev_log_index: u64,
    pub prev_log_term: u64,
    pub entries: Vec<LogEntry>,
    pub leader_commit: u64,
    pub target: NodeId,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesResponse {
    pub term: u64,
    pub success: bool,
    pub match_index: u64,
    pub from: NodeId,
}
```

## 分布式通信模式

### 1. Actor模型

```rust
// Actor模型实现
use tokio::sync::{mpsc, oneshot};
use std::collections::HashMap;
use async_trait::async_trait;

// Actor特质
#[async_trait]
pub trait Actor: Send + 'static {
    type Message: Send;
    type Error: Send;
    
    async fn handle(&mut self, message: Self::Message) -> Result<(), Self::Error>;
    
    async fn pre_start(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    
    async fn post_stop(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

// Actor引用
#[derive(Clone)]
pub struct ActorRef<M> {
    sender: mpsc::UnboundedSender<M>,
    name: String,
}

impl<M> ActorRef<M> {
    pub fn tell(&self, message: M) -> Result<(), ActorError> {
        self.sender.send(message)
            .map_err(|_| ActorError::MailboxClosed)
    }
    
    pub fn name(&self) -> &str {
        &self.name
    }
}

// Actor系统
pub struct ActorSystem {
    actors: HashMap<String, Box<dyn std::any::Any + Send>>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self {
            actors: HashMap::new(),
        }
    }
    
    pub async fn spawn<A>(&mut self, name: String, mut actor: A) -> ActorRef<A::Message>
    where
        A: Actor,
    {
        let (sender, mut receiver) = mpsc::unbounded_channel::<A::Message>();
        
        // 启动actor
        let actor_name = name.clone();
        tokio::spawn(async move {
            if let Err(_) = actor.pre_start().await {
                return;
            }
            
            while let Some(message) = receiver.recv().await {
                if let Err(_) = actor.handle(message).await {
                    break;
                }
            }
            
            let _ = actor.post_stop().await;
        });
        
        let actor_ref = ActorRef {
            sender: sender.clone(),
            name: name.clone(),
        };
        
        self.actors.insert(name, Box::new(sender));
        actor_ref
    }
}

// 分布式Actor
pub struct DistributedActor {
    local_system: ActorSystem,
    remote_nodes: HashMap<String, RemoteNode>,
}

pub struct RemoteNode {
    address: String,
    client: Box<dyn RemoteActorClient>,
}

#[async_trait]
pub trait RemoteActorClient: Send + Sync {
    async fn send_message(&self, actor_path: &str, message: Vec<u8>) -> Result<(), RemoteError>;
}

// 错误类型
#[derive(Debug, thiserror::Error)]
pub enum ActorError {
    #[error("Mailbox is closed")]
    MailboxClosed,
    #[error("Actor not found")]
    ActorNotFound,
}

#[derive(Debug, thiserror::Error)]
pub enum RemoteError {
    #[error("Network error: {0}")]
    NetworkError(String),
    #[error("Serialization error: {0}")]
    SerializationError(String),
}

// 示例Actor：计数器
pub struct CounterActor {
    count: i32,
}

impl CounterActor {
    pub fn new() -> Self {
        Self { count: 0 }
    }
}

#[derive(Debug)]
pub enum CounterMessage {
    Increment,
    Decrement,
    GetCount(oneshot::Sender<i32>),
}

#[async_trait]
impl Actor for CounterActor {
    type Message = CounterMessage;
    type Error = ();
    
    async fn handle(&mut self, message: Self::Message) -> Result<(), Self::Error> {
        match message {
            CounterMessage::Increment => {
                self.count += 1;
            }
            CounterMessage::Decrement => {
                self.count -= 1;
            }
            CounterMessage::GetCount(sender) => {
                let _ = sender.send(self.count);
            }
        }
        Ok(())
    }
}
```

### 2. 发布-订阅模式

```haskell
-- 分布式发布-订阅系统
{-# LANGUAGE OverloadedStrings #-}

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Concurrent.STM

-- 主题和消息
newtype Topic = Topic Text deriving (Show, Eq, Ord)
newtype Message = Message Text deriving (Show, Eq)
newtype SubscriberId = SubscriberId Text deriving (Show, Eq, Ord)

-- 订阅者信息
data Subscriber = Subscriber
  { subscriberId :: SubscriberId
  , nodeId :: NodeId
  , topicFilters :: [TopicFilter]
  , messageQueue :: TQueue Message
  } deriving (Eq)

data TopicFilter = 
  ExactMatch Topic |
  WildcardMatch Text |
  RegexMatch Text
  deriving (Show, Eq)

-- 分布式发布-订阅代理
data PubSubBroker = PubSubBroker
  { localSubscribers :: TVar (Map Topic (Set SubscriberId))
  , remoteNodes :: TVar (Map NodeId RemoteNodeInfo)
  , routingTable :: TVar (Map Topic (Set NodeId))
  , messageBuffer :: TVar [Message]
  } deriving (Eq)

data RemoteNodeInfo = RemoteNodeInfo
  { nodeAddress :: Text
  , isOnline :: Bool
  , lastHeartbeat :: UTCTime
  } deriving (Show, Eq)

-- 发布-订阅操作
class Monad m => PubSub m where
  subscribe :: Topic -> SubscriberId -> m Bool
  unsubscribe :: Topic -> SubscriberId -> m Bool
  publish :: Topic -> Message -> m Bool
  getSubscribers :: Topic -> m [SubscriberId]

-- STM实现
instance PubSub STM where
  subscribe topic subscriberId = do
    subscribers <- readTVar localSubscribers
    let currentSubs = Map.findWithDefault Set.empty topic subscribers
        newSubs = Set.insert subscriberId currentSubs
    writeTVar localSubscribers $ Map.insert topic newSubs subscribers
    return True
  
  unsubscribe topic subscriberId = do
    subscribers <- readTVar localSubscribers
    case Map.lookup topic subscribers of
      Nothing -> return False
      Just subs -> do
        let newSubs = Set.delete subscriberId subs
        writeTVar localSubscribers $ 
          if Set.null newSubs
          then Map.delete topic subscribers
          else Map.insert topic newSubs subscribers
        return True
  
  publish topic message = do
    subscribers <- readTVar localSubscribers
    case Map.lookup topic subscribers of
      Nothing -> return False
      Just subs -> do
        -- 本地分发
        mapM_ (deliverMessage message) (Set.toList subs)
        
        -- 远程分发
        routing <- readTVar routingTable
        case Map.lookup topic routing of
          Nothing -> return ()
          Just nodes -> mapM_ (forwardMessage topic message) (Set.toList nodes)
        
        return True
    where
      deliverMessage msg subId = return () -- 实际实现中需要将消息放入订阅者队列
      forwardMessage t m nodeId = return () -- 实际实现中需要转发到远程节点
  
  getSubscribers topic = do
    subscribers <- readTVar localSubscribers
    return $ Set.toList $ Map.findWithDefault Set.empty topic subscribers

-- 主题匹配
matchesTopic :: TopicFilter -> Topic -> Bool
matchesTopic (ExactMatch filterTopic) topic = filterTopic == topic
matchesTopic (WildcardMatch pattern) (Topic topicName) = 
  -- 简化的通配符匹配
  pattern `isPrefixOf` topicName || pattern `isSuffixOf` topicName
matchesTopic (RegexMatch pattern) (Topic topicName) = 
  -- 需要正则表达式库支持
  True -- 简化实现

-- 分布式路由
updateRoutingTable :: NodeId -> [Topic] -> PubSubBroker -> STM ()
updateRoutingTable nodeId topics broker = do
  routing <- readTVar (routingTable broker)
  let updatedRouting = foldl (updateTopic nodeId) routing topics
  writeTVar (routingTable broker) updatedRouting
  where
    updateTopic nodeId routing topic = 
      Map.insertWith Set.union topic (Set.singleton nodeId) routing

-- 故障检测和恢复
handleNodeFailure :: NodeId -> PubSubBroker -> STM ()
handleNodeFailure failedNodeId broker = do
  -- 从路由表中移除失败的节点
  routing <- readTVar (routingTable broker)
  let cleanedRouting = Map.map (Set.delete failedNodeId) routing
  writeTVar (routingTable broker) cleanedRouting
  
  -- 从远程节点列表中移除
  nodes <- readTVar (remoteNodes broker)
  writeTVar (remoteNodes broker) $ Map.delete failedNodeId nodes
```

## 容错与可靠性

### 1. 故障检测

```rust
// 故障检测器
use std::time::{Duration, Instant};
use std::collections::HashMap;
use tokio::time::interval;

#[derive(Debug, Clone)]
pub struct FailureDetector {
    nodes: HashMap<NodeId, NodeState>,
    phi_threshold: f64,
    window_size: usize,
    min_std_deviation: Duration,
}

#[derive(Debug, Clone)]
struct NodeState {
    arrival_intervals: Vec<Duration>,
    last_heartbeat: Instant,
    expected_interval: Duration,
    phi_values: Vec<f64>,
}

impl FailureDetector {
    pub fn new(phi_threshold: f64) -> Self {
        Self {
            nodes: HashMap::new(),
            phi_threshold,
            window_size: 100,
            min_std_deviation: Duration::from_millis(10),
        }
    }
    
    // 记录心跳
    pub fn heartbeat(&mut self, node_id: NodeId) {
        let now = Instant::now();
        
        match self.nodes.get_mut(&node_id) {
            Some(state) => {
                let interval = now.duration_since(state.last_heartbeat);
                state.arrival_intervals.push(interval);
                
                if state.arrival_intervals.len() > self.window_size {
                    state.arrival_intervals.remove(0);
                }
                
                state.last_heartbeat = now;
                self.update_phi(&node_id);
            }
            None => {
                self.nodes.insert(node_id, NodeState {
                    arrival_intervals: vec![],
                    last_heartbeat: now,
                    expected_interval: Duration::from_secs(1),
                    phi_values: vec![],
                });
            }
        }
    }
    
    // 计算phi值
    fn update_phi(&mut self, node_id: &NodeId) {
        if let Some(state) = self.nodes.get_mut(node_id) {
            if state.arrival_intervals.len() < 2 {
                return;
            }
            
            let mean = self.calculate_mean(&state.arrival_intervals);
            let std_dev = self.calculate_std_deviation(&state.arrival_intervals, mean);
            let std_dev = std_dev.max(self.min_std_deviation);
            
            let time_since_last = state.last_heartbeat.elapsed();
            let phi = self.calculate_phi(time_since_last, mean, std_dev);
            
            state.phi_values.push(phi);
            if state.phi_values.len() > self.window_size {
                state.phi_values.remove(0);
            }
        }
    }
    
    fn calculate_mean(&self, intervals: &[Duration]) -> Duration {
        let sum: Duration = intervals.iter().sum();
        sum / intervals.len() as u32
    }
    
    fn calculate_std_deviation(&self, intervals: &[Duration], mean: Duration) -> Duration {
        let variance: f64 = intervals.iter()
            .map(|&interval| {
                let diff = interval.as_secs_f64() - mean.as_secs_f64();
                diff * diff
            })
            .sum::<f64>() / intervals.len() as f64;
        
        Duration::from_secs_f64(variance.sqrt())
    }
    
    fn calculate_phi(&self, time_since_last: Duration, mean: Duration, std_dev: Duration) -> f64 {
        let t = time_since_last.as_secs_f64();
        let mean_ms = mean.as_secs_f64();
        let std_dev_ms = std_dev.as_secs_f64();
        
        if std_dev_ms == 0.0 {
            return if t > mean_ms { f64::INFINITY } else { 0.0 };
        }
        
        // 使用正态分布的累积分布函数
        let normalized = (t - mean_ms) / std_dev_ms;
        -10.0 * (1.0 - self.normal_cdf(normalized)).log10()
    }
    
    fn normal_cdf(&self, x: f64) -> f64 {
        // 正态分布累积分布函数的近似
        0.5 * (1.0 + self.erf(x / 2.0_f64.sqrt()))
    }
    
    fn erf(&self, x: f64) -> f64 {
        // 误差函数的近似实现
        let a1 = 0.254829592;
        let a2 = -0.284496736;
        let a3 = 1.421413741;
        let a4 = -1.453152027;
        let a5 = 1.061405429;
        let p = 0.3275911;
        
        let sign = if x < 0.0 { -1.0 } else { 1.0 };
        let x = x.abs();
        
        let t = 1.0 / (1.0 + p * x);
        let y = 1.0 - (((((a5 * t + a4) * t) + a3) * t + a2) * t + a1) * t * (-x * x).exp();
        
        sign * y
    }
    
    // 检查节点是否被怀疑失败
    pub fn is_suspected(&self, node_id: &NodeId) -> bool {
        self.nodes.get(node_id)
            .and_then(|state| state.phi_values.last())
            .map(|&phi| phi > self.phi_threshold)
            .unwrap_or(false)
    }
    
    // 获取节点的可疑程度
    pub fn suspicion_level(&self, node_id: &NodeId) -> f64 {
        self.nodes.get(node_id)
            .and_then(|state| state.phi_values.last())
            .copied()
            .unwrap_or(0.0)
    }
}

// 集群成员管理
#[derive(Debug, Clone)]
pub struct ClusterMembership {
    local_node: NodeId,
    members: HashMap<NodeId, MemberInfo>,
    failure_detector: FailureDetector,
}

#[derive(Debug, Clone)]
struct MemberInfo {
    status: MemberStatus,
    incarnation: u64,
    metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq)]
enum MemberStatus {
    Alive,
    Suspected,
    Dead,
    Left,
}

impl ClusterMembership {
    pub fn new(local_node: NodeId) -> Self {
        Self {
            local_node,
            members: HashMap::new(),
            failure_detector: FailureDetector::new(8.0),
        }
    }
    
    pub fn join(&mut self, node_id: NodeId, metadata: HashMap<String, String>) {
        self.members.insert(node_id, MemberInfo {
            status: MemberStatus::Alive,
            incarnation: 0,
            metadata,
        });
    }
    
    pub fn suspect(&mut self, node_id: &NodeId) {
        if let Some(member) = self.members.get_mut(node_id) {
            if member.status == MemberStatus::Alive {
                member.status = MemberStatus::Suspected;
                member.incarnation += 1;
            }
        }
    }
    
    pub fn confirm_alive(&mut self, node_id: &NodeId, incarnation: u64) {
        if let Some(member) = self.members.get_mut(node_id) {
            if incarnation >= member.incarnation {
                member.status = MemberStatus::Alive;
                member.incarnation = incarnation;
            }
        }
    }
    
    pub fn declare_dead(&mut self, node_id: &NodeId) {
        if let Some(member) = self.members.get_mut(node_id) {
            member.status = MemberStatus::Dead;
        }
    }
    
    pub fn get_alive_members(&self) -> Vec<NodeId> {
        self.members.iter()
            .filter(|(_, member)| member.status == MemberStatus::Alive)
            .map(|(id, _)| id.clone())
            .collect()
    }
}
```

### 2. 复制与分区容错

```haskell
-- 分布式复制系统
{-# LANGUAGE OverloadedStrings #-}

-- 复制策略
data ReplicationStrategy = 
  SimpleReplication Int |  -- 简单复制，指定副本数
  ConsistentHashing Int |  -- 一致性哈希
  QuorumBased QuorumConfig
  deriving (Show)

-- 数据分区
data Partition = Partition
  { partitionId :: PartitionId
  , keyRange :: (Key, Key)
  , replicas :: [NodeId]
  , primaryReplica :: NodeId
  } deriving (Show)

newtype PartitionId = PartitionId Int deriving (Show, Eq, Ord)

-- 分区管理器
data PartitionManager = PartitionManager
  { partitions :: Map PartitionId Partition
  , nodePartitions :: Map NodeId [PartitionId]
  , hashRing :: ConsistentHashRing
  } deriving (Show)

-- 一致性哈希环
data ConsistentHashRing = ConsistentHashRing
  { virtualNodes :: Map Word32 NodeId
  , replicationFactor :: Int
  } deriving (Show)

-- 创建一致性哈希环
createHashRing :: [NodeId] -> Int -> ConsistentHashRing
createHashRing nodes virtualNodeCount = 
  let virtualNodes = Map.fromList $ concatMap (createVirtualNodes virtualNodeCount) nodes
  in ConsistentHashRing virtualNodes virtualNodeCount
  where
    createVirtualNodes count (NodeId nodeIdText) = 
      [(hash (nodeIdText <> show i), NodeId nodeIdText) | i <- [0..count-1]]
    
    hash :: Text -> Word32
    hash = fromIntegral . Data.HashTable.hash . encodeUtf8

-- 查找键对应的节点
findNodes :: ConsistentHashRing -> Key -> [NodeId]
findNodes ring (Key keyText) = 
  let keyHash = hash keyText
      virtualNodes = virtualNodes ring
      (_, candidateNodes) = Map.split keyHash virtualNodes
      allCandidates = Map.elems candidateNodes ++ Map.elems virtualNodes
  in take (replicationFactor ring) $ nub allCandidates
  where
    hash = fromIntegral . Data.HashTable.hash . encodeUtf8

-- 分布式读写操作
class Monad m => DistributedStorage m where
  distributedRead :: ReplicationStrategy -> Key -> m (Either StorageError Value)
  distributedWrite :: ReplicationStrategy -> Key -> Value -> m (Either StorageError ())
  repairRead :: Key -> [Value] -> m Value

-- 读修复
performReadRepair :: (DistributedStorage m) => Key -> [Value] -> m Value
performReadRepair key values = do
  let uniqueValues = nub values
  case uniqueValues of
    [singleValue] -> return singleValue  -- 所有副本一致
    multipleValues -> do
      -- 选择最新的值（基于时间戳或版本）
      let latestValue = maximumBy compareVersions multipleValues
      -- 修复不一致的副本
      mapM_ (repairReplica key latestValue) (filter (/= latestValue) multipleValues)
      return latestValue
  where
    compareVersions v1 v2 = compare (getVersion v1) (getVersion v2)
    getVersion (Value _) = 0  -- 简化版本，实际需要版本信息
    repairReplica key correctValue wrongValue = 
      distributedWrite (SimpleReplication 1) key correctValue

-- Vector Clock版本控制
data VersionedValue = VersionedValue
  { versionedValue :: Value
  , vectorClock :: VectorClock
  , timestamp :: UTCTime
  } deriving (Show, Eq)

-- 冲突解决
resolveConflicts :: [VersionedValue] -> VersionedValue
resolveConflicts versions = 
  case findConcurrentVersions versions of
    [singleVersion] -> singleVersion
    conflictingVersions -> 
      -- 使用最后写入胜利策略
      maximumBy (comparing timestamp) conflictingVersions

findConcurrentVersions :: [VersionedValue] -> [VersionedValue]
findConcurrentVersions versions = 
  let dominantVersions = filter (\v -> not $ any (dominates v) versions) versions
  in if null dominantVersions then [maximumBy (comparing timestamp) versions] else dominantVersions
  where
    dominates v1 v2 = 
      happensBefore (vectorClock v2) (vectorClock v1) && v1 /= v2

-- 网络分区处理
data PartitionTolerance = PartitionTolerance
  { allowStaleReads :: Bool
  , writeAvailability :: WriteAvailabilityMode
  , conflictResolution :: ConflictResolutionStrategy
  } deriving (Show)

data WriteAvailabilityMode = 
  RequireMajority |
  AllowAnyReplica |
  RequireQuorum QuorumConfig
  deriving (Show)

data ConflictResolutionStrategy = 
  LastWriteWins |
  VectorClockMerge |
  ApplicationSpecific
  deriving (Show)
```

## 总结

分布式系统在函数式编程环境中的关键特性：

1. **不可变性**: 减少并发控制复杂性，简化复制和一致性
2. **纯函数**: 确保操作的可重复性和幂等性
3. **类型安全**: 编译时检查分布式协议的正确性
4. **组合性**: 分布式算法可以通过简单组件组合实现
5. **形式化验证**: 数学基础支持协议正确性证明

分布式系统的核心挑战：

- **一致性**: 保证数据在所有节点上的一致性
- **可用性**: 系统在部分故障时仍能提供服务
- **分区容错**: 网络分区时的系统行为
- **性能**: 分布式操作的延迟和吞吐量
- **故障恢复**: 节点故障后的快速恢复

通过函数式编程的理论优势，我们能够构建更可靠、更易推理的分布式系统。
