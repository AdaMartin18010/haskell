# 分布式共识模式（Consensus Pattern）

## 概述

分布式共识模式是一种分布式系统设计模式，确保在多个节点之间达成一致的状态或决策，即使在网络分区和节点故障的情况下也能保持一致性。

## 理论基础

- **一致性**：所有节点最终达成相同状态
- **可用性**：系统在部分节点故障时仍可提供服务
- **分区容错性**：在网络分区时保持一致性

## Rust实现示例

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};
use tokio::sync::mpsc;

// 节点状态
#[derive(Debug, Clone, PartialEq)]
enum NodeState {
    Follower,
    Candidate,
    Leader,
}

// 日志条目
#[derive(Debug, Clone)]
struct LogEntry {
    term: u64,
    index: u64,
    command: String,
}

// Raft节点
struct RaftNode {
    id: u32,
    state: Arc<Mutex<NodeState>>,
    current_term: Arc<Mutex<u64>>,
    voted_for: Arc<Mutex<Option<u32>>>,
    log: Arc<Mutex<Vec<LogEntry>>>,
    commit_index: Arc<Mutex<u64>>,
    last_applied: Arc<Mutex<u64>>,
    next_index: Arc<Mutex<HashMap<u32, u64>>>,
    match_index: Arc<Mutex<HashMap<u32, u64>>>,
    election_timeout: Duration,
    heartbeat_interval: Duration,
}

impl RaftNode {
    fn new(id: u32) -> Self {
        Self {
            id,
            state: Arc::new(Mutex::new(NodeState::Follower)),
            current_term: Arc::new(Mutex::new(0)),
            voted_for: Arc::new(Mutex::new(None)),
            log: Arc::new(Mutex::new(Vec::new())),
            commit_index: Arc::new(Mutex::new(0)),
            last_applied: Arc::new(Mutex::new(0)),
            next_index: Arc::new(Mutex::new(HashMap::new())),
            match_index: Arc::new(Mutex::new(HashMap::new())),
            election_timeout: Duration::from_millis(150 + (id as u64) * 100),
            heartbeat_interval: Duration::from_millis(50),
        }
    }
    
    async fn start(&self, peers: Vec<u32>) {
        let node_id = self.id;
        let state = Arc::clone(&self.state);
        let current_term = Arc::clone(&self.current_term);
        let voted_for = Arc::clone(&self.voted_for);
        let log = Arc::clone(&self.log);
        let commit_index = Arc::clone(&self.commit_index);
        let last_applied = Arc::clone(&self.last_applied);
        let next_index = Arc::clone(&self.next_index);
        let match_index = Arc::clone(&self.match_index);
        let election_timeout = self.election_timeout;
        let heartbeat_interval = self.heartbeat_interval;
        
        tokio::spawn(async move {
            loop {
                let current_state = { *state.lock().unwrap() };
                
                match current_state {
                    NodeState::Follower => {
                        Self::run_follower(
                            node_id,
                            &state,
                            &current_term,
                            &voted_for,
                            &log,
                            &commit_index,
                            &last_applied,
                            election_timeout,
                        ).await;
                    }
                    NodeState::Candidate => {
                        Self::run_candidate(
                            node_id,
                            &state,
                            &current_term,
                            &voted_for,
                            &log,
                            &commit_index,
                            &last_applied,
                            &peers,
                            election_timeout,
                        ).await;
                    }
                    NodeState::Leader => {
                        Self::run_leader(
                            node_id,
                            &state,
                            &current_term,
                            &voted_for,
                            &log,
                            &commit_index,
                            &last_applied,
                            &next_index,
                            &match_index,
                            &peers,
                            heartbeat_interval,
                        ).await;
                    }
                }
            }
        });
    }
    
    async fn run_follower(
        node_id: u32,
        state: &Arc<Mutex<NodeState>>,
        current_term: &Arc<Mutex<u64>>,
        voted_for: &Arc<Mutex<Option<u32>>>,
        log: &Arc<Mutex<Vec<LogEntry>>>,
        commit_index: &Arc<Mutex<u64>>,
        last_applied: &Arc<Mutex<u64>>,
        election_timeout: Duration,
    ) {
        println!("节点 {} 作为Follower运行", node_id);
        
        // 等待选举超时或收到心跳
        tokio::time::sleep(election_timeout).await;
        
        // 转换为候选人
        {
            let mut state_guard = state.lock().unwrap();
            *state_guard = NodeState::Candidate;
        }
        
        {
            let mut term_guard = current_term.lock().unwrap();
            *term_guard += 1;
        }
        
        {
            let mut voted_guard = voted_for.lock().unwrap();
            *voted_guard = Some(node_id);
        }
    }
    
    async fn run_candidate(
        node_id: u32,
        state: &Arc<Mutex<NodeState>>,
        current_term: &Arc<Mutex<u64>>,
        voted_for: &Arc<Mutex<Option<u32>>>,
        log: &Arc<Mutex<Vec<LogEntry>>>,
        commit_index: &Arc<Mutex<u64>>,
        last_applied: &Arc<Mutex<u64>>,
        peers: &Vec<u32>,
        election_timeout: Duration,
    ) {
        println!("节点 {} 作为Candidate运行", node_id);
        
        // 发起选举
        let votes_received = Arc::new(Mutex::new(1)); // 自己的一票
        
        // 向其他节点请求投票
        for &peer_id in peers {
            if peer_id != node_id {
                let votes_clone = Arc::clone(&votes_received);
                tokio::spawn(async move {
                    // 模拟投票请求
                    tokio::time::sleep(Duration::from_millis(50)).await;
                    
                    if let Ok(mut votes) = votes_clone.lock() {
                        *votes += 1;
                    }
                });
            }
        }
        
        // 等待选举结果
        tokio::time::sleep(election_timeout).await;
        
        let votes = { *votes_received.lock().unwrap() };
        let majority = (peers.len() + 1) / 2 + 1;
        
        if votes >= majority {
            println!("节点 {} 成为Leader", node_id);
            {
                let mut state_guard = state.lock().unwrap();
                *state_guard = NodeState::Leader;
            }
        } else {
            println!("节点 {} 选举失败，回到Follower", node_id);
            {
                let mut state_guard = state.lock().unwrap();
                *state_guard = NodeState::Follower;
            }
        }
    }
    
    async fn run_leader(
        node_id: u32,
        state: &Arc<Mutex<NodeState>>,
        current_term: &Arc<Mutex<u64>>,
        voted_for: &Arc<Mutex<Option<u32>>>,
        log: &Arc<Mutex<Vec<LogEntry>>>,
        commit_index: &Arc<Mutex<u64>>,
        last_applied: &Arc<Mutex<u64>>,
        next_index: &Arc<Mutex<HashMap<u32, u64>>>,
        match_index: &Arc<Mutex<HashMap<u32, u64>>>,
        peers: &Vec<u32>,
        heartbeat_interval: Duration,
    ) {
        println!("节点 {} 作为Leader运行", node_id);
        
        // 发送心跳
        for &peer_id in peers {
            if peer_id != node_id {
                tokio::spawn(async move {
                    // 模拟心跳发送
                    println!("向节点 {} 发送心跳", peer_id);
                });
            }
        }
        
        // 等待下一个心跳间隔
        tokio::time::sleep(heartbeat_interval).await;
    }
    
    async fn propose_command(&self, command: String) -> Result<u64, String> {
        let current_state = { *self.state.lock().unwrap() };
        
        if current_state != NodeState::Leader {
            return Err("只有Leader可以提议命令".to_string());
        }
        
        let term = { *self.current_term.lock().unwrap() };
        let log_index = { self.log.lock().unwrap().len() as u64 };
        
        let entry = LogEntry {
            term,
            index: log_index,
            command,
        };
        
        {
            let mut log_guard = self.log.lock().unwrap();
            log_guard.push(entry);
        }
        
        Ok(log_index)
    }
}

// Paxos共识算法
struct PaxosNode {
    id: u32,
    proposer_id: u32,
    accepted_value: Arc<Mutex<Option<String>>>,
    accepted_proposal: Arc<Mutex<Option<u64>>>,
    highest_proposal: Arc<Mutex<u64>>,
}

impl PaxosNode {
    fn new(id: u32) -> Self {
        Self {
            id,
            proposer_id: id,
            accepted_value: Arc::new(Mutex::new(None)),
            accepted_proposal: Arc::new(Mutex::new(None)),
            highest_proposal: Arc::new(Mutex::new(0)),
        }
    }
    
    async fn propose(&self, value: String, peers: Vec<u32>) -> Result<String, String> {
        let proposal_number = {
            let mut highest = self.highest_proposal.lock().unwrap();
            *highest += 1;
            *highest
        };
        
        // Phase 1: Prepare
        let prepare_responses = self.send_prepare(proposal_number, &peers).await;
        let majority = (peers.len() + 1) / 2 + 1;
        
        if prepare_responses.len() < majority {
            return Err("Prepare阶段未获得多数票".to_string());
        }
        
        // Phase 2: Accept
        let accept_responses = self.send_accept(proposal_number, value.clone(), &peers).await;
        
        if accept_responses.len() >= majority {
            Ok(value)
        } else {
            Err("Accept阶段未获得多数票".to_string())
        }
    }
    
    async fn send_prepare(&self, proposal_number: u64, peers: &Vec<u32>) -> Vec<bool> {
        let mut responses = Vec::new();
        
        for &peer_id in peers {
            if peer_id != self.id {
                // 模拟网络请求
                tokio::time::sleep(Duration::from_millis(10)).await;
                responses.push(true); // 简化实现
            }
        }
        
        responses
    }
    
    async fn send_accept(&self, proposal_number: u64, value: String, peers: &Vec<u32>) -> Vec<bool> {
        let mut responses = Vec::new();
        
        for &peer_id in peers {
            if peer_id != self.id {
                // 模拟网络请求
                tokio::time::sleep(Duration::from_millis(10)).await;
                responses.push(true); // 简化实现
            }
        }
        
        responses
    }
}

#[tokio::main]
async fn main() {
    // Raft共识示例
    println!("=== Raft共识示例 ===");
    let node1 = RaftNode::new(1);
    let node2 = RaftNode::new(2);
    let node3 = RaftNode::new(3);
    
    let peers = vec![1, 2, 3];
    
    let handle1 = tokio::spawn(async move {
        node1.start(peers.clone()).await;
    });
    
    let handle2 = tokio::spawn(async move {
        node2.start(peers.clone()).await;
    });
    
    let handle3 = tokio::spawn(async move {
        node3.start(peers).await;
    });
    
    // 等待一段时间让选举进行
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // Paxos共识示例
    println!("\n=== Paxos共识示例 ===");
    let paxos_node = PaxosNode::new(1);
    let paxos_peers = vec![1, 2, 3];
    
    match paxos_node.propose("共识值".to_string(), paxos_peers).await {
        Ok(value) => println!("达成共识: {}", value),
        Err(error) => println!("共识失败: {}", error),
    }
    
    // 清理
    handle1.abort();
    handle2.abort();
    handle3.abort();
}
```

## Haskell实现示例

```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.IORef
import Data.Map as M

-- 节点状态
data NodeState = Follower | Candidate | Leader deriving (Eq, Show)

-- 日志条目
data LogEntry = LogEntry
    { term :: Int
    , index :: Int
    , command :: String
    } deriving (Show)

-- Raft节点
data RaftNode = RaftNode
    { nodeId :: Int
    , state :: IORef NodeState
    , currentTerm :: IORef Int
    , votedFor :: IORef (Maybe Int)
    , log :: IORef [LogEntry]
    , commitIndex :: IORef Int
    , lastApplied :: IORef Int
    , nextIndex :: IORef (M.Map Int Int)
    , matchIndex :: IORef (M.Map Int Int)
    }

newRaftNode :: Int -> IO RaftNode
newRaftNode id = do
    state <- newIORef Follower
    currentTerm <- newIORef 0
    votedFor <- newIORef Nothing
    log <- newIORef []
    commitIndex <- newIORef 0
    lastApplied <- newIORef 0
    nextIndex <- newIORef M.empty
    matchIndex <- newIORef M.empty
    return $ RaftNode id state currentTerm votedFor log commitIndex lastApplied nextIndex matchIndex

runFollower :: RaftNode -> [Int] -> IO ()
runFollower node peers = do
    putStrLn $ "节点 " ++ show (nodeId node) ++ " 作为Follower运行"
    threadDelay 1000000 -- 1秒
    writeIORef (state node) Candidate
    modifyIORef (currentTerm node) (+1)
    writeIORef (votedFor node) (Just (nodeId node))

runCandidate :: RaftNode -> [Int] -> IO ()
runCandidate node peers = do
    putStrLn $ "节点 " ++ show (nodeId node) ++ " 作为Candidate运行"
    
    -- 发起选举
    votesReceived <- newIORef 1 -- 自己的一票
    
    -- 向其他节点请求投票
    mapM_ (\peerId -> 
        if peerId /= nodeId node
            then forkIO $ do
                threadDelay 50000 -- 50ms
                modifyIORef votesReceived (+1)
            else return ()
        ) peers
    
    threadDelay 1000000 -- 等待选举结果
    
    votes <- readIORef votesReceived
    let majority = (length peers + 1) `div` 2 + 1
    
    if votes >= majority
        then do
            putStrLn $ "节点 " ++ show (nodeId node) ++ " 成为Leader"
            writeIORef (state node) Leader
        else do
            putStrLn $ "节点 " ++ show (nodeId node) ++ " 选举失败，回到Follower"
            writeIORef (state node) Follower

runLeader :: RaftNode -> [Int] -> IO ()
runLeader node peers = do
    putStrLn $ "节点 " ++ show (nodeId node) ++ " 作为Leader运行"
    
    -- 发送心跳
    mapM_ (\peerId -> 
        if peerId /= nodeId node
            then putStrLn $ "向节点 " ++ show peerId ++ " 发送心跳"
            else return ()
        ) peers
    
    threadDelay 50000 -- 50ms

startRaftNode :: RaftNode -> [Int] -> IO ()
startRaftNode node peers = do
    let loop = do
        currentState <- readIORef (state node)
        case currentState of
            Follower -> runFollower node peers >> loop
            Candidate -> runCandidate node peers >> loop
            Leader -> runLeader node peers >> loop
    
    loop

proposeCommand :: RaftNode -> String -> IO (Either String Int)
proposeCommand node command = do
    currentState <- readIORef (state node)
    if currentState /= Leader
        then return $ Left "只有Leader可以提议命令"
        else do
            term <- readIORef (currentTerm node)
            logEntries <- readIORef (log node)
            let logIndex = length logEntries
            
            let entry = LogEntry term logIndex command
            modifyIORef (log node) (++ [entry])
            
            return $ Right logIndex

-- Paxos节点
data PaxosNode = PaxosNode
    { paxosId :: Int
    , proposerId :: Int
    , acceptedValue :: IORef (Maybe String)
    , acceptedProposal :: IORef (Maybe Int)
    , highestProposal :: IORef Int
    }

newPaxosNode :: Int -> IO PaxosNode
newPaxosNode id = do
    acceptedValue <- newIORef Nothing
    acceptedProposal <- newIORef Nothing
    highestProposal <- newIORef 0
    return $ PaxosNode id id acceptedValue acceptedProposal highestProposal

propose :: PaxosNode -> String -> [Int] -> IO (Either String String)
propose node value peers = do
    proposalNumber <- do
        modifyIORef (highestProposal node) (+1)
        readIORef (highestProposal node)
    
    -- Phase 1: Prepare
    prepareResponses <- sendPrepare node proposalNumber peers
    let majority = (length peers + 1) `div` 2 + 1
    
    if length prepareResponses < majority
        then return $ Left "Prepare阶段未获得多数票"
        else do
            -- Phase 2: Accept
            acceptResponses <- sendAccept node proposalNumber value peers
            
            if length acceptResponses >= majority
                then return $ Right value
                else return $ Left "Accept阶段未获得多数票"

sendPrepare :: PaxosNode -> Int -> [Int] -> IO [Bool]
sendPrepare node proposalNumber peers = do
    responses <- mapM (\peerId -> 
        if peerId /= paxosId node
            then do
                threadDelay 10000 -- 10ms
                return True -- 简化实现
            else return True
        ) peers
    return responses

sendAccept :: PaxosNode -> Int -> String -> [Int] -> IO [Bool]
sendAccept node proposalNumber value peers = do
    responses <- mapM (\peerId -> 
        if peerId /= paxosId node
            then do
                threadDelay 10000 -- 10ms
                return True -- 简化实现
            else return True
        ) peers
    return responses

-- 测试函数
testRaftConsensus :: IO ()
testRaftConsensus = do
    putStrLn "=== Raft共识示例 ==="
    
    node1 <- newRaftNode 1
    node2 <- newRaftNode 2
    node3 <- newRaftNode 3
    
    let peers = [1, 2, 3]
    
    forkIO $ startRaftNode node1 peers
    forkIO $ startRaftNode node2 peers
    forkIO $ startRaftNode node3 peers
    
    threadDelay 2000000 -- 2秒
    
    -- 尝试提议命令
    result <- proposeCommand node1 "测试命令"
    case result of
        Right index -> putStrLn $ "命令提议成功，索引: " ++ show index
        Left error -> putStrLn $ "命令提议失败: " ++ error

testPaxosConsensus :: IO ()
testPaxosConsensus = do
    putStrLn "\n=== Paxos共识示例 ==="
    
    paxosNode <- newPaxosNode 1
    let peers = [1, 2, 3]
    
    result <- propose paxosNode "共识值" peers
    case result of
        Right value -> putStrLn $ "达成共识: " ++ value
        Left error -> putStrLn $ "共识失败: " ++ error

main :: IO ()
main = do
    testRaftConsensus
    testPaxosConsensus
```

## Lean实现思路

```lean
-- 节点状态
inductive NodeState where
  | Follower
  | Candidate
  | Leader

-- 日志条目
structure LogEntry where
  term : Nat
  index : Nat
  command : String

-- Raft节点
structure RaftNode where
  nodeId : Nat
  state : NodeState
  currentTerm : Nat
  votedFor : Option Nat
  log : List LogEntry
  commitIndex : Nat
  lastApplied : Nat

def newRaftNode (id : Nat) : RaftNode :=
  { nodeId := id
  , state := NodeState.Follower
  , currentTerm := 0
  , votedFor := none
  , log := []
  , commitIndex := 0
  , lastApplied := 0
  }

def runFollower (node : RaftNode) (peers : List Nat) : RaftNode :=
  { node with 
    state := NodeState.Candidate
  , currentTerm := node.currentTerm + 1
  , votedFor := some node.nodeId
  }

def runCandidate (node : RaftNode) (peers : List Nat) : RaftNode :=
  let votesReceived := 1 -- 自己的一票
  let majority := (peers.length + 1) `div` 2 + 1
  
  if votesReceived ≥ majority
    then { node with state := NodeState.Leader }
    else { node with state := NodeState.Follower }

def runLeader (node : RaftNode) (peers : List Nat) : RaftNode :=
  node -- 简化实现

-- Paxos节点
structure PaxosNode where
  paxosId : Nat
  proposerId : Nat
  acceptedValue : Option String
  acceptedProposal : Option Nat
  highestProposal : Nat

def newPaxosNode (id : Nat) : PaxosNode :=
  { paxosId := id
  , proposerId := id
  , acceptedValue := none
  , acceptedProposal := none
  , highestProposal := 0
  }

def propose (node : PaxosNode) (value : String) (peers : List Nat) : Sum String String :=
  let proposalNumber := node.highestProposal + 1
  let majority := (peers.length + 1) `div` 2 + 1
  
  -- 简化的实现
  if proposalNumber > 0
    then Sum.inr value
    else Sum.inl "共识失败"
```

## 应用场景

- 分布式数据库
- 区块链系统
- 分布式锁服务
- 配置管理

## 最佳实践

- 合理设置超时时间
- 实现日志压缩
- 优化网络通信
- 监控节点状态
