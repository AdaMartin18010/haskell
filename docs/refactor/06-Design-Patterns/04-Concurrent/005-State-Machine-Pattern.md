# 状态机模式 (State Machine Pattern)

## 概述

状态机模式是一种并发设计模式，用于管理复杂的状态转换逻辑，确保状态转换的原子性和一致性。

## 核心概念

### 状态机组件

- **状态 (State)**: 系统在某一时刻的配置
- **事件 (Event)**: 触发状态转换的输入
- **转换 (Transition)**: 从一个状态到另一个状态的映射
- **动作 (Action)**: 状态转换时执行的操作

### 并发特性

- **原子性**: 状态转换必须是原子的
- **一致性**: 状态转换必须保持系统一致性
- **隔离性**: 并发访问状态机时的隔离机制

## 实现模式

### 1. 锁保护状态机

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
enum State {
    Idle,
    Processing,
    Completed,
    Error,
}

#[derive(Debug, Clone)]
enum Event {
    Start,
    Process,
    Complete,
    Fail,
}

struct StateMachine {
    current_state: State,
    transitions: HashMap<(State, Event), State>,
    actions: HashMap<(State, Event), Box<dyn Fn() + Send + Sync>>,
}

impl StateMachine {
    fn new() -> Self {
        let mut transitions = HashMap::new();
        transitions.insert((State::Idle, Event::Start), State::Processing);
        transitions.insert((State::Processing, Event::Process), State::Processing);
        transitions.insert((State::Processing, Event::Complete), State::Completed);
        transitions.insert((State::Processing, Event::Fail), State::Error);
        
        Self {
            current_state: State::Idle,
            transitions,
            actions: HashMap::new(),
        }
    }
    
    fn transition(&mut self, event: Event) -> Result<State, String> {
        let key = (self.current_state.clone(), event);
        
        if let Some(&new_state) = self.transitions.get(&key) {
            // 执行状态转换动作
            if let Some(action) = self.actions.get(&key) {
                action();
            }
            
            self.current_state = new_state.clone();
            Ok(new_state)
        } else {
            Err("Invalid transition".to_string())
        }
    }
}

// 并发安全的状态机
struct ConcurrentStateMachine {
    state_machine: Arc<Mutex<StateMachine>>,
}

impl ConcurrentStateMachine {
    fn new() -> Self {
        Self {
            state_machine: Arc::new(Mutex::new(StateMachine::new())),
        }
    }
    
    fn transition(&self, event: Event) -> Result<State, String> {
        let mut sm = self.state_machine.lock().unwrap();
        sm.transition(event)
    }
}
```

### 2. 无锁状态机

```rust
use std::sync::atomic::{AtomicU32, Ordering};

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq)]
enum State {
    Idle = 0,
    Processing = 1,
    Completed = 2,
    Error = 3,
}

struct LockFreeStateMachine {
    current_state: AtomicU32,
}

impl LockFreeStateMachine {
    fn new() -> Self {
        Self {
            current_state: AtomicU32::new(State::Idle as u32),
        }
    }
    
    fn get_state(&self) -> State {
        match self.current_state.load(Ordering::Acquire) {
            0 => State::Idle,
            1 => State::Processing,
            2 => State::Completed,
            3 => State::Error,
            _ => State::Error,
        }
    }
    
    fn transition(&self, event: Event) -> Result<State, String> {
        let current = self.get_state();
        let new_state = match (current, event) {
            (State::Idle, Event::Start) => State::Processing,
            (State::Processing, Event::Process) => State::Processing,
            (State::Processing, Event::Complete) => State::Completed,
            (State::Processing, Event::Fail) => State::Error,
            _ => return Err("Invalid transition".to_string()),
        };
        
        // CAS操作确保原子性
        let expected = current as u32;
        let desired = new_state as u32;
        
        match self.current_state.compare_exchange(
            expected,
            desired,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => Ok(new_state),
            Err(_) => Err("Concurrent modification".to_string()),
        }
    }
}
```

### 3. 事件驱动状态机

```rust
use tokio::sync::mpsc;
use std::collections::HashMap;

struct EventDrivenStateMachine {
    state: State,
    transitions: HashMap<(State, Event), State>,
    event_sender: mpsc::Sender<Event>,
    event_receiver: mpsc::Receiver<Event>,
}

impl EventDrivenStateMachine {
    fn new() -> (Self, mpsc::Sender<Event>) {
        let (tx, rx) = mpsc::channel(100);
        let mut transitions = HashMap::new();
        transitions.insert((State::Idle, Event::Start), State::Processing);
        transitions.insert((State::Processing, Event::Process), State::Processing);
        transitions.insert((State::Processing, Event::Complete), State::Completed);
        transitions.insert((State::Processing, Event::Fail), State::Error);
        
        let sm = Self {
            state: State::Idle,
            transitions,
            event_sender: tx.clone(),
            event_receiver: rx,
        };
        
        (sm, tx)
    }
    
    async fn run(&mut self) {
        while let Some(event) = self.event_receiver.recv().await {
            if let Ok(new_state) = self.process_event(event) {
                println!("State transition: {:?} -> {:?}", self.state, new_state);
                self.state = new_state;
            }
        }
    }
    
    fn process_event(&self, event: Event) -> Result<State, String> {
        let key = (self.state, event);
        self.transitions.get(&key).cloned()
            .ok_or_else(|| "Invalid transition".to_string())
    }
}
```

## Haskell实现

```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Data.Map (Map)
import qualified Data.Map as Map

-- 状态定义
data State = Idle | Processing | Completed | Error
    deriving (Eq, Show, Ord)

-- 事件定义
data Event = Start | Process | Complete | Fail
    deriving (Eq, Show, Ord)

-- 状态机定义
data StateMachine = StateMachine
    { currentState :: TVar State
    , transitions :: Map (State, Event) State
    , actions :: Map (State, Event) (IO ())
    }

-- 创建状态机
createStateMachine :: IO StateMachine
createStateMachine = do
    currentState <- newTVarIO Idle
    let transitions = Map.fromList
            [ ((Idle, Start), Processing)
            , ((Processing, Process), Processing)
            , ((Processing, Complete), Completed)
            , ((Processing, Fail), Error)
            ]
        actions = Map.empty
    return StateMachine { currentState, transitions, actions }

-- 状态转换
transition :: StateMachine -> Event -> STM (Maybe State)
transition sm event = do
    current <- readTVar (currentState sm)
    let newState = Map.lookup (current, event) (transitions sm)
    case newState of
        Just state -> do
            writeTVar (currentState sm) state
            return (Just state)
        Nothing -> return Nothing

-- 并发状态机
concurrentTransition :: StateMachine -> Event -> IO (Maybe State)
concurrentTransition sm event = atomically $ transition sm event

-- 事件驱动状态机
data EventDrivenStateMachine = EventDrivenStateMachine
    { state :: TVar State
    , eventChan :: TChan Event
    }

createEventDrivenStateMachine :: IO EventDrivenStateMachine
createEventDrivenStateMachine = do
    state <- newTVarIO Idle
    eventChan <- newTChanIO
    return EventDrivenStateMachine { state, eventChan }

runEventDrivenStateMachine :: EventDrivenStateMachine -> IO ()
runEventDrivenStateMachine sm = do
    atomically $ do
        event <- readTChan (eventChan sm)
        current <- readTVar (state sm)
        let newState = case (current, event) of
                (Idle, Start) -> Just Processing
                (Processing, Process) -> Just Processing
                (Processing, Complete) -> Just Completed
                (Processing, Fail) -> Just Error
                _ -> Nothing
        case newState of
            Just state -> writeTVar (state sm) state
            Nothing -> return ()
    runEventDrivenStateMachine sm
```

## Lean实现

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- 状态定义
inductive State where
  | idle : State
  | processing : State
  | completed : State
  | error : State

-- 事件定义
inductive Event where
  | start : Event
  | process : Event
  | complete : Event
  | fail : Event

-- 状态机结构
structure StateMachine where
  currentState : State
  transitions : HashMap (State × Event) State
  actions : HashMap (State × Event) (IO Unit)

-- 创建状态机
def createStateMachine : IO StateMachine := do
  let transitions := HashMap.empty
    |>.insert (State.idle, Event.start) State.processing
    |>.insert (State.processing, Event.process) State.processing
    |>.insert (State.processing, Event.complete) State.completed
    |>.insert (State.processing, Event.fail) State.error
  
  let actions := HashMap.empty
  
  return {
    currentState := State.idle,
    transitions := transitions,
    actions := actions
  }

-- 状态转换
def transition (sm : StateMachine) (event : Event) : IO (Option State) := do
  let key := (sm.currentState, event)
  match sm.transitions.find? key with
  | some newState => 
    -- 执行动作
    match sm.actions.find? key with
    | some action => action
    | none => return ()
    return some newState
  | none => return none

-- 并发状态机
structure ConcurrentStateMachine where
  stateMachine : IO StateMachine
  mutex : IO.Mutex

def createConcurrentStateMachine : IO ConcurrentStateMachine := do
  let sm ← createStateMachine
  let mutex ← IO.Mutex.new
  return { stateMachine := sm, mutex := mutex }

def concurrentTransition (csm : ConcurrentStateMachine) (event : Event) : IO (Option State) := do
  csm.mutex.withLock fun _ => do
    let sm ← csm.stateMachine
    transition sm event
```

## 应用场景

### 1. 工作流引擎

- 业务流程状态管理
- 任务生命周期控制
- 审批流程状态跟踪

### 2. 游戏状态管理

- 游戏角色状态
- 关卡进度状态
- 多人游戏同步

### 3. 网络协议实现

- TCP连接状态
- HTTP请求状态
- WebSocket连接状态

### 4. 数据库事务

- 事务状态管理
- 分布式事务协调
- 回滚机制实现

## 最佳实践

### 1. 状态设计原则

- 状态应该是互斥的
- 状态转换应该是确定的
- 避免状态爆炸

### 2. 并发安全

- 使用适当的同步机制
- 避免死锁和活锁
- 考虑性能影响

### 3. 错误处理

- 定义错误状态
- 实现恢复机制
- 记录状态转换日志

### 4. 测试策略

- 状态转换测试
- 并发测试
- 边界条件测试

## 性能考虑

### 1. 内存使用

- 状态机大小
- 转换表存储
- 动作函数存储

### 2. 并发性能

- 锁竞争
- 原子操作开销
- 内存屏障

### 3. 扩展性

- 状态数量增长
- 事件类型增加
- 分布式部署

## 总结

状态机模式是并发系统中管理复杂状态转换的重要模式。通过合理的设计和实现，可以确保状态转换的原子性、一致性和隔离性，同时保持良好的性能和可维护性。
