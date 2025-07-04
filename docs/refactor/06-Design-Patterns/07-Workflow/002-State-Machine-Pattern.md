# 工作流状态机模式 (Workflow State Machine Pattern)

## 概述

工作流状态机模式用于建模和管理复杂业务流程的状态转换，支持条件分支、并行执行、异常处理等高级工作流特性。

## 核心思想

- 状态定义：明确工作流的各个阶段状态
- 事件驱动：通过事件触发状态转换
- 条件分支：根据业务规则选择不同路径
- 并行执行：支持多个活动同时进行

## 状态机组件

- **状态 (State)**: 工作流的当前阶段
- **事件 (Event)**: 触发状态转换的业务事件
- **转换 (Transition)**: 状态间的转换规则
- **动作 (Action)**: 状态转换时执行的业务逻辑
- **守卫 (Guard)**: 转换条件判断

## Rust实现示例

```rust
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
enum WorkflowState {
    Created,
    Submitted,
    UnderReview,
    Approved,
    Rejected,
    Completed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum WorkflowEvent {
    Submit,
    Review,
    Approve,
    Reject,
    Complete,
}

struct WorkflowStateMachine {
    current_state: WorkflowState,
    transitions: HashMap<(WorkflowState, WorkflowEvent), WorkflowState>,
    guards: HashMap<(WorkflowState, WorkflowEvent), Box<dyn Fn(&WorkflowContext) -> bool + Send + Sync>>,
    actions: HashMap<(WorkflowState, WorkflowEvent), Box<dyn Fn(&mut WorkflowContext) + Send + Sync>>,
}

#[derive(Debug, Clone)]
struct WorkflowContext {
    user_id: String,
    data: HashMap<String, String>,
    metadata: HashMap<String, String>,
}

impl WorkflowStateMachine {
    fn new() -> Self {
        let mut transitions = HashMap::new();
        transitions.insert((WorkflowState::Created, WorkflowEvent::Submit), WorkflowState::Submitted);
        transitions.insert((WorkflowState::Submitted, WorkflowEvent::Review), WorkflowState::UnderReview);
        transitions.insert((WorkflowState::UnderReview, WorkflowEvent::Approve), WorkflowState::Approved);
        transitions.insert((WorkflowState::UnderReview, WorkflowEvent::Reject), WorkflowState::Rejected);
        transitions.insert((WorkflowState::Approved, WorkflowEvent::Complete), WorkflowState::Completed);
        
        Self {
            current_state: WorkflowState::Created,
            transitions,
            guards: HashMap::new(),
            actions: HashMap::new(),
        }
    }
    
    fn transition(&mut self, event: WorkflowEvent, context: &mut WorkflowContext) -> Result<WorkflowState, String> {
        let key = (self.current_state.clone(), event.clone());
        
        // 检查守卫条件
        if let Some(guard) = self.guards.get(&key) {
            if !guard(context) {
                return Err("Guard condition not met".to_string());
            }
        }
        
        // 执行转换
        if let Some(&new_state) = self.transitions.get(&key) {
            // 执行动作
            if let Some(action) = self.actions.get(&key) {
                action(context);
            }
            
            self.current_state = new_state.clone();
            Ok(new_state)
        } else {
            Err("Invalid transition".to_string())
        }
    }
    
    fn add_guard(&mut self, from: WorkflowState, event: WorkflowEvent, guard: Box<dyn Fn(&WorkflowContext) -> bool + Send + Sync>) {
        self.guards.insert((from, event), guard);
    }
    
    fn add_action(&mut self, from: WorkflowState, event: WorkflowEvent, action: Box<dyn Fn(&mut WorkflowContext) + Send + Sync>) {
        self.actions.insert((from, event), action);
    }
}
```

## Haskell实现示例

```haskell
import Control.Concurrent.STM
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)

-- 状态定义
data WorkflowState = Created | Submitted | UnderReview | Approved | Rejected | Completed
    deriving (Eq, Show, Ord)

-- 事件定义
data WorkflowEvent = Submit | Review | Approve | Reject | Complete
    deriving (Eq, Show, Ord)

-- 上下文定义
data WorkflowContext = WorkflowContext
    { userId :: Text
    , data :: Map Text Text
    , metadata :: Map Text Text
    }

-- 守卫函数类型
type Guard = WorkflowContext -> Bool

-- 动作函数类型
type Action = WorkflowContext -> IO WorkflowContext

-- 状态机定义
data WorkflowStateMachine = WorkflowStateMachine
    { currentState :: TVar WorkflowState
    , transitions :: Map (WorkflowState, WorkflowEvent) WorkflowState
    , guards :: Map (WorkflowState, WorkflowEvent) Guard
    , actions :: Map (WorkflowState, WorkflowEvent) Action
    }

-- 创建状态机
createWorkflowStateMachine :: IO WorkflowStateMachine
createWorkflowStateMachine = do
    currentState <- newTVarIO Created
    let transitions = Map.fromList
            [ ((Created, Submit), Submitted)
            , ((Submitted, Review), UnderReview)
            , ((UnderReview, Approve), Approved)
            , ((UnderReview, Reject), Rejected)
            , ((Approved, Complete), Completed)
            ]
        guards = Map.empty
        actions = Map.empty
    return WorkflowStateMachine { currentState, transitions, guards, actions }

-- 状态转换
transition :: WorkflowStateMachine -> WorkflowEvent -> WorkflowContext -> IO (Either String WorkflowState)
transition sm event context = atomically $ do
    current <- readTVar (currentState sm)
    let key = (current, event)
    
    -- 检查守卫条件
    case Map.lookup key (guards sm) of
        Just guard -> do
            if guard context
                then return ()
                else return (Left "Guard condition not met")
        Nothing -> return ()
    
    -- 执行转换
    case Map.lookup key (transitions sm) of
        Just newState -> do
            writeTVar (currentState sm) newState
            return (Right newState)
        Nothing -> return (Left "Invalid transition")

-- 添加守卫
addGuard :: WorkflowStateMachine -> WorkflowState -> WorkflowEvent -> Guard -> IO ()
addGuard sm from event guard = do
    let newGuards = Map.insert (from, event) guard (guards sm)
    -- 更新状态机的守卫映射
    return ()

-- 添加动作
addAction :: WorkflowStateMachine -> WorkflowState -> WorkflowEvent -> Action -> IO ()
addAction sm from event action = do
    let newActions = Map.insert (from, event) action (actions sm)
    -- 更新状态机的动作映射
    return ()
```

## Lean实现思路

```lean
import Lean.Data.HashMap

-- 状态定义
inductive WorkflowState where
  | created : WorkflowState
  | submitted : WorkflowState
  | underReview : WorkflowState
  | approved : WorkflowState
  | rejected : WorkflowState
  | completed : WorkflowState

-- 事件定义
inductive WorkflowEvent where
  | submit : WorkflowEvent
  | review : WorkflowEvent
  | approve : WorkflowEvent
  | reject : WorkflowEvent
  | complete : WorkflowEvent

-- 上下文定义
structure WorkflowContext where
  userId : String
  data : HashMap String String
  metadata : HashMap String String

-- 守卫函数类型
def Guard := WorkflowContext → Bool

-- 动作函数类型
def Action := WorkflowContext → IO WorkflowContext

-- 状态机定义
structure WorkflowStateMachine where
  currentState : WorkflowState
  transitions : HashMap (WorkflowState × WorkflowEvent) WorkflowState
  guards : HashMap (WorkflowState × WorkflowEvent) Guard
  actions : HashMap (WorkflowState × WorkflowEvent) Action

-- 创建状态机
def createWorkflowStateMachine : WorkflowStateMachine :=
  let transitions := HashMap.empty
    |>.insert (WorkflowState.created, WorkflowEvent.submit) WorkflowState.submitted
    |>.insert (WorkflowState.submitted, WorkflowEvent.review) WorkflowState.underReview
    |>.insert (WorkflowState.underReview, WorkflowEvent.approve) WorkflowState.approved
    |>.insert (WorkflowState.underReview, WorkflowEvent.reject) WorkflowState.rejected
    |>.insert (WorkflowState.approved, WorkflowEvent.complete) WorkflowState.completed
  
  { currentState := WorkflowState.created
    transitions := transitions
    guards := HashMap.empty
    actions := HashMap.empty
  }

-- 状态转换
def transition (sm : WorkflowStateMachine) (event : WorkflowEvent) (context : WorkflowContext) : IO (Option WorkflowState) := do
  let key := (sm.currentState, event)
  
  -- 检查守卫条件
  match sm.guards.find? key with
  | some guard => 
    if guard context then return () else return none
  | none => return ()
  
  -- 执行转换
  match sm.transitions.find? key with
  | some newState => 
    -- 执行动作
    match sm.actions.find? key with
    | some action => action context
    | none => return ()
    return some newState
  | none => return none
```

## 应用场景

### 1. 业务流程管理

- 审批流程（请假申请、采购审批）
- 订单处理流程
- 客户服务流程

### 2. 软件开发流程

- CI/CD流水线
- 代码审查流程
- 发布管理流程

### 3. 合规与监管

- 合规检查流程
- 审计跟踪
- 风险控制流程

### 4. 游戏与娱乐

- 游戏关卡流程
- 用户注册流程
- 支付处理流程

## 最佳实践

### 1. 状态设计

- 状态应该清晰明确，避免模糊
- 状态转换应该是确定的
- 考虑异常状态和错误处理

### 2. 事件设计

- 事件应该反映业务含义
- 事件应该是原子的
- 考虑事件的幂等性

### 3. 守卫条件

- 守卫条件应该简单明确
- 避免复杂的业务逻辑
- 考虑性能影响

### 4. 动作设计

- 动作应该是幂等的
- 考虑事务性
- 记录操作日志

### 5. 持久化

- 状态机状态需要持久化
- 考虑分布式部署
- 支持状态恢复

## 性能考虑

### 1. 内存使用

- 状态机大小
- 转换表存储
- 上下文数据大小

### 2. 并发性能

- 状态机访问模式
- 锁竞争
- 事件处理性能

### 3. 扩展性

- 状态数量增长
- 事件类型增加
- 分布式部署

## 总结

工作流状态机模式是复杂业务流程建模和管理的重要工具。通过合理的设计和实现，可以构建灵活、可靠、高性能的工作流系统，支持复杂的业务场景和需求。
