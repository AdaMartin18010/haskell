# 008 状态模式 (State Pattern)

## 1. 理论基础

### 1.1 模式定义

状态模式是一种行为型设计模式，允许对象在内部状态改变时改变其行为，对象看起来好像修改了其类。

### 1.2 核心概念

- **State（状态）**: 定义一个接口以封装与Context的一个特定状态相关的行为
- **ConcreteState（具体状态）**: 实现State接口，每个子类实现一个与Context的一个状态相关的行为
- **Context（上下文）**: 定义客户感兴趣的接口，维护一个ConcreteState子类的实例

### 1.3 设计原则

- **开闭原则**: 可以添加新的状态而不修改现有代码
- **单一职责**: 每个状态只负责一个状态的行为
- **依赖倒置**: 上下文依赖于抽象状态接口

### 1.4 优缺点分析

**优点:**

- 状态转换逻辑与状态对象合为一体，减少条件语句
- 状态对象可以被共享
- 状态转换更加明确
- 符合开闭原则

**缺点:**

- 状态类会增多
- 状态转换逻辑可能分散在多个状态类中
- 可能导致状态对象变得复杂

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class State a where
  handle :: a -> Context -> (String, Context)
  getStateName :: a -> String
  canTransitionTo :: a -> String -> Bool

-- 上下文接口
class Context a where
  setState :: a -> State -> a
  getCurrentState :: a -> String
  getStateHistory :: a -> [String]
```

### 2.2 扩展接口

```haskell
-- 支持状态历史的接口
class (State a) => StateWithHistory a where
  getHistory :: a -> [String]
  addToHistory :: a -> String -> a
  
-- 支持状态验证的接口
class (State a) => ValidatedState a where
  validateTransition :: a -> String -> Bool
  getValidTransitions :: a -> [String]
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 状态接口
class State a where
  handle :: a -> Context -> (String, Context)
  getStateName :: a -> String
  canTransitionTo :: a -> String -> Bool

-- 上下文
data Context = Context {
  currentState :: State,
  stateHistory :: [String],
  data :: String
} deriving Show

newContext :: Context
newContext = Context ConcreteStateA [] "初始数据"

setState :: Context -> State -> Context
setState context newState = context {
  currentState = newState,
  stateHistory = getStateName newState : stateHistory context
}

getCurrentState :: Context -> String
getCurrentState = getStateName . currentState

getStateHistory :: Context -> [String]
getStateHistory = reverse . stateHistory

-- 具体状态
data ConcreteStateA = ConcreteStateA deriving Show

instance State ConcreteStateA where
  handle _ context = 
    let newContext = setState context ConcreteStateB
        message = "状态A处理请求，转换到状态B"
    in (message, newContext)
  
  getStateName _ = "StateA"
  canTransitionTo _ "StateB" = True
  canTransitionTo _ _ = False

data ConcreteStateB = ConcreteStateB deriving Show

instance State ConcreteStateB where
  handle _ context = 
    let newContext = setState context ConcreteStateC
        message = "状态B处理请求，转换到状态C"
    in (message, newContext)
  
  getStateName _ = "StateB"
  canTransitionTo _ "StateC" = True
  canTransitionTo _ _ = False

data ConcreteStateC = ConcreteStateC deriving Show

instance State ConcreteStateC where
  handle _ context = 
    let newContext = setState context ConcreteStateA
        message = "状态C处理请求，转换到状态A"
    in (message, newContext)
  
  getStateName _ = "StateC"
  canTransitionTo _ "StateA" = True
  canTransitionTo _ _ = False

-- 状态机
data StateMachine = StateMachine {
  context :: Context,
  transitions :: Map String [String]
} deriving Show

newStateMachine :: StateMachine
newStateMachine = StateMachine newContext $ Map.fromList [
  ("StateA", ["StateB"]),
  ("StateB", ["StateC"]),
  ("StateC", ["StateA"])
]

request :: StateMachine -> (String, StateMachine)
request machine = 
  let (message, newContext) = handle (currentState $ context machine) (context machine)
      newMachine = machine { context = newContext }
  in (message, newMachine)

-- 状态验证器
validateTransition :: StateMachine -> String -> Bool
validateTransition machine targetState = 
  let currentStateName = getCurrentState (context machine)
      validTransitions = Map.findWithDefault [] currentStateName (transitions machine)
  in targetState `elem` validTransitions

-- 使用示例
main :: IO ()
main = do
  let machine = newStateMachine
  
  putStrLn "状态模式示例:"
  
  -- 执行状态转换
  let (result1, machine1) = request machine
  putStrLn $ "请求1: " ++ result1
  putStrLn $ "当前状态: " ++ getCurrentState (context machine1)
  putStrLn $ "状态历史: " ++ show (getStateHistory (context machine1))
  
  let (result2, machine2) = request machine1
  putStrLn $ "请求2: " ++ result2
  putStrLn $ "当前状态: " ++ getCurrentState (context machine2)
  
  let (result3, machine3) = request machine2
  putStrLn $ "请求3: " ++ result3
  putStrLn $ "当前状态: " ++ getCurrentState (context machine3)
  
  let (result4, machine4) = request machine3
  putStrLn $ "请求4: " ++ result4
  putStrLn $ "当前状态: " ++ getCurrentState (context machine4)
  
  -- 验证状态转换
  putStrLn $ "\n状态转换验证:"
  putStrLn $ "StateA -> StateB: " ++ show (validateTransition machine "StateB")
  putStrLn $ "StateA -> StateC: " ++ show (validateTransition machine "StateC")
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 状态trait
trait State {
    fn handle(&self, context: &mut Context) -> String;
    fn get_state_name(&self) -> String;
    fn can_transition_to(&self, target_state: &str) -> bool;
}

// 上下文
#[derive(Debug)]
struct Context {
    state: Box<dyn State>,
    state_history: Vec<String>,
    data: String,
}

impl Context {
    fn new() -> Self {
        Context {
            state: Box::new(ConcreteStateA),
            state_history: Vec::new(),
            data: "初始数据".to_string(),
        }
    }
    
    fn set_state(&mut self, state: Box<dyn State>) {
        let state_name = state.get_state_name();
        self.state_history.push(state_name);
        self.state = state;
    }
    
    fn get_current_state(&self) -> String {
        self.state.get_state_name()
    }
    
    fn get_state_history(&self) -> Vec<String> {
        self.state_history.clone()
    }
}

// 具体状态A
#[derive(Debug)]
struct ConcreteStateA;

impl State for ConcreteStateA {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateB));
        "状态A处理请求，转换到状态B".to_string()
    }
    
    fn get_state_name(&self) -> String {
        "StateA".to_string()
    }
    
    fn can_transition_to(&self, target_state: &str) -> bool {
        target_state == "StateB"
    }
}

// 具体状态B
#[derive(Debug)]
struct ConcreteStateB;

impl State for ConcreteStateB {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateC));
        "状态B处理请求，转换到状态C".to_string()
    }
    
    fn get_state_name(&self) -> String {
        "StateB".to_string()
    }
    
    fn can_transition_to(&self, target_state: &str) -> bool {
        target_state == "StateC"
    }
}

// 具体状态C
#[derive(Debug)]
struct ConcreteStateC;

impl State for ConcreteStateC {
    fn handle(&self, context: &mut Context) -> String {
        context.set_state(Box::new(ConcreteStateA));
        "状态C处理请求，转换到状态A".to_string()
    }
    
    fn get_state_name(&self) -> String {
        "StateC".to_string()
    }
    
    fn can_transition_to(&self, target_state: &str) -> bool {
        target_state == "StateA"
    }
}

// 状态机
#[derive(Debug)]
struct StateMachine {
    context: Context,
    transitions: HashMap<String, Vec<String>>,
}

impl StateMachine {
    fn new() -> Self {
        let mut transitions = HashMap::new();
        transitions.insert("StateA".to_string(), vec!["StateB".to_string()]);
        transitions.insert("StateB".to_string(), vec!["StateC".to_string()]);
        transitions.insert("StateC".to_string(), vec!["StateA".to_string()]);
        
        StateMachine {
            context: Context::new(),
            transitions,
        }
    }
    
    fn request(&mut self) -> String {
        self.state.handle(&mut self.context)
    }
    
    fn get_current_state(&self) -> String {
        self.context.get_current_state()
    }
    
    fn get_state_history(&self) -> Vec<String> {
        self.context.get_state_history()
    }
    
    fn validate_transition(&self, target_state: &str) -> bool {
        let current_state = self.get_current_state();
        if let Some(valid_transitions) = self.transitions.get(&current_state) {
            valid_transitions.contains(&target_state.to_string())
        } else {
            false
        }
    }
}

// 使用示例
fn main() {
    let mut machine = StateMachine::new();
    
    println!("状态模式示例:");
    
    // 执行状态转换
    let result1 = machine.request();
    println!("请求1: {}", result1);
    println!("当前状态: {}", machine.get_current_state());
    println!("状态历史: {:?}", machine.get_state_history());
    
    let result2 = machine.request();
    println!("请求2: {}", result2);
    println!("当前状态: {}", machine.get_current_state());
    
    let result3 = machine.request();
    println!("请求3: {}", result3);
    println!("当前状态: {}", machine.get_current_state());
    
    let result4 = machine.request();
    println!("请求4: {}", result4);
    println!("当前状态: {}", machine.get_current_state());
    
    // 验证状态转换
    println!("\n状态转换验证:");
    println!("StateA -> StateB: {}", machine.validate_transition("StateB"));
    println!("StateA -> StateC: {}", machine.validate_transition("StateC"));
}
```

### 3.3 Lean实现

```lean
-- 状态类型
inductive State where
  | ConcreteStateA : State
  | ConcreteStateB : State
  | ConcreteStateC : State

-- 上下文类型
structure Context where
  currentState : State
  stateHistory : List String
  data : String

-- 创建新上下文
def newContext : Context := { 
  currentState := State.ConcreteStateA,
  stateHistory := [],
  data := "初始数据"
}

-- 设置状态
def setState (context : Context) (state : State) : Context :=
  { context with 
    currentState := state,
    stateHistory := getStateName state :: context.stateHistory 
  }

-- 获取状态名称
def getStateName : State → String
  | State.ConcreteStateA => "StateA"
  | State.ConcreteStateB => "StateB"
  | State.ConcreteStateC => "StateC"

-- 处理状态
def handle : State → Context → String × Context
  | State.ConcreteStateA, context => 
    ("状态A处理请求，转换到状态B", setState context State.ConcreteStateB)
  | State.ConcreteStateB, context => 
    ("状态B处理请求，转换到状态C", setState context State.ConcreteStateC)
  | State.ConcreteStateC, context => 
    ("状态C处理请求，转换到状态A", setState context State.ConcreteStateA)

-- 检查是否可以转换到目标状态
def canTransitionTo : State → String → Bool
  | State.ConcreteStateA, "StateB" => true
  | State.ConcreteStateB, "StateC" => true
  | State.ConcreteStateC, "StateA" => true
  | _, _ => false

-- 获取当前状态
def getCurrentState (context : Context) : String :=
  getStateName context.currentState

-- 获取状态历史
def getStateHistory (context : Context) : List String :=
  context.stateHistory.reverse

-- 状态机类型
structure StateMachine where
  context : Context
  transitions : List (String × List String)

-- 创建新状态机
def newStateMachine : StateMachine := {
  context := newContext,
  transitions := [
    ("StateA", ["StateB"]),
    ("StateB", ["StateC"]),
    ("StateC", ["StateA"])
  ]
}

-- 请求处理
def request (machine : StateMachine) : String × StateMachine :=
  let (message, newContext) := handle machine.context.currentState machine.context
  (message, { machine with context := newContext })

-- 验证状态转换
def validateTransition (machine : StateMachine) (targetState : String) : Bool :=
  let currentState := getCurrentState machine.context
  let validTransitions := 
    match machine.transitions.find? (λ (state, _) => state = currentState) with
    | some (_, transitions) => transitions
    | none => []
  targetState ∈ validTransitions

-- 使用示例
def main : IO Unit := do
  let machine := newStateMachine
  
  IO.println "状态模式示例:"
  
  -- 执行状态转换
  let (result1, machine1) := request machine
  IO.println s!"请求1: {result1}"
  IO.println s!"当前状态: {getCurrentState machine1.context}"
  IO.println s!"状态历史: {getStateHistory machine1.context}"
  
  let (result2, machine2) := request machine1
  IO.println s!"请求2: {result2}"
  IO.println s!"当前状态: {getCurrentState machine2.context}"
  
  let (result3, machine3) := request machine2
  IO.println s!"请求3: {result3}"
  IO.println s!"当前状态: {getCurrentState machine3.context}"
  
  let (result4, machine4) := request machine3
  IO.println s!"请求4: {result4}"
  IO.println s!"当前状态: {getCurrentState machine4.context}"
  
  -- 验证状态转换
  IO.println "\n状态转换验证:"
  IO.println s!"StateA -> StateB: {validateTransition machine \"StateB\"}"
  IO.println s!"StateA -> StateC: {validateTransition machine \"StateC\"}"
```

## 4. 工程实践

### 4.1 设计考虑

- **状态转换规则**: 明确定义状态之间的转换规则
- **状态验证**: 确保状态转换的合法性
- **状态历史**: 记录状态转换的历史
- **错误处理**: 处理无效的状态转换

### 4.2 实现模式

```haskell
-- 带验证的状态机
data ValidatedStateMachine = ValidatedStateMachine {
  context :: Context,
  transitions :: Map String [String],
  validators :: Map String (String -> Bool)
}

-- 异步状态机
data AsyncStateMachine = AsyncStateMachine {
  context :: Context,
  executor :: ThreadPool
}

-- 带监控的状态机
data MonitoredStateMachine = MonitoredStateMachine {
  context :: Context,
  metrics :: MVar StateMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data StateError = 
  InvalidTransition String String
  | StateNotFound String
  | TransitionNotAllowed String String

-- 安全状态转换
safeTransition :: StateMachine -> String -> IO (Either StateError StateMachine)
safeTransition machine targetState = 
  if validateTransition machine targetState
  then do
    let newMachine = performTransition machine targetState
    return $ Right newMachine
  else return $ Left $ InvalidTransition (getCurrentState machine) targetState
```

## 5. 性能优化

### 5.1 状态缓存

- **状态对象缓存**: 缓存状态对象避免重复创建
- **转换规则缓存**: 缓存状态转换规则
- **历史记录缓存**: 缓存状态历史记录

### 5.2 状态池

```haskell
-- 状态对象池
data StatePool = StatePool {
  states :: Map String State,
  pool :: MVar [State]
}

getStateFromPool :: StatePool -> String -> IO State
getStateFromPool pool stateName = do
  availableStates <- takeMVar (pool pool)
  case availableStates of
    (state:rest) -> do
      putMVar (pool pool) rest
      return state
    [] -> return $ createState stateName
```

### 5.3 并行状态处理

```haskell
-- 并行状态处理器
data ParallelStateProcessor = ParallelStateProcessor {
  processors :: [StateProcessor],
  executor :: ThreadPool
}

processStatesParallel :: ParallelStateProcessor -> [String] -> IO [String]
processStatesParallel processor states = 
  mapConcurrently (\s -> processState s) states
```

## 6. 应用场景

### 6.1 游戏角色状态

```haskell
-- 游戏角色状态
data GameCharacterState = GameCharacterState {
  health :: Int,
  stamina :: Int,
  state :: CharacterState
}

data CharacterState = 
  IdleState
  | WalkingState
  | RunningState
  | AttackingState
  | DefendingState

updateCharacterState :: GameCharacterState -> String -> GameCharacterState
updateCharacterState character event = 
  case (state character, event) of
    (IdleState, "move") -> character { state = WalkingState }
    (WalkingState, "run") -> character { state = RunningState }
    (WalkingState, "stop") -> character { state = IdleState }
    (RunningState, "stop") -> character { state = IdleState }
    (_, "attack") -> character { state = AttackingState }
    (_, "defend") -> character { state = DefendingState }
    (_, _) -> character
```

### 6.2 工作流状态机

```haskell
-- 工作流状态
data WorkflowState = 
  CreatedState
  | InProgressState
  | ReviewState
  | CompletedState
  | CancelledState

data Workflow = Workflow {
  id :: String,
  state :: WorkflowState,
  data :: String
}

transitionWorkflow :: Workflow -> String -> Workflow
transitionWorkflow workflow event = 
  case (state workflow, event) of
    (CreatedState, "start") -> workflow { state = InProgressState }
    (InProgressState, "review") -> workflow { state = ReviewState }
    (ReviewState, "approve") -> workflow { state = CompletedState }
    (ReviewState, "reject") -> workflow { state = InProgressState }
    (_, "cancel") -> workflow { state = CancelledState }
    (_, _) -> workflow
```

### 6.3 网络连接状态

```haskell
-- 网络连接状态
data ConnectionState = 
  DisconnectedState
  | ConnectingState
  | ConnectedState
  | ReconnectingState
  | ErrorState

data NetworkConnection = NetworkConnection {
  host :: String,
  port :: Int,
  state :: ConnectionState,
  retryCount :: Int
}

handleConnectionEvent :: NetworkConnection -> String -> NetworkConnection
handleConnectionEvent connection event = 
  case (state connection, event) of
    (DisconnectedState, "connect") -> connection { state = ConnectingState }
    (ConnectingState, "connected") -> connection { state = ConnectedState }
    (ConnectingState, "failed") -> connection { state = ErrorState }
    (ConnectedState, "disconnect") -> connection { state = DisconnectedState }
    (ConnectedState, "error") -> connection { state = ReconnectingState }
    (ReconnectingState, "connected") -> connection { state = ConnectedState }
    (ReconnectingState, "failed") -> 
      if retryCount connection < 3
      then connection { retryCount = retryCount connection + 1 }
      else connection { state = ErrorState }
    (_, _) -> connection
```

### 6.4 订单状态管理

```haskell
-- 订单状态
data OrderState = 
  PendingState
  | ConfirmedState
  | ShippedState
  | DeliveredState
  | CancelledState
  | RefundedState

data Order = Order {
  orderId :: String,
  customerId :: String,
  items :: [String],
  state :: OrderState,
  totalAmount :: Double
}

processOrderEvent :: Order -> String -> Order
processOrderEvent order event = 
  case (state order, event) of
    (PendingState, "confirm") -> order { state = ConfirmedState }
    (ConfirmedState, "ship") -> order { state = ShippedState }
    (ShippedState, "deliver") -> order { state = DeliveredState }
    (PendingState, "cancel") -> order { state = CancelledState }
    (ConfirmedState, "cancel") -> order { state = CancelledState }
    (DeliveredState, "refund") -> order { state = RefundedState }
    (_, _) -> order
```

## 7. 最佳实践

### 7.1 设计原则

- **明确定义状态转换规则**: 确保状态转换的清晰性和一致性
- **避免状态类过于复杂**: 保持状态类的简洁性
- **支持状态历史记录**: 记录状态转换的历史
- **状态验证**: 验证状态转换的合法性

### 7.2 实现建议

```haskell
-- 状态工厂
class StateFactory a where
  createState :: String -> Maybe a
  listStates :: [String]
  validateState :: a -> Bool

-- 状态注册表
data StateRegistry = StateRegistry {
  states :: Map String (forall a. State a => a),
  metadata :: Map String String
}

-- 线程安全状态机
data ThreadSafeStateMachine = ThreadSafeStateMachine {
  machine :: MVar StateMachine,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 状态测试
testStateTransition :: StateMachine -> String -> Bool
testStateTransition machine targetState = 
  validateTransition machine targetState

-- 性能测试
benchmarkStateMachine :: StateMachine -> [String] -> IO Double
benchmarkStateMachine machine events = do
  start <- getCurrentTime
  foldM (\m e -> return $ snd $ request m) machine events
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的状态类型
- **序列化**: 支持状态的序列化和反序列化
- **版本控制**: 支持状态的版本管理
- **分布式**: 支持跨网络的状态同步

## 8. 总结

状态模式是管理对象状态变化的强大工具，通过将状态封装为独立的对象提供了清晰的状态转换和灵活的行为变化。在实现时需要注意状态转换规则的明确定义、状态验证和性能优化。该模式在游戏角色状态、工作流状态机、网络连接状态、订单状态管理等场景中都有广泛应用。
