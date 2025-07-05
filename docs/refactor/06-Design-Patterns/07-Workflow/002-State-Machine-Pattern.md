# 状态机模式（State Machine Pattern）

## 概述
状态机模式是一种工作流设计模式，通过定义有限状态和状态转换来建模复杂的工作流程，每个状态都有特定的行为和转换条件。

## 理论基础
- **状态（State）**：系统在某一时刻的配置
- **事件（Event）**：触发状态转换的输入
- **转换（Transition）**：从一个状态到另一个状态的映射
- **动作（Action）**：状态转换时执行的操作

## Rust实现示例
```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use uuid::Uuid;

// 状态枚举
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OrderState {
    Created,
    Pending,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
}

// 事件枚举
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum OrderEvent {
    Submit,
    Approve,
    Process,
    Ship,
    Deliver,
    Cancel,
}

// 状态机配置
struct StateMachineConfig {
    initial_state: OrderState,
    final_states: Vec<OrderState>,
    transitions: HashMap<(OrderState, OrderEvent), OrderState>,
    actions: HashMap<(OrderState, OrderEvent), Box<dyn Fn() -> Result<(), String> + Send + Sync>>,
    guards: HashMap<(OrderState, OrderEvent), Box<dyn Fn() -> bool + Send + Sync>>,
}

impl StateMachineConfig {
    fn new(initial_state: OrderState) -> Self {
        Self {
            initial_state,
            final_states: Vec::new(),
            transitions: HashMap::new(),
            actions: HashMap::new(),
            guards: HashMap::new(),
        }
    }
    
    fn add_transition(&mut self, from: OrderState, event: OrderEvent, to: OrderState) {
        self.transitions.insert((from, event), to);
    }
    
    fn add_action(&mut self, from: OrderState, event: OrderEvent, action: Box<dyn Fn() -> Result<(), String> + Send + Sync>) {
        self.actions.insert((from, event), action);
    }
    
    fn add_guard(&mut self, from: OrderState, event: OrderEvent, guard: Box<dyn Fn() -> bool + Send + Sync>) {
        self.guards.insert((from, event), guard);
    }
    
    fn add_final_state(&mut self, state: OrderState) {
        self.final_states.push(state);
    }
    
    fn can_transition(&self, from: &OrderState, event: &OrderEvent) -> bool {
        // 检查转换是否存在
        if !self.transitions.contains_key(&(from.clone(), event.clone())) {
            return false;
        }
        
        // 检查守卫条件
        if let Some(guard) = self.guards.get(&(from.clone(), event.clone())) {
            if !guard() {
                return false;
            }
        }
        
        true
    }
    
    fn get_next_state(&self, from: &OrderState, event: &OrderEvent) -> Option<OrderState> {
        self.transitions.get(&(from.clone(), event.clone())).cloned()
    }
    
    fn is_final_state(&self, state: &OrderState) -> bool {
        self.final_states.contains(state)
    }
}

// 状态机实例
struct StateMachine {
    id: String,
    config: StateMachineConfig,
    current_state: Arc<Mutex<OrderState>>,
    history: Arc<Mutex<Vec<(OrderState, OrderEvent, OrderState)>>>,
    context: Arc<Mutex<HashMap<String, String>>>,
}

impl StateMachine {
    fn new(config: StateMachineConfig) -> Self {
        let current_state = Arc::new(Mutex::new(config.initial_state.clone()));
        let history = Arc::new(Mutex::new(Vec::new()));
        let context = Arc::new(Mutex::new(HashMap::new()));
        
        Self {
            id: Uuid::new_v4().to_string(),
            config,
            current_state,
            history,
            context,
        }
    }
    
    async fn trigger_event(&self, event: OrderEvent) -> Result<OrderState, String> {
        let current_state = { *self.current_state.lock().unwrap() };
        
        if !self.config.can_transition(&current_state, &event) {
            return Err(format!("无法从状态 {:?} 通过事件 {:?} 转换", current_state, event));
        }
        
        // 执行动作
        if let Some(action) = self.config.actions.get(&(current_state.clone(), event.clone())) {
            action()?;
        }
        
        // 获取下一个状态
        let next_state = self.config.get_next_state(&current_state, &event)
            .ok_or("转换配置错误")?;
        
        // 更新状态
        {
            let mut state_guard = self.current_state.lock().unwrap();
            *state_guard = next_state.clone();
        }
        
        // 记录历史
        {
            let mut history_guard = self.history.lock().unwrap();
            history_guard.push((current_state, event, next_state.clone()));
        }
        
        println!("状态机 {}: {:?} -> {:?}", self.id, current_state, next_state);
        Ok(next_state)
    }
    
    fn get_current_state(&self) -> OrderState {
        { *self.current_state.lock().unwrap() }
    }
    
    fn get_history(&self) -> Vec<(OrderState, OrderEvent, OrderState)> {
        { self.history.lock().unwrap().clone() }
    }
    
    fn set_context(&self, key: String, value: String) {
        let mut context = self.context.lock().unwrap();
        context.insert(key, value);
    }
    
    fn get_context(&self, key: &str) -> Option<String> {
        let context = self.context.lock().unwrap();
        context.get(key).cloned()
    }
    
    fn is_final(&self) -> bool {
        let current_state = self.get_current_state();
        self.config.is_final_state(&current_state)
    }
}

// 订单状态机
struct OrderStateMachine {
    state_machine: StateMachine,
    order_id: String,
    customer_id: String,
    total_amount: f64,
}

impl OrderStateMachine {
    fn new(order_id: String, customer_id: String, total_amount: f64) -> Self {
        let mut config = StateMachineConfig::new(OrderState::Created);
        
        // 定义转换
        config.add_transition(OrderState::Created, OrderEvent::Submit, OrderState::Pending);
        config.add_transition(OrderState::Pending, OrderEvent::Approve, OrderState::Processing);
        config.add_transition(OrderState::Processing, OrderEvent::Process, OrderState::Shipped);
        config.add_transition(OrderState::Shipped, OrderEvent::Ship, OrderState::Delivered);
        config.add_transition(OrderState::Created, OrderEvent::Cancel, OrderState::Cancelled);
        config.add_transition(OrderState::Pending, OrderEvent::Cancel, OrderState::Cancelled);
        config.add_transition(OrderState::Processing, OrderEvent::Cancel, OrderState::Cancelled);
        
        // 定义动作
        config.add_action(OrderState::Created, OrderEvent::Submit, Box::new(|| {
            println!("执行：提交订单");
            Ok(())
        }));
        
        config.add_action(OrderState::Pending, OrderEvent::Approve, Box::new(|| {
            println!("执行：审批订单");
            Ok(())
        }));
        
        config.add_action(OrderState::Processing, OrderEvent::Process, Box::new(|| {
            println!("执行：处理订单");
            Ok(())
        }));
        
        config.add_action(OrderState::Shipped, OrderEvent::Ship, Box::new(|| {
            println!("执行：发货");
            Ok(())
        }));
        
        config.add_action(OrderState::Created, OrderEvent::Cancel, Box::new(|| {
            println!("执行：取消订单");
            Ok(())
        }));
        
        // 定义守卫条件
        config.add_guard(OrderState::Pending, OrderEvent::Approve, Box::new(|| {
            // 检查库存是否充足
            true
        }));
        
        config.add_guard(OrderState::Processing, OrderEvent::Process, Box::new(|| {
            // 检查支付是否完成
            true
        }));
        
        // 定义最终状态
        config.add_final_state(OrderState::Delivered);
        config.add_final_state(OrderState::Cancelled);
        
        Self {
            state_machine: StateMachine::new(config),
            order_id,
            customer_id,
            total_amount,
        }
    }
    
    async fn submit_order(&self) -> Result<OrderState, String> {
        self.state_machine.trigger_event(OrderEvent::Submit).await
    }
    
    async fn approve_order(&self) -> Result<OrderState, String> {
        self.state_machine.trigger_event(OrderEvent::Approve).await
    }
    
    async fn process_order(&self) -> Result<OrderState, String> {
        self.state_machine.trigger_event(OrderEvent::Process).await
    }
    
    async fn ship_order(&self) -> Result<OrderState, String> {
        self.state_machine.trigger_event(OrderEvent::Ship).await
    }
    
    async fn cancel_order(&self) -> Result<OrderState, String> {
        self.state_machine.trigger_event(OrderEvent::Cancel).await
    }
    
    fn get_current_state(&self) -> OrderState {
        self.state_machine.get_current_state()
    }
    
    fn get_history(&self) -> Vec<(OrderState, OrderEvent, OrderState)> {
        self.state_machine.get_history()
    }
    
    fn is_completed(&self) -> bool {
        self.state_machine.is_final()
    }
}

// 工作流状态机
struct WorkflowStateMachine {
    state_machine: StateMachine,
    workflow_id: String,
    steps: Vec<String>,
    current_step: usize,
}

impl WorkflowStateMachine {
    fn new(workflow_id: String, steps: Vec<String>) -> Self {
        let mut config = StateMachineConfig::new(OrderState::Created);
        
        // 简化的工作流状态转换
        config.add_transition(OrderState::Created, OrderEvent::Submit, OrderState::Pending);
        config.add_transition(OrderState::Pending, OrderEvent::Approve, OrderState::Processing);
        config.add_transition(OrderState::Processing, OrderEvent::Process, OrderState::Shipped);
        config.add_transition(OrderState::Shipped, OrderEvent::Ship, OrderState::Delivered);
        
        Self {
            state_machine: StateMachine::new(config),
            workflow_id,
            steps,
            current_step: 0,
        }
    }
    
    async fn execute_step(&self) -> Result<OrderState, String> {
        if self.current_step >= self.steps.len() {
            return Err("工作流已完成".to_string());
        }
        
        let step_name = &self.steps[self.current_step];
        println!("执行工作流步骤: {}", step_name);
        
        // 根据步骤执行相应的状态转换
        let event = match self.current_step {
            0 => OrderEvent::Submit,
            1 => OrderEvent::Approve,
            2 => OrderEvent::Process,
            3 => OrderEvent::Ship,
            _ => return Err("未知步骤".to_string()),
        };
        
        let result = self.state_machine.trigger_event(event).await;
        if result.is_ok() {
            // 更新步骤
            // 注意：这里需要可变引用，实际实现中需要更复杂的同步机制
        }
        
        result
    }
    
    fn get_progress(&self) -> f64 {
        if self.steps.is_empty() {
            0.0
        } else {
            (self.current_step as f64) / (self.steps.len() as f64)
        }
    }
}

// 状态机管理器
struct StateMachineManager {
    machines: Arc<Mutex<HashMap<String, Arc<StateMachine>>>>,
}

impl StateMachineManager {
    fn new() -> Self {
        Self {
            machines: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn register_machine(&self, machine: StateMachine) {
        let mut machines = self.machines.lock().unwrap();
        machines.insert(machine.id.clone(), Arc::new(machine));
    }
    
    async fn get_machine(&self, machine_id: &str) -> Option<Arc<StateMachine>> {
        let machines = self.machines.lock().unwrap();
        machines.get(machine_id).cloned()
    }
    
    async fn trigger_event(&self, machine_id: &str, event: OrderEvent) -> Result<OrderState, String> {
        if let Some(machine) = self.get_machine(machine_id).await {
            machine.trigger_event(event).await
        } else {
            Err("状态机不存在".to_string())
        }
    }
    
    async fn get_all_machines(&self) -> Vec<Arc<StateMachine>> {
        let machines = self.machines.lock().unwrap();
        machines.values().cloned().collect()
    }
}

#[tokio::main]
async fn main() {
    // 订单状态机测试
    println!("=== 订单状态机测试 ===");
    
    let order_machine = OrderStateMachine::new(
        "order-001".to_string(),
        "customer-001".to_string(),
        99.99,
    );
    
    println!("初始状态: {:?}", order_machine.get_current_state());
    
    // 提交订单
    match order_machine.submit_order().await {
        Ok(state) => println!("提交订单后状态: {:?}", state),
        Err(error) => println!("提交订单失败: {}", error),
    }
    
    // 审批订单
    match order_machine.approve_order().await {
        Ok(state) => println!("审批订单后状态: {:?}", state),
        Err(error) => println!("审批订单失败: {}", error),
    }
    
    // 处理订单
    match order_machine.process_order().await {
        Ok(state) => println!("处理订单后状态: {:?}", state),
        Err(error) => println!("处理订单失败: {}", error),
    }
    
    // 发货
    match order_machine.ship_order().await {
        Ok(state) => println!("发货后状态: {:?}", state),
        Err(error) => println!("发货失败: {}", error),
    }
    
    println!("订单完成: {}", order_machine.is_completed());
    println!("状态历史: {:?}", order_machine.get_history());
    
    // 工作流状态机测试
    println!("\n=== 工作流状态机测试 ===");
    
    let steps = vec![
        "步骤1: 数据验证".to_string(),
        "步骤2: 业务处理".to_string(),
        "步骤3: 结果输出".to_string(),
        "步骤4: 完成".to_string(),
    ];
    
    let workflow_machine = WorkflowStateMachine::new("workflow-001".to_string(), steps);
    
    println!("工作流进度: {:.2}%", workflow_machine.get_progress() * 100.0);
    
    // 执行工作流步骤
    for i in 0..4 {
        match workflow_machine.execute_step().await {
            Ok(state) => println!("步骤 {} 执行后状态: {:?}", i + 1, state),
            Err(error) => println!("步骤 {} 执行失败: {}", i + 1, error),
        }
    }
    
    // 状态机管理器测试
    println!("\n=== 状态机管理器测试 ===");
    
    let manager = StateMachineManager::new();
    
    // 创建并注册状态机
    let config = StateMachineConfig::new(OrderState::Created);
    let machine = StateMachine::new(config);
    let machine_id = machine.id.clone();
    
    manager.register_machine(machine).await;
    
    // 触发事件
    match manager.trigger_event(&machine_id, OrderEvent::Submit).await {
        Ok(state) => println!("管理器触发事件后状态: {:?}", state),
        Err(error) => println!("管理器触发事件失败: {}", error),
    }
    
    // 获取所有状态机
    let all_machines = manager.get_all_machines().await;
    println!("管理器中的状态机数量: {}", all_machines.len());
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Data.IORef
import Data.Map as M
import System.Random
import Text.Printf

-- 状态枚举
data OrderState = Created | Pending | Processing | Shipped | Delivered | Cancelled deriving (Eq, Show, Ord)

-- 事件枚举
data OrderEvent = Submit | Approve | Process | Ship | Deliver | Cancel deriving (Eq, Show, Ord)

-- 状态机配置
data StateMachineConfig = StateMachineConfig
    { initialState :: OrderState
    , finalStates :: [OrderState]
    , transitions :: M.Map (OrderState, OrderEvent) OrderState
    , actions :: M.Map (OrderState, OrderEvent) (IO (Either String ()))
    , guards :: M.Map (OrderState, OrderEvent) (IO Bool)
    }

newStateMachineConfig :: OrderState -> StateMachineConfig
newStateMachineConfig initialState = StateMachineConfig
    { initialState = initialState
    , finalStates = []
    , transitions = M.empty
    , actions = M.empty
    , guards = M.empty
    }

addTransition :: StateMachineConfig -> OrderState -> OrderEvent -> OrderState -> StateMachineConfig
addTransition config from event to = 
    config { transitions = M.insert (from, event) to (transitions config) }

addAction :: StateMachineConfig -> OrderState -> OrderEvent -> IO (Either String ()) -> StateMachineConfig
addAction config from event action = 
    config { actions = M.insert (from, event) action (actions config) }

addGuard :: StateMachineConfig -> OrderState -> OrderEvent -> IO Bool -> StateMachineConfig
addGuard config from event guard = 
    config { guards = M.insert (from, event) guard (guards config) }

addFinalState :: StateMachineConfig -> OrderState -> StateMachineConfig
addFinalState config state = 
    config { finalStates = state : finalStates config }

canTransition :: StateMachineConfig -> OrderState -> OrderEvent -> IO Bool
canTransition config from event = do
    -- 检查转换是否存在
    let transitionExists = M.member (from, event) (transitions config)
    if not transitionExists
        then return False
        else do
            -- 检查守卫条件
            case M.lookup (from, event) (guards config) of
                Just guard -> guard
                Nothing -> return True

getNextState :: StateMachineConfig -> OrderState -> OrderEvent -> Maybe OrderState
getNextState config from event = M.lookup (from, event) (transitions config)

isFinalState :: StateMachineConfig -> OrderState -> Bool
isFinalState config state = state `elem` finalStates config

-- 状态机实例
data StateMachine = StateMachine
    { machineId :: String
    , config :: StateMachineConfig
    , currentState :: IORef OrderState
    , history :: IORef [(OrderState, OrderEvent, OrderState)]
    , context :: IORef (M.Map String String)
    }

newStateMachine :: StateMachineConfig -> IO StateMachine
newStateMachine config = do
    currentState <- newIORef (initialState config)
    history <- newIORef []
    context <- newIORef M.empty
    return $ StateMachine (show $ randomRIO (0, 1000000)) config currentState history context

triggerEvent :: StateMachine -> OrderEvent -> IO (Either String OrderState)
triggerEvent machine event = do
    currentState <- readIORef (currentState machine)
    
    canTransitionResult <- canTransition (config machine) currentState event
    if not canTransitionResult
        then return $ Left $ "无法从状态 " ++ show currentState ++ " 通过事件 " ++ show event ++ " 转换"
        else do
            -- 执行动作
            case M.lookup (currentState, event) (actions (config machine)) of
                Just action -> do
                    actionResult <- action
                    case actionResult of
                        Left error -> return $ Left error
                        Right _ -> return ()
                Nothing -> return ()
            
            -- 获取下一个状态
            let nextState = getNextState (config machine) currentState event
            case nextState of
                Just state -> do
                    -- 更新状态
                    writeIORef (currentState machine) state
                    
                    -- 记录历史
                    modifyIORef (history machine) ((currentState, event, state) :)
                    
                    printf "状态机 %s: %s -> %s\n" (machineId machine) (show currentState) (show state)
                    return $ Right state
                Nothing -> return $ Left "转换配置错误"

getCurrentState :: StateMachine -> IO OrderState
getCurrentState machine = readIORef (currentState machine)

getHistory :: StateMachine -> IO [(OrderState, OrderEvent, OrderState)]
getHistory machine = readIORef (history machine)

setContext :: StateMachine -> String -> String -> IO ()
setContext machine key value = do
    modifyIORef (context machine) (M.insert key value)

getContext :: StateMachine -> String -> IO (Maybe String)
getContext machine key = do
    contextMap <- readIORef (context machine)
    return $ M.lookup key contextMap

isFinal :: StateMachine -> IO Bool
isFinal machine = do
    currentState <- getCurrentState machine
    return $ isFinalState (config machine) currentState

-- 订单状态机
data OrderStateMachine = OrderStateMachine
    { stateMachine :: StateMachine
    , orderId :: String
    , customerId :: String
    , totalAmount :: Double
    }

newOrderStateMachine :: String -> String -> Double -> IO OrderStateMachine
newOrderStateMachine orderId customerId totalAmount = do
    let config = newStateMachineConfig Created
        configWithTransitions = addTransition (addTransition (addTransition (addTransition (addTransition (addTransition (addTransition config Created Submit Pending) Pending Approve Processing) Processing Process Shipped) Shipped Ship Delivered) Created Cancel Cancelled) Pending Cancel Cancelled) Processing Cancel Cancelled
        configWithActions = addAction (addAction (addAction (addAction (addAction configWithTransitions Created Submit (putStrLn "执行：提交订单" >> return (Right ()))) Pending Approve (putStrLn "执行：审批订单" >> return (Right ()))) Processing Process (putStrLn "执行：处理订单" >> return (Right ()))) Shipped Ship (putStrLn "执行：发货" >> return (Right ()))) Created Cancel (putStrLn "执行：取消订单" >> return (Right ())))
        configWithGuards = addGuard (addGuard configWithActions Pending Approve (return True)) Processing Process (return True)
        finalConfig = addFinalState (addFinalState configWithGuards Delivered) Cancelled
    
    stateMachine <- newStateMachine finalConfig
    return $ OrderStateMachine stateMachine orderId customerId totalAmount

submitOrder :: OrderStateMachine -> IO (Either String OrderState)
submitOrder machine = triggerEvent (stateMachine machine) Submit

approveOrder :: OrderStateMachine -> IO (Either String OrderState)
approveOrder machine = triggerEvent (stateMachine machine) Approve

processOrder :: OrderStateMachine -> IO (Either String OrderState)
processOrder machine = triggerEvent (stateMachine machine) Process

shipOrder :: OrderStateMachine -> IO (Either String OrderState)
shipOrder machine = triggerEvent (stateMachine machine) Ship

cancelOrder :: OrderStateMachine -> IO (Either String OrderState)
cancelOrder machine = triggerEvent (stateMachine machine) Cancel

getCurrentOrderState :: OrderStateMachine -> IO OrderState
getCurrentOrderState machine = getCurrentState (stateMachine machine)

getOrderHistory :: OrderStateMachine -> IO [(OrderState, OrderEvent, OrderState)]
getOrderHistory machine = getHistory (stateMachine machine)

isOrderCompleted :: OrderStateMachine -> IO Bool
isOrderCompleted machine = isFinal (stateMachine machine)

-- 工作流状态机
data WorkflowStateMachine = WorkflowStateMachine
    { workflowStateMachine :: StateMachine
    , workflowId :: String
    , steps :: [String]
    , currentStep :: IORef Int
    }

newWorkflowStateMachine :: String -> [String] -> IO WorkflowStateMachine
newWorkflowStateMachine workflowId steps = do
    let config = newStateMachineConfig Created
        configWithTransitions = addTransition (addTransition (addTransition config Created Submit Pending) Pending Approve Processing) Processing Process Shipped
    stateMachine <- newStateMachine configWithTransitions
    currentStep <- newIORef 0
    return $ WorkflowStateMachine stateMachine workflowId steps currentStep

executeStep :: WorkflowStateMachine -> IO (Either String OrderState)
executeStep workflow = do
    currentStepIndex <- readIORef (currentStep workflow)
    if currentStepIndex >= length (steps workflow)
        then return $ Left "工作流已完成"
        else do
            let stepName = steps workflow !! currentStepIndex
            putStrLn $ "执行工作流步骤: " ++ stepName
            
            -- 根据步骤执行相应的状态转换
            let event = case currentStepIndex of
                    0 -> Submit
                    1 -> Approve
                    2 -> Process
                    3 -> Ship
                    _ -> Submit -- 默认
            
            result <- triggerEvent (workflowStateMachine workflow) event
            case result of
                Right _ -> do
                    modifyIORef (currentStep workflow) (+1)
                    return result
                Left error -> return $ Left error

getProgress :: WorkflowStateMachine -> IO Double
getProgress workflow = do
    currentStepIndex <- readIORef (currentStep workflow)
    let totalSteps = length (steps workflow)
    if totalSteps == 0
        then return 0.0
        else return $ fromIntegral currentStepIndex / fromIntegral totalSteps

-- 状态机管理器
data StateMachineManager = StateMachineManager
    { machines :: TVar (M.Map String StateMachine)
    }

newStateMachineManager :: IO StateMachineManager
newStateMachineManager = do
    machines <- newTVarIO M.empty
    return $ StateMachineManager machines

registerMachine :: StateMachineManager -> StateMachine -> IO ()
registerMachine manager machine = do
    atomically $ do
        currentMachines <- readTVar (machines manager)
        writeTVar (machines manager) (M.insert (machineId machine) machine currentMachines)

getMachine :: StateMachineManager -> String -> IO (Maybe StateMachine)
getMachine manager machineId = do
    atomically $ do
        currentMachines <- readTVar (machines manager)
        return $ M.lookup machineId currentMachines

triggerManagerEvent :: StateMachineManager -> String -> OrderEvent -> IO (Either String OrderState)
triggerManagerEvent manager machineId event = do
    maybeMachine <- getMachine manager machineId
    case maybeMachine of
        Just machine -> triggerEvent machine event
        Nothing -> return $ Left "状态机不存在"

getAllMachines :: StateMachineManager -> IO [StateMachine]
getAllMachines manager = do
    atomically $ do
        currentMachines <- readTVar (machines manager)
        return $ M.elems currentMachines

-- 测试函数
testOrderStateMachine :: IO ()
testOrderStateMachine = do
    putStrLn "=== 订单状态机测试 ==="
    
    orderMachine <- newOrderStateMachine "order-001" "customer-001" 99.99
    
    currentState <- getCurrentOrderState orderMachine
    putStrLn $ "初始状态: " ++ show currentState
    
    -- 提交订单
    result1 <- submitOrder orderMachine
    case result1 of
        Right state -> putStrLn $ "提交订单后状态: " ++ show state
        Left error -> putStrLn $ "提交订单失败: " ++ error
    
    -- 审批订单
    result2 <- approveOrder orderMachine
    case result2 of
        Right state -> putStrLn $ "审批订单后状态: " ++ show state
        Left error -> putStrLn $ "审批订单失败: " ++ error
    
    -- 处理订单
    result3 <- processOrder orderMachine
    case result3 of
        Right state -> putStrLn $ "处理订单后状态: " ++ show state
        Left error -> putStrLn $ "处理订单失败: " ++ error
    
    -- 发货
    result4 <- shipOrder orderMachine
    case result4 of
        Right state -> putStrLn $ "发货后状态: " ++ show state
        Left error -> putStrLn $ "发货失败: " ++ error
    
    completed <- isOrderCompleted orderMachine
    putStrLn $ "订单完成: " ++ show completed
    
    history <- getOrderHistory orderMachine
    putStrLn $ "状态历史: " ++ show history

testWorkflowStateMachine :: IO ()
testWorkflowStateMachine = do
    putStrLn "\n=== 工作流状态机测试 ==="
    
    let steps = ["步骤1: 数据验证", "步骤2: 业务处理", "步骤3: 结果输出", "步骤4: 完成"]
    workflowMachine <- newWorkflowStateMachine "workflow-001" steps
    
    progress <- getProgress workflowMachine
    putStrLn $ "工作流进度: " ++ printf "%.2f" (progress * 100) ++ "%"
    
    -- 执行工作流步骤
    mapM_ (\i -> do
        result <- executeStep workflowMachine
        case result of
            Right state -> putStrLn $ "步骤 " ++ show (i + 1) ++ " 执行后状态: " ++ show state
            Left error -> putStrLn $ "步骤 " ++ show (i + 1) ++ " 执行失败: " ++ error
        ) [0..3]

testStateMachineManager :: IO ()
testStateMachineManager = do
    putStrLn "\n=== 状态机管理器测试 ==="
    
    manager <- newStateMachineManager
    
    -- 创建并注册状态机
    config <- newStateMachineConfig Created
    machine <- newStateMachine config
    let machineId = machineId machine
    
    registerMachine manager machine
    
    -- 触发事件
    result <- triggerManagerEvent manager machineId Submit
    case result of
        Right state -> putStrLn $ "管理器触发事件后状态: " ++ show state
        Left error -> putStrLn $ "管理器触发事件失败: " ++ error
    
    -- 获取所有状态机
    allMachines <- getAllMachines manager
    putStrLn $ "管理器中的状态机数量: " ++ show (length allMachines)

main :: IO ()
main = do
    testOrderStateMachine
    testWorkflowStateMachine
    testStateMachineManager
```

## Lean实现思路
```lean
-- 状态枚举
inductive OrderState where
  | Created
  | Pending
  | Processing
  | Shipped
  | Delivered
  | Cancelled

-- 事件枚举
inductive OrderEvent where
  | Submit
  | Approve
  | Process
  | Ship
  | Deliver
  | Cancel

-- 状态机配置
structure StateMachineConfig where
  initialState : OrderState
  finalStates : List OrderState
  transitions : Map (OrderState × OrderEvent) OrderState
  actions : Map (OrderState × OrderEvent) (Sum String Unit)
  guards : Map (OrderState × OrderEvent) Bool

def newStateMachineConfig (initialState : OrderState) : StateMachineConfig :=
  { initialState := initialState
  , finalStates := []
  , transitions := Map.empty
  , actions := Map.empty
  , guards := Map.empty
  }

def addTransition (config : StateMachineConfig) (from : OrderState) (event : OrderEvent) (to : OrderState) : StateMachineConfig :=
  { config with transitions := config.transitions.insert (from, event) to }

def addAction (config : StateMachineConfig) (from : OrderState) (event : OrderEvent) (action : Sum String Unit) : StateMachineConfig :=
  { config with actions := config.actions.insert (from, event) action }

def addGuard (config : StateMachineConfig) (from : OrderState) (event : OrderEvent) (guard : Bool) : StateMachineConfig :=
  { config with guards := config.guards.insert (from, event) guard }

def addFinalState (config : StateMachineConfig) (state : OrderState) : StateMachineConfig :=
  { config with finalStates := state :: config.finalStates }

def canTransition (config : StateMachineConfig) (from : OrderState) (event : OrderEvent) : Bool :=
  -- 检查转换是否存在
  let transitionExists := config.transitions.contains (from, event)
  if not transitionExists
    then false
    else 
      -- 检查守卫条件
      match config.guards.find? (from, event) with
      | some guard => guard
      | none => true

def getNextState (config : StateMachineConfig) (from : OrderState) (event : OrderEvent) : Option OrderState :=
  config.transitions.find? (from, event)

def isFinalState (config : StateMachineConfig) (state : OrderState) : Bool :=
  config.finalStates.contains state

-- 状态机实例
structure StateMachine where
  machineId : String
  config : StateMachineConfig
  currentState : OrderState
  history : List (OrderState × OrderEvent × OrderState)
  context : Map String String

def newStateMachine (config : StateMachineConfig) : StateMachine :=
  { machineId := "machine-" ++ toString (hash config.initialState)
  , config := config
  , currentState := config.initialState
  , history := []
  , context := Map.empty
  }

def triggerEvent (machine : StateMachine) (event : OrderEvent) : Sum String (StateMachine × OrderState) :=
  if not (canTransition machine.config machine.currentState event)
    then Sum.inl ("无法从状态 " ++ toString machine.currentState ++ " 通过事件 " ++ toString event ++ " 转换")
    else 
      -- 执行动作
      let actionResult := match machine.config.actions.find? (machine.currentState, event) with
        | some action => action
        | none => Sum.inr ()
      
      match actionResult with
      | Sum.inl error => Sum.inl error
      | Sum.inr _ => 
          -- 获取下一个状态
          let nextState := getNextState machine.config machine.currentState event
          match nextState with
          | some state => 
              let updatedMachine := { machine with 
                  currentState := state
                , history := (machine.currentState, event, state) :: machine.history
                }
              Sum.inr (updatedMachine, state)
          | none => Sum.inl "转换配置错误"

def getCurrentState (machine : StateMachine) : OrderState :=
  machine.currentState

def getHistory (machine : StateMachine) : List (OrderState × OrderEvent × OrderState) :=
  machine.history

def setContext (machine : StateMachine) (key value : String) : StateMachine :=
  { machine with context := machine.context.insert key value }

def getContext (machine : StateMachine) (key : String) : Option String :=
  machine.context.find? key

def isFinal (machine : StateMachine) : Bool :=
  isFinalState machine.config machine.currentState

-- 订单状态机
structure OrderStateMachine where
  stateMachine : StateMachine
  orderId : String
  customerId : String
  totalAmount : Float

def newOrderStateMachine (orderId customerId : String) (totalAmount : Float) : OrderStateMachine :=
  let config := newStateMachineConfig OrderState.Created
  let configWithTransitions := addTransition (addTransition (addTransition (addTransition (addTransition (addTransition (addTransition config OrderState.Created OrderEvent.Submit OrderState.Pending) OrderState.Pending OrderEvent.Approve OrderState.Processing) OrderState.Processing OrderEvent.Process OrderState.Shipped) OrderState.Shipped OrderEvent.Ship OrderState.Delivered) OrderState.Created OrderEvent.Cancel OrderState.Cancelled) OrderState.Pending OrderEvent.Cancel OrderState.Cancelled) OrderState.Processing OrderEvent.Cancel OrderState.Cancelled
  let configWithActions := addAction (addAction (addAction (addAction (addAction configWithTransitions OrderState.Created OrderEvent.Submit (Sum.inr ())) OrderState.Pending OrderEvent.Approve (Sum.inr ())) OrderState.Processing OrderEvent.Process (Sum.inr ())) OrderState.Shipped OrderEvent.Ship (Sum.inr ())) OrderState.Created OrderEvent.Cancel (Sum.inr ())
  let configWithGuards := addGuard (addGuard configWithActions OrderState.Pending OrderEvent.Approve true) OrderState.Processing OrderEvent.Process true
  let finalConfig := addFinalState (addFinalState configWithGuards OrderState.Delivered) OrderState.Cancelled
  let stateMachine := newStateMachine finalConfig
  
  { stateMachine := stateMachine
  , orderId := orderId
  , customerId := customerId
  , totalAmount := totalAmount
  }

def submitOrder (machine : OrderStateMachine) : Sum String (OrderStateMachine × OrderState) :=
  match triggerEvent machine.stateMachine OrderEvent.Submit with
  | Sum.inr (updatedStateMachine, state) => Sum.inr ({ machine with stateMachine := updatedStateMachine }, state)
  | Sum.inl error => Sum.inl error

def approveOrder (machine : OrderStateMachine) : Sum String (OrderStateMachine × OrderState) :=
  match triggerEvent machine.stateMachine OrderEvent.Approve with
  | Sum.inr (updatedStateMachine, state) => Sum.inr ({ machine with stateMachine := updatedStateMachine }, state)
  | Sum.inl error => Sum.inl error

def processOrder (machine : OrderStateMachine) : Sum String (OrderStateMachine × OrderState) :=
  match triggerEvent machine.stateMachine OrderEvent.Process with
  | Sum.inr (updatedStateMachine, state) => Sum.inr ({ machine with stateMachine := updatedStateMachine }, state)
  | Sum.inl error => Sum.inl error

def shipOrder (machine : OrderStateMachine) : Sum String (OrderStateMachine × OrderState) :=
  match triggerEvent machine.stateMachine OrderEvent.Ship with
  | Sum.inr (updatedStateMachine, state) => Sum.inr ({ machine with stateMachine := updatedStateMachine }, state)
  | Sum.inl error => Sum.inl error

def cancelOrder (machine : OrderStateMachine) : Sum String (OrderStateMachine × OrderState) :=
  match triggerEvent machine.stateMachine OrderEvent.Cancel with
  | Sum.inr (updatedStateMachine, state) => Sum.inr ({ machine with stateMachine := updatedStateMachine }, state)
  | Sum.inl error => Sum.inl error

def getCurrentOrderState (machine : OrderStateMachine) : OrderState :=
  getCurrentState machine.stateMachine

def getOrderHistory (machine : OrderStateMachine) : List (OrderState × OrderEvent × OrderState) :=
  getHistory machine.stateMachine

def isOrderCompleted (machine : OrderStateMachine) : Bool :=
  isFinal machine.stateMachine

-- 工作流状态机
structure WorkflowStateMachine where
  workflowStateMachine : StateMachine
  workflowId : String
  steps : List String
  currentStep : Nat

def newWorkflowStateMachine (workflowId : String) (steps : List String) : WorkflowStateMachine :=
  let config := newStateMachineConfig OrderState.Created
  let configWithTransitions := addTransition (addTransition (addTransition config OrderState.Created OrderEvent.Submit OrderState.Pending) OrderState.Pending OrderEvent.Approve OrderState.Processing) OrderState.Processing OrderEvent.Process OrderState.Shipped
  let stateMachine := newStateMachine configWithTransitions
  
  { workflowStateMachine := stateMachine
  , workflowId := workflowId
  , steps := steps
  , currentStep := 0
  }

def executeStep (workflow : WorkflowStateMachine) : Sum String (WorkflowStateMachine × OrderState) :=
  if workflow.currentStep >= workflow.steps.length
    then Sum.inl "工作流已完成"
    else 
      let stepName := workflow.steps.get! workflow.currentStep
      let event := match workflow.currentStep with
        | 0 => OrderEvent.Submit
        | 1 => OrderEvent.Approve
        | 2 => OrderEvent.Process
        | 3 => OrderEvent.Ship
        | _ => OrderEvent.Submit
      
      match triggerEvent workflow.workflowStateMachine event with
      | Sum.inr (updatedStateMachine, state) => 
          let updatedWorkflow := { workflow with 
              workflowStateMachine := updatedStateMachine
            , currentStep := workflow.currentStep + 1
            }
          Sum.inr (updatedWorkflow, state)
      | Sum.inl error => Sum.inl error

def getProgress (workflow : WorkflowStateMachine) : Float :=
  if workflow.steps.isEmpty
    then 0.0
    else workflow.currentStep.toFloat / workflow.steps.length.toFloat

-- 状态机管理器
structure StateMachineManager where
  machines : Map String StateMachine

def newStateMachineManager : StateMachineManager :=
  { machines := Map.empty }

def registerMachine (manager : StateMachineManager) (machine : StateMachine) : StateMachineManager :=
  { manager with machines := manager.machines.insert machine.machineId machine }

def getMachine (manager : StateMachineManager) (machineId : String) : Option StateMachine :=
  manager.machines.find? machineId

def triggerManagerEvent (manager : StateMachineManager) (machineId : String) (event : OrderEvent) : Sum String (StateMachineManager × OrderState) :=
  match getMachine manager machineId with
  | some machine => 
      match triggerEvent machine event with
      | Sum.inr (updatedMachine, state) => 
          let updatedManager := registerMachine manager updatedMachine
          Sum.inr (updatedManager, state)
      | Sum.inl error => Sum.inl error
  | none => Sum.inl "状态机不存在"

def getAllMachines (manager : StateMachineManager) : List StateMachine :=
  manager.machines.values
```

## 应用场景
- 业务流程管理
- 订单处理系统
- 工作流引擎
- 游戏状态管理

## 最佳实践
- 合理设计状态和事件
- 实现状态持久化
- 添加状态验证
- 监控状态转换
