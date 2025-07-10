# 005 中介者模式 (Mediator Pattern)

## 1. 理论基础

### 1.1 模式定义

中介者模式是一种行为型设计模式，用一个中介对象封装一系列对象交互。中介者使各对象不需要显式地相互引用，从而使其耦合松散，而且可以独立地改变它们之间的交互。

### 1.2 核心概念

- **Mediator（中介者）**: 定义对象交互的接口
- **ConcreteMediator（具体中介者）**: 实现中介者接口，协调各同事对象
- **Colleague（同事）**: 参与交互的对象，持有中介者引用
- **ConcreteColleague（具体同事）**: 实现同事接口，具体业务逻辑
- **Client（客户端）**: 配置中介者和同事对象

### 1.3 设计原则

- **单一职责**: 中介者负责对象间通信，同事只关注自身业务
- **开闭原则**: 支持扩展新的同事和中介者
- **依赖倒置**: 同事依赖中介者抽象

### 1.4 优缺点分析

**优点：**

- 降低对象间耦合
- 集中控制交互逻辑
- 易于扩展和维护
- 简化对象间通信

**缺点：**

- 中介者可能过于复杂
- 影响性能和可测试性
- 过度集中可能导致"上帝对象"

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Mediator a where
  send :: a -> String -> Colleague -> IO ()
  register :: a -> Colleague -> a
  unregister :: a -> Colleague -> a

class Colleague a where
  setMediator :: a -> Mediator -> a
  send :: a -> String -> IO ()
  receive :: a -> String -> IO ()
  getName :: a -> String
```

### 2.2 扩展接口

```haskell
-- 支持广播和组播
class (Mediator a) => BroadcastMediator a where
  broadcast :: a -> String -> IO ()
  multicast :: a -> [Colleague] -> String -> IO ()

-- 支持优先级和过滤
class (Mediator a) => PriorityMediator a where
  sendWithPriority :: a -> String -> Colleague -> Int -> IO ()
  filterColleagues :: a -> (Colleague -> Bool) -> [Colleague]
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 中介者接口
class Mediator a where
  send :: a -> String -> Colleague -> IO ()
  register :: a -> Colleague -> a
  unregister :: a -> Colleague -> a

-- 同事接口
class Colleague a where
  setMediator :: a -> Mediator -> a
  send :: a -> String -> IO ()
  receive :: a -> String -> IO ()
  getName :: a -> String

-- 具体同事A
data ConcreteColleagueA = ConcreteColleagueA {
  name :: String,
  mediator :: Maybe Mediator,
  status :: String
} deriving Show

instance Colleague ConcreteColleagueA where
  setMediator colleague newMediator = 
    colleague { mediator = Just newMediator }
  
  send colleague message = do
    putStrLn $ name colleague ++ " 发送消息: " ++ message
    case mediator colleague of
      Just med -> send med message colleague
      Nothing -> putStrLn $ name colleague ++ " 没有中介者"
  
  receive colleague message = 
    putStrLn $ name colleague ++ " 收到消息: " ++ message
  
  getName = name

-- 具体同事B
data ConcreteColleagueB = ConcreteColleagueB {
  name :: String,
  mediator :: Maybe Mediator,
  priority :: Int
} deriving Show

instance Colleague ConcreteColleagueB where
  setMediator colleague newMediator = 
    colleague { mediator = Just newMediator }
  
  send colleague message = do
    putStrLn $ name colleague ++ " 发送消息: " ++ message ++ " (优先级: " ++ show (priority colleague) ++ ")"
    case mediator colleague of
      Just med -> send med message colleague
      Nothing -> putStrLn $ name colleague ++ " 没有中介者"
  
  receive colleague message = 
    putStrLn $ name colleague ++ " 收到消息: " ++ message
  
  getName = name

-- 具体中介者
data ConcreteMediator = ConcreteMediator {
  colleagues :: [Colleague],
  messageLog :: [String]
} deriving Show

instance Mediator ConcreteMediator where
  send mediator message sender = do
    let filteredColleagues = filter (\c -> getName c /= getName sender) (colleagues mediator)
    mapM_ (\colleague -> receive colleague message) filteredColleagues
    let newLog = messageLog mediator ++ [getName sender ++ ": " ++ message]
    return $ mediator { messageLog = newLog }
  
  register mediator colleague = 
    mediator { colleagues = colleague : colleagues mediator }
  
  unregister mediator targetColleague = 
    mediator { colleagues = filter (\c -> getName c /= getName targetColleague) (colleagues mediator) }

-- 广播中介者
data BroadcastMediator = BroadcastMediator {
  baseMediator :: ConcreteMediator,
  broadcastEnabled :: Bool
} deriving Show

instance Mediator BroadcastMediator where
  send mediator message sender = 
    send (baseMediator mediator) message sender
  
  register mediator colleague = 
    mediator { baseMediator = register (baseMediator mediator) colleague }
  
  unregister mediator colleague = 
    mediator { baseMediator = unregister (baseMediator mediator) colleague }

instance BroadcastMediator BroadcastMediator where
  broadcast mediator message = do
    if broadcastEnabled mediator
    then do
      putStrLn $ "广播消息: " ++ message
      mapM_ (\colleague -> receive colleague message) (colleagues (baseMediator mediator))
    else putStrLn "广播功能已禁用"
  
  multicast mediator message targetColleagues = do
    putStrLn $ "组播消息: " ++ message
    mapM_ (\colleague -> receive colleague message) targetColleagues

-- 优先级中介者
data PriorityMediator = PriorityMediator {
  baseMediator :: ConcreteMediator,
  priorityQueue :: [(Int, Colleague)]
} deriving Show

instance Mediator PriorityMediator where
  send mediator message sender = 
    send (baseMediator mediator) message sender
  
  register mediator colleague = 
    mediator { baseMediator = register (baseMediator mediator) colleague }
  
  unregister mediator colleague = 
    mediator { baseMediator = unregister (baseMediator mediator) colleague }

instance PriorityMediator PriorityMediator where
  sendWithPriority mediator message sender priority = do
    putStrLn $ "发送优先级消息: " ++ message ++ " (优先级: " ++ show priority ++ ")"
    send mediator message sender
  
  filterColleagues mediator predicate = 
    filter predicate (colleagues (baseMediator mediator))

-- 使用示例
main :: IO ()
main = do
  -- 创建中介者
  let mediator = ConcreteMediator [] []
  
  -- 创建同事
  let colleagueA = ConcreteColleagueA "同事A" Nothing "在线"
  let colleagueB = ConcreteColleagueB "同事B" Nothing 1
  
  -- 注册同事到中介者
  let mediator' = register (register mediator colleagueA) colleagueB
  
  -- 设置同事的中介者
  let colleagueA' = setMediator colleagueA mediator'
  let colleagueB' = setMediator colleagueB mediator'
  
  putStrLn "中介者模式示例:"
  
  -- 发送消息
  send colleagueA' "Hello from A"
  send colleagueB' "Hello from B"
  
  -- 广播中介者
  let broadcastMediator = BroadcastMediator mediator' True
  broadcast broadcastMediator "广播消息"
  
  -- 优先级中介者
  let priorityMediator = PriorityMediator mediator' []
  sendWithPriority priorityMediator "优先级消息" colleagueA' 5
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 中介者trait
trait Mediator {
    fn send(&self, message: &str, colleague: &dyn Colleague);
    fn register(&mut self, colleague: Box<dyn Colleague>);
    fn unregister(&mut self, name: &str);
    fn broadcast(&self, message: &str);
    fn multicast(&self, message: &str, names: &[String]);
}

// 同事trait
trait Colleague {
    fn set_mediator(&mut self, mediator: &dyn Mediator);
    fn send(&self, message: &str);
    fn receive(&self, message: &str);
    fn get_name(&self) -> &str;
}

// 具体同事A
#[derive(Debug)]
struct ConcreteColleagueA {
    name: String,
    mediator: Option<&'static dyn Mediator>,
    status: String,
}

impl ConcreteColleagueA {
    fn new(name: String) -> Self {
        ConcreteColleagueA {
            name,
            mediator: None,
            status: "在线".to_string(),
        }
    }
}

impl Colleague for ConcreteColleagueA {
    fn set_mediator(&mut self, mediator: &'static dyn Mediator) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        println!("{} 发送消息: {}", self.name, message);
        if let Some(mediator) = self.mediator {
            mediator.send(message, self);
        } else {
            println!("{} 没有中介者", self.name);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("{} 收到消息: {}", self.name, message);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 具体同事B
#[derive(Debug)]
struct ConcreteColleagueB {
    name: String,
    mediator: Option<&'static dyn Mediator>,
    priority: i32,
}

impl ConcreteColleagueB {
    fn new(name: String, priority: i32) -> Self {
        ConcreteColleagueB {
            name,
            mediator: None,
            priority,
        }
    }
}

impl Colleague for ConcreteColleagueB {
    fn set_mediator(&mut self, mediator: &'static dyn Mediator) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        println!("{} 发送消息: {} (优先级: {})", self.name, message, self.priority);
        if let Some(mediator) = self.mediator {
            mediator.send(message, self);
        } else {
            println!("{} 没有中介者", self.name);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("{} 收到消息: {}", self.name, message);
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 具体中介者
#[derive(Debug)]
struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague>>,
    message_log: Vec<String>,
}

impl ConcreteMediator {
    fn new() -> Self {
        ConcreteMediator {
            colleagues: Vec::new(),
            message_log: Vec::new(),
        }
    }
}

impl Mediator for ConcreteMediator {
    fn send(&self, message: &str, sender: &dyn Colleague) {
        for colleague in &self.colleagues {
            if colleague.get_name() != sender.get_name() {
                colleague.receive(message);
            }
        }
    }
    
    fn register(&mut self, colleague: Box<dyn Colleague>) {
        self.colleagues.push(colleague);
    }
    
    fn unregister(&mut self, name: &str) {
        self.colleagues.retain(|c| c.get_name() != name);
    }
    
    fn broadcast(&self, message: &str) {
        println!("广播消息: {}", message);
        for colleague in &self.colleagues {
            colleague.receive(message);
        }
    }
    
    fn multicast(&self, message: &str, names: &[String]) {
        println!("组播消息: {}", message);
        for colleague in &self.colleagues {
            if names.contains(&colleague.get_name().to_string()) {
                colleague.receive(message);
            }
        }
    }
}

// 广播中介者
#[derive(Debug)]
struct BroadcastMediator {
    base_mediator: ConcreteMediator,
    broadcast_enabled: bool,
}

impl BroadcastMediator {
    fn new() -> Self {
        BroadcastMediator {
            base_mediator: ConcreteMediator::new(),
            broadcast_enabled: true,
        }
    }
}

impl Mediator for BroadcastMediator {
    fn send(&self, message: &str, colleague: &dyn Colleague) {
        self.base_mediator.send(message, colleague);
    }
    
    fn register(&mut self, colleague: Box<dyn Colleague>) {
        self.base_mediator.register(colleague);
    }
    
    fn unregister(&mut self, name: &str) {
        self.base_mediator.unregister(name);
    }
    
    fn broadcast(&self, message: &str) {
        if self.broadcast_enabled {
            self.base_mediator.broadcast(message);
        } else {
            println!("广播功能已禁用");
        }
    }
    
    fn multicast(&self, message: &str, names: &[String]) {
        self.base_mediator.multicast(message, names);
    }
}

// 优先级中介者
#[derive(Debug)]
struct PriorityMediator {
    base_mediator: ConcreteMediator,
    priority_queue: Vec<(i32, Box<dyn Colleague>)>,
}

impl PriorityMediator {
    fn new() -> Self {
        PriorityMediator {
            base_mediator: ConcreteMediator::new(),
            priority_queue: Vec::new(),
        }
    }
    
    fn send_with_priority(&self, message: &str, colleague: &dyn Colleague, priority: i32) {
        println!("发送优先级消息: {} (优先级: {})", message, priority);
        self.base_mediator.send(message, colleague);
    }
    
    fn filter_colleagues<F>(&self, predicate: F) -> Vec<&dyn Colleague>
    where
        F: Fn(&dyn Colleague) -> bool,
    {
        self.base_mediator.colleagues.iter()
            .filter(|c| predicate(c.as_ref()))
            .map(|c| c.as_ref())
            .collect()
    }
}

impl Mediator for PriorityMediator {
    fn send(&self, message: &str, colleague: &dyn Colleague) {
        self.base_mediator.send(message, colleague);
    }
    
    fn register(&mut self, colleague: Box<dyn Colleague>) {
        self.base_mediator.register(colleague);
    }
    
    fn unregister(&mut self, name: &str) {
        self.base_mediator.unregister(name);
    }
    
    fn broadcast(&self, message: &str) {
        self.base_mediator.broadcast(message);
    }
    
    fn multicast(&self, message: &str, names: &[String]) {
        self.base_mediator.multicast(message, names);
    }
}

// 使用示例
fn main() {
    let mut mediator = ConcreteMediator::new();
    let mut colleague_a = ConcreteColleagueA::new("同事A".to_string());
    let mut colleague_b = ConcreteColleagueB::new("同事B".to_string(), 1);
    
    // 设置中介者
    colleague_a.set_mediator(&mediator);
    colleague_b.set_mediator(&mediator);
    
    // 注册同事到中介者
    mediator.register(Box::new(colleague_a));
    mediator.register(Box::new(colleague_b));
    
    println!("中介者模式示例:");
    
    // 发送消息
    colleague_a.send("Hello from A");
    colleague_b.send("Hello from B");
    
    // 广播消息
    mediator.broadcast("广播消息");
    
    // 组播消息
    mediator.multicast("组播消息", &["同事A".to_string()]);
    
    // 优先级中介者
    let mut priority_mediator = PriorityMediator::new();
    let mut priority_colleague = ConcreteColleagueA::new("优先级同事".to_string());
    priority_colleague.set_mediator(&priority_mediator);
    priority_mediator.register(Box::new(priority_colleague));
    priority_mediator.send_with_priority("优先级消息", &priority_colleague, 5);
}
```

### 3.3 Lean实现

```lean
-- 中介者类型类
class Mediator (α : Type) where
  send : α → String → Colleague → IO Unit
  register : α → Colleague → α
  unregister : α → Colleague → α

-- 同事类型类
class Colleague (α : Type) where
  setMediator : α → Mediator → α
  send : α → String → IO Unit
  receive : α → String → IO Unit
  getName : α → String

-- 具体同事A
structure ConcreteColleagueA where
  name : String
  mediator : Option Mediator
  status : String

def newColleagueA (name : String) : ConcreteColleagueA := {
  name := name,
  mediator := none,
  status := "在线"
}

instance : Colleague ConcreteColleagueA where
  setMediator colleague newMediator := {
    colleague with mediator := some newMediator
  }
  
  send colleague message := do
    IO.println (colleague.name ++ " 发送消息: " ++ message)
    match colleague.mediator with
    | some med => send med message colleague
    | none => IO.println (colleague.name ++ " 没有中介者")
  
  receive colleague message := 
    IO.println (colleague.name ++ " 收到消息: " ++ message)
  
  getName colleague := colleague.name

-- 具体同事B
structure ConcreteColleagueB where
  name : String
  mediator : Option Mediator
  priority : Nat

def newColleagueB (name : String) (priority : Nat) : ConcreteColleagueB := {
  name := name,
  mediator := none,
  priority := priority
}

instance : Colleague ConcreteColleagueB where
  setMediator colleague newMediator := {
    colleague with mediator := some newMediator
  }
  
  send colleague message := do
    IO.println (colleague.name ++ " 发送消息: " ++ message ++ " (优先级: " ++ toString colleague.priority ++ ")")
    match colleague.mediator with
    | some med => send med message colleague
    | none => IO.println (colleague.name ++ " 没有中介者")
  
  receive colleague message := 
    IO.println (colleague.name ++ " 收到消息: " ++ message)
  
  getName colleague := colleague.name

-- 具体中介者
structure ConcreteMediator where
  colleagues : List Colleague
  messageLog : List String

def newMediator : ConcreteMediator := {
  colleagues := [],
  messageLog := []
}

instance : Mediator ConcreteMediator where
  send mediator message sender := do
    let filteredColleagues := mediator.colleagues.filter (fun c => getName c ≠ getName sender)
    filteredColleagues.forM (fun colleague => receive colleague message)
    let newLog := mediator.messageLog ++ [getName sender ++ ": " ++ message]
    return { mediator with messageLog := newLog }
  
  register mediator colleague := {
    mediator with colleagues := colleague :: mediator.colleagues
  }
  
  unregister mediator targetColleague := {
    mediator with colleagues := mediator.colleagues.filter (fun c => getName c ≠ getName targetColleague)
  }

-- 广播中介者
structure BroadcastMediator where
  baseMediator : ConcreteMediator
  broadcastEnabled : Bool

def newBroadcastMediator : BroadcastMediator := {
  baseMediator := newMediator,
  broadcastEnabled := true
}

instance : Mediator BroadcastMediator where
  send mediator message sender := 
    send mediator.baseMediator message sender
  
  register mediator colleague := {
    mediator with baseMediator := register mediator.baseMediator colleague
  }
  
  unregister mediator colleague := {
    mediator with baseMediator := unregister mediator.baseMediator colleague
  }

def broadcast (mediator : BroadcastMediator) (message : String) : IO Unit := do
  if mediator.broadcastEnabled
  then do
    IO.println ("广播消息: " ++ message)
    mediator.baseMediator.colleagues.forM (fun colleague => receive colleague message)
  else IO.println "广播功能已禁用"

def multicast (mediator : BroadcastMediator) (message : String) (targetColleagues : List Colleague) : IO Unit := do
  IO.println ("组播消息: " ++ message)
  targetColleagues.forM (fun colleague => receive colleague message)

-- 使用示例
def main : IO Unit := do
  let mediator := newMediator
  let colleagueA := newColleagueA "同事A"
  let colleagueB := newColleagueB "同事B" 1
  
  let colleagueA' := setMediator colleagueA mediator
  let colleagueB' := setMediator colleagueB mediator
  
  let mediator' := register (register mediator colleagueA') colleagueB'
  
  IO.println "中介者模式示例:"
  
  send colleagueA' "Hello from A"
  send colleagueB' "Hello from B"
  
  let broadcastMediator := newBroadcastMediator
  broadcast broadcastMediator "广播消息"
```

## 4. 工程实践

### 4.1 设计考虑

- **解耦通信**: 避免同事间直接引用
- **扩展性**: 支持动态注册/注销同事
- **性能优化**: 避免中介者成为瓶颈
- **错误处理**: 处理消息丢失、同事失效等

### 4.2 实现模式

```haskell
-- 带缓存的中介者
data CachedMediator = CachedMediator {
  mediator :: Mediator,
  cache :: MVar (Map String String)
}

-- 异步中介者
data AsyncMediator = AsyncMediator {
  mediator :: Mediator,
  executor :: ThreadPool
}

-- 带监控的中介者
data MonitoredMediator = MonitoredMediator {
  mediator :: Mediator,
  metrics :: MVar MediatorMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data MediatorError = 
  ColleagueNotFound String
  | MessageDeliveryFailed String
  | MediatorOverload

-- 安全发送
safeSend :: Mediator a => a -> String -> Colleague -> IO (Either MediatorError ())
safeSend mediator message colleague = 
  try (send mediator message colleague) >>= \case
    Left e -> return $ Left $ MessageDeliveryFailed (show e)
    Right _ -> return $ Right ()
```

## 5. 性能优化

### 5.1 缓存与并发

- **消息缓存**: 缓存未送达消息
- **并发处理**: 支持多线程消息分发
- **资源管理**: 动态回收失效同事

### 5.2 负载均衡

```haskell
-- 负载均衡中介者
data LoadBalancingMediator = LoadBalancingMediator {
  mediator :: Mediator,
  strategy :: LoadBalancingStrategy
}

data LoadBalancingStrategy = RoundRobin | LeastConnections | RandomChoice
```

## 6. 应用场景

### 6.1 GUI组件通信

```haskell
-- 窗口控件中介者
data WidgetMediator = WidgetMediator {
  widgets :: [Widget],
  eventBus :: EventBus
}

-- 控件事件分发
handleEvent :: WidgetMediator -> WidgetEvent -> IO ()
handleEvent mediator event = ...
```

### 6.2 消息系统

```haskell
-- 消息中介者
data MessageMediator = MessageMediator {
  subscribers :: [Subscriber],
  messageQueue :: MessageQueue
}

-- 消息分发
publishMessage :: MessageMediator -> Message -> IO ()
publishMessage mediator message = ...
```

### 6.3 协作平台

```haskell
-- 协作中介者
data CollaborationMediator = CollaborationMediator {
  users :: [User],
  sessionManager :: SessionManager
}

-- 协作消息
sendCollaborationMessage :: CollaborationMediator -> User -> String -> IO ()
sendCollaborationMessage mediator user msg = ...
```

### 6.4 微服务通信

```haskell
-- 微服务中介者
data MicroserviceMediator = MicroserviceMediator {
  services :: [Service],
  registry :: ServiceRegistry
}

-- 服务间消息
sendServiceMessage :: MicroserviceMediator -> Service -> String -> IO ()
sendServiceMessage mediator service msg = ...
```

## 7. 最佳实践

### 7.1 设计原则

- **保持中介者简洁**: 避免"上帝对象"
- **合理拆分中介者**: 按业务领域拆分多个中介者
- **支持动态扩展**: 支持同事和中介者的动态注册
- **性能考虑**: 避免同步瓶颈

### 7.2 实现建议

```haskell
-- 中介者工厂
class MediatorFactory a where
  createMediator :: String -> Maybe a
  listMediators :: [String]
  validateMediator :: a -> Bool

-- 中介者注册表
data MediatorRegistry = MediatorRegistry {
  mediators :: Map String (forall a. Mediator a => a),
  metadata :: Map String String
}

-- 线程安全中介者管理器
data ThreadSafeMediatorManager = ThreadSafeMediatorManager {
  manager :: MVar MediatorManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 中介者测试
testMediator :: Mediator a => a -> [Colleague] -> Bool
testMediator mediator colleagues = 
  all (\c -> testColleague c mediator) colleagues

-- 性能测试
benchmarkMediator :: Mediator a => a -> [Colleague] -> IO Double
benchmarkMediator mediator colleagues = do
  start <- getCurrentTime
  replicateM_ 1000 $ mapM_ (\c -> send mediator "test" c) colleagues
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的中介者类型
- **序列化**: 支持中介者和同事的序列化
- **版本控制**: 支持中介者接口的版本管理
- **分布式**: 支持跨网络的中介者通信

## 8. 总结

中介者模式是解耦对象通信、简化交互逻辑的强大工具，通过集中管理对象间的消息分发和协调，提升了系统的可维护性和扩展性。在实现时需注意中介者的复杂度、性能优化和扩展性。该模式在GUI、消息系统、协作平台、微服务等场景中有广泛应用。
