# 002 命令模式 (Command Pattern)

## 1. 理论基础

### 1.1 模式定义

命令模式是一种行为型设计模式，将请求封装成对象，从而可以用不同的请求对客户进行参数化，对请求排队或记录请求日志，以及支持可撤销的操作。

### 1.2 核心概念

- **Command（命令）**: 声明执行操作的接口
- **ConcreteCommand（具体命令）**: 将一个接收者对象绑定于一个动作，调用接收者相应的操作
- **Client（客户端）**: 创建一个具体命令对象并设定它的接收者
- **Invoker（调用者）**: 要求该命令执行这个请求
- **Receiver（接收者）**: 知道如何实施与执行一个请求相关的操作

### 1.3 设计原则

- **单一职责**: 每个命令只负责一个操作
- **开闭原则**: 可以轻松添加新的命令类型
- **依赖倒置**: 客户端依赖于抽象命令接口

### 1.4 优缺点分析

**优点:**

- 将调用操作的对象与知道如何实现该操作的对象解耦
- 可以容易地添加新的命令
- 可以容易地组合命令
- 支持撤销和重做操作

**缺点:**

- 可能导致类的数量增加
- 命令对象可能变得复杂
- 撤销操作可能难以实现

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Command a where
  execute :: a -> IO ()
  undo :: a -> IO ()
  canUndo :: a -> Bool
  getDescription :: a -> String

-- 接收者接口
class Receiver a where
  performAction :: a -> String -> IO ()
  undoAction :: a -> String -> IO ()
  getState :: a -> String
```

### 2.2 扩展接口

```haskell
-- 支持参数的命令接口
class (Command a) => ParameterizedCommand a where
  setParameters :: a -> [String] -> a
  getParameters :: a -> [String]
  
-- 支持宏的命令接口
class (Command a) => MacroCommand a where
  addCommand :: a -> a -> a
  removeCommand :: a -> a -> Maybe a
  getCommands :: a -> [a]
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 命令接口
class Command a where
  execute :: a -> IO ()
  undo :: a -> IO ()
  canUndo :: a -> Bool
  getDescription :: a -> String

-- 接收者
data Receiver = Receiver {
  name :: String,
  state :: String
} deriving Show

instance Receiver Receiver where
  performAction receiver action = do
    putStrLn $ name receiver ++ " 执行操作: " ++ action
    return $ receiver { state = action }
  undoAction receiver action = do
    putStrLn $ name receiver ++ " 撤销操作: " ++ action
    return $ receiver { state = "撤销后的状态" }
  getState = state

-- 具体命令
data ConcreteCommand = ConcreteCommand {
  receiver :: Receiver,
  action :: String,
  description :: String
} deriving Show

instance Command ConcreteCommand where
  execute command = do
    putStrLn $ "执行命令: " ++ description command
    performAction (receiver command) (action command)
  
  undo command = do
    putStrLn $ "撤销命令: " ++ description command
    undoAction (receiver command) (action command)
  
  canUndo _ = True
  getDescription = description

-- 宏命令
data MacroCommand = MacroCommand {
  commands :: [ConcreteCommand],
  macroDescription :: String
} deriving Show

instance Command MacroCommand where
  execute macro = do
    putStrLn $ "执行宏命令: " ++ macroDescription macro
    mapM_ execute (commands macro)
  
  undo macro = do
    putStrLn $ "撤销宏命令: " ++ macroDescription macro
    mapM_ undo (reverse $ commands macro)
  
  canUndo _ = True
  getDescription = macroDescription

-- 调用者
data Invoker = Invoker {
  commands :: [ConcreteCommand],
  history :: [ConcreteCommand]
} deriving Show

addCommand :: Invoker -> ConcreteCommand -> Invoker
addCommand invoker command = 
  invoker { commands = command : commands invoker }

executeCommand :: Invoker -> IO Invoker
executeCommand invoker = case commands invoker of
  [] -> return invoker
  (cmd:rest) -> do
    execute cmd
    return $ invoker { 
      commands = rest,
      history = cmd : history invoker 
    }

undoLastCommand :: Invoker -> IO Invoker
undoLastCommand invoker = case history invoker of
  [] -> return invoker
  (cmd:rest) -> do
    undo cmd
    return $ invoker { 
      commands = cmd : commands invoker,
      history = rest 
    }

-- 命令工厂
data CommandFactory = CommandFactory {
  receivers :: [Receiver],
  commandTypes :: [String]
}

createCommand :: CommandFactory -> String -> String -> Maybe ConcreteCommand
createCommand factory receiverName actionName = 
  let matchingReceivers = filter (\r -> name r == receiverName) (receivers factory)
  in case matchingReceivers of
    (receiver:_) -> Just $ ConcreteCommand {
      receiver = receiver,
      action = actionName,
      description = receiverName ++ " -> " ++ actionName
    }
    [] -> Nothing

-- 使用示例
main :: IO ()
main = do
  let receiver1 = Receiver "文件系统" "空闲"
  let receiver2 = Receiver "数据库" "连接"
  
  let factory = CommandFactory [receiver1, receiver2] ["创建", "删除", "修改"]
  
  let command1 = ConcreteCommand receiver1 "创建文件" "创建新文件"
  let command2 = ConcreteCommand receiver2 "插入数据" "向数据库插入数据"
  
  let macroCommand = MacroCommand [command1, command2] "文件操作宏"
  
  let invoker = Invoker [] []
  let invoker1 = addCommand invoker command1
  let invoker2 = addCommand invoker1 command2
  
  putStrLn "命令模式示例:"
  
  -- 执行单个命令
  putStrLn "\n执行单个命令:"
  execute command1
  
  -- 执行宏命令
  putStrLn "\n执行宏命令:"
  execute macroCommand
  
  -- 使用调用者
  putStrLn "\n使用调用者:"
  invoker3 <- executeCommand invoker2
  invoker4 <- executeCommand invoker3
  putStrLn "撤销最后一个命令:"
  undoLastCommand invoker4
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 命令trait
trait Command {
    fn execute(&self);
    fn undo(&self);
    fn can_undo(&self) -> bool;
    fn get_description(&self) -> String;
}

// 接收者
#[derive(Debug, Clone)]
struct Receiver {
    name: String,
    state: String,
}

impl Receiver {
    fn new(name: String) -> Self {
        Receiver {
            name,
            state: "空闲".to_string(),
        }
    }
    
    fn perform_action(&mut self, action: &str) {
        println!("{} 执行操作: {}", self.name, action);
        self.state = action.to_string();
    }
    
    fn undo_action(&mut self, action: &str) {
        println!("{} 撤销操作: {}", self.name, action);
        self.state = "撤销后的状态".to_string();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

// 具体命令
#[derive(Debug)]
struct ConcreteCommand {
    receiver: Receiver,
    action: String,
    description: String,
}

impl ConcreteCommand {
    fn new(receiver: Receiver, action: String, description: String) -> Self {
        ConcreteCommand {
            receiver,
            action,
            description,
        }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) {
        println!("执行命令: {}", self.description);
        let mut receiver = self.receiver.clone();
        receiver.perform_action(&self.action);
    }
    
    fn undo(&self) {
        println!("撤销命令: {}", self.description);
        let mut receiver = self.receiver.clone();
        receiver.undo_action(&self.action);
    }
    
    fn can_undo(&self) -> bool {
        true
    }
    
    fn get_description(&self) -> String {
        self.description.clone()
    }
}

// 宏命令
#[derive(Debug)]
struct MacroCommand {
    commands: Vec<Box<dyn Command>>,
    macro_description: String,
}

impl MacroCommand {
    fn new(description: String) -> Self {
        MacroCommand {
            commands: Vec::new(),
            macro_description: description,
        }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
}

impl Command for MacroCommand {
    fn execute(&self) {
        println!("执行宏命令: {}", self.macro_description);
        for command in &self.commands {
            command.execute();
        }
    }
    
    fn undo(&self) {
        println!("撤销宏命令: {}", self.macro_description);
        for command in self.commands.iter().rev() {
            command.undo();
        }
    }
    
    fn can_undo(&self) -> bool {
        true
    }
    
    fn get_description(&self) -> String {
        self.macro_description.clone()
    }
}

// 调用者
#[derive(Debug)]
struct Invoker {
    commands: Vec<Box<dyn Command>>,
    history: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Invoker {
            commands: Vec::new(),
            history: Vec::new(),
        }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
    
    fn execute_all(&mut self) {
        for command in &self.commands {
            command.execute();
            // 这里需要克隆命令到历史记录，实际实现会更复杂
        }
    }
    
    fn execute_next(&mut self) -> Option<()> {
        if let Some(command) = self.commands.pop() {
            command.execute();
            self.history.push(command);
            Some(())
        } else {
            None
        }
    }
    
    fn undo_last(&mut self) -> Option<()> {
        if let Some(command) = self.history.pop() {
            command.undo();
            self.commands.push(command);
            Some(())
        } else {
            None
        }
    }
}

// 命令工厂
struct CommandFactory {
    receivers: HashMap<String, Receiver>,
}

impl CommandFactory {
    fn new() -> Self {
        let mut receivers = HashMap::new();
        receivers.insert("文件系统".to_string(), Receiver::new("文件系统".to_string()));
        receivers.insert("数据库".to_string(), Receiver::new("数据库".to_string()));
        
        CommandFactory { receivers }
    }
    
    fn create_command(&self, receiver_name: &str, action: &str, description: &str) -> Option<ConcreteCommand> {
        if let Some(receiver) = self.receivers.get(receiver_name) {
            Some(ConcreteCommand::new(
                receiver.clone(),
                action.to_string(),
                description.to_string(),
            ))
        } else {
            None
        }
    }
}

// 使用示例
fn main() {
    let factory = CommandFactory::new();
    
    let command1 = factory.create_command("文件系统", "创建文件", "创建新文件").unwrap();
    let command2 = factory.create_command("数据库", "插入数据", "向数据库插入数据").unwrap();
    
    let mut macro_command = MacroCommand::new("文件操作宏".to_string());
    macro_command.add_command(Box::new(command1.clone()));
    macro_command.add_command(Box::new(command2.clone()));
    
    let mut invoker = Invoker::new();
    invoker.add_command(Box::new(command1));
    invoker.add_command(Box::new(command2));
    
    println!("命令模式示例:");
    
    // 执行单个命令
    println!("\n执行单个命令:");
    command1.execute();
    
    // 执行宏命令
    println!("\n执行宏命令:");
    macro_command.execute();
    
    // 使用调用者
    println!("\n使用调用者:");
    invoker.execute_next();
    invoker.execute_next();
    println!("撤销最后一个命令:");
    invoker.undo_last();
}
```

### 3.3 Lean实现

```lean
-- 命令类型
inductive Command where
  | ConcreteCommand : String → String → String → Command
  | MacroCommand : String → List Command → Command

-- 接收者类型
structure Receiver where
  name : String
  state : String

-- 执行命令
def execute : Command → IO Unit
  | Command.ConcreteCommand receiver action description => do
    IO.println s!"执行命令: {description}"
    IO.println s!"{receiver} 执行操作: {action}"
  | Command.MacroCommand description commands => do
    IO.println s!"执行宏命令: {description}"
    commands.forM execute

-- 撤销命令
def undo : Command → IO Unit
  | Command.ConcreteCommand receiver action description => do
    IO.println s!"撤销命令: {description}"
    IO.println s!"{receiver} 撤销操作: {action}"
  | Command.MacroCommand description commands => do
    IO.println s!"撤销宏命令: {description}"
    commands.reverse.forM undo

-- 获取描述
def getDescription : Command → String
  | Command.ConcreteCommand _ _ description => description
  | Command.MacroCommand description _ => description

-- 检查是否可以撤销
def canUndo : Command → Bool
  | _ => true

-- 调用者类型
structure Invoker where
  commands : List Command
  history : List Command

-- 添加命令
def addCommand (invoker : Invoker) (command : Command) : Invoker :=
  { invoker with commands := command :: invoker.commands }

-- 执行下一个命令
def executeNext (invoker : Invoker) : IO Invoker := do
  match invoker.commands with
  | [] => return invoker
  | command :: rest => do
    execute command
    return { 
      commands := rest,
      history := command :: invoker.history 
    }

-- 撤销最后一个命令
def undoLast (invoker : Invoker) : IO Invoker := do
  match invoker.history with
  | [] => return invoker
  | command :: rest => do
    undo command
    return { 
      commands := command :: invoker.commands,
      history := rest 
    }

-- 使用示例
def main : IO Unit := do
  let command1 := Command.ConcreteCommand "文件系统" "创建文件" "创建新文件"
  let command2 := Command.ConcreteCommand "数据库" "插入数据" "向数据库插入数据"
  let macroCommand := Command.MacroCommand "文件操作宏" [command1, command2]
  
  let invoker := Invoker.mk [] []
  let invoker1 := addCommand invoker command1
  let invoker2 := addCommand invoker1 command2
  
  IO.println "命令模式示例:"
  
  -- 执行单个命令
  IO.println "\n执行单个命令:"
  execute command1
  
  -- 执行宏命令
  IO.println "\n执行宏命令:"
  execute macroCommand
  
  -- 使用调用者
  IO.println "\n使用调用者:"
  invoker3 ← executeNext invoker2
  invoker4 ← executeNext invoker3
  IO.println "撤销最后一个命令:"
  undoLast invoker4
```

## 4. 工程实践

### 4.1 设计考虑

- **命令对象轻量化**: 避免命令对象过于复杂
- **状态管理**: 正确处理撤销操作的状态
- **内存管理**: 合理管理命令历史记录
- **性能优化**: 避免不必要的对象创建

### 4.2 实现模式

```haskell
-- 带状态的命令
data StatefulCommand a = StatefulCommand {
  command :: a,
  state :: MVar String,
  history :: MVar [String]
}

-- 异步命令
data AsyncCommand a = AsyncCommand {
  command :: a,
  executor :: ThreadPool
}

-- 带缓存的命令
data CachedCommand a = CachedCommand {
  command :: a,
  cache :: MVar (Map String String)
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data CommandError = 
  CommandExecutionFailed String
  | UndoNotSupported String
  | InvalidCommand String

-- 安全执行
safeExecute :: Command a => a -> IO (Either CommandError ())
safeExecute command = 
  try (execute command) >>= \case
    Left e -> return $ Left $ CommandExecutionFailed (show e)
    Right _ -> return $ Right ()
```

## 5. 性能优化

### 5.1 缓存策略

- **命令结果缓存**: 缓存相同命令的执行结果
- **撤销状态缓存**: 缓存撤销操作的状态
- **命令对象池**: 使用对象池减少内存分配

### 5.2 异步执行

```haskell
-- 异步命令执行器
data AsyncCommandExecutor = AsyncCommandExecutor {
  threadPool :: ThreadPool,
  queue :: MVar [Command]
}

executeAsync :: AsyncCommandExecutor -> Command -> IO ThreadId
executeAsync executor command = 
  forkIO $ do
    execute command
    return ()
```

### 5.3 命令批处理

```haskell
-- 批处理命令
data BatchCommand a = BatchCommand {
  commands :: [a],
  batchSize :: Int
}

executeBatch :: Command a => BatchCommand a -> IO ()
executeBatch (BatchCommand commands batchSize) = 
  forM_ (chunksOf batchSize commands) $ \batch ->
    mapConcurrently execute batch
```

## 6. 应用场景

### 6.1 GUI按钮事件处理

```haskell
-- GUI命令
data GUICommand = GUICommand {
  action :: String,
  parameters :: Map String String
}

-- GUI事件处理器
data GUIEventHandler = GUIEventHandler {
  commands :: Map String GUICommand,
  invoker :: Invoker
}

handleGUIEvent :: GUIEventHandler -> String -> IO ()
handleGUIEventHandler handler eventType = 
  case Map.lookup eventType (commands handler) of
    Just command -> execute command
    Nothing -> putStrLn $ "未知事件类型: " ++ eventType
```

### 6.2 宏录制和回放

```haskell
-- 宏录制器
data MacroRecorder = MacroRecorder {
  isRecording :: MVar Bool,
  recordedCommands :: MVar [Command],
  macroName :: String
}

startRecording :: MacroRecorder -> IO ()
startRecording recorder = 
  modifyMVar_ (isRecording recorder) $ return . const True

stopRecording :: MacroRecorder -> IO MacroCommand
stopRecording recorder = do
  modifyMVar_ (isRecording recorder) $ return . const False
  commands <- readMVar (recordedCommands recorder)
  return $ MacroCommand (macroName recorder) commands
```

### 6.3 事务处理

```haskell
-- 事务命令
data TransactionCommand = TransactionCommand {
  commands :: [Command],
  rollbackCommands :: [Command]
}

executeTransaction :: TransactionCommand -> IO (Either String ())
executeTransaction transaction = do
  results <- mapM safeExecute (commands transaction)
  case sequence results of
    Left error -> do
      mapM_ undo (reverse $ commands transaction)
      return $ Left error
    Right _ -> return $ Right ()
```

### 6.4 撤销重做功能

```haskell
-- 撤销重做管理器
data UndoRedoManager = UndoRedoManager {
  undoStack :: MVar [Command],
  redoStack :: MVar [Command],
  maxStackSize :: Int
}

undo :: UndoRedoManager -> IO (Maybe Command)
undo manager = do
  stack <- takeMVar (undoStack manager)
  case stack of
    (cmd:rest) -> do
      putMVar (undoStack manager) rest
      redoStack' <- takeMVar (redoStack manager)
      putMVar (redoStack manager) (cmd:redoStack')
      undo cmd
      return $ Just cmd
    [] -> do
      putMVar (undoStack manager) []
      return Nothing

redo :: UndoRedoManager -> IO (Maybe Command)
redo manager = do
  stack <- takeMVar (redoStack manager)
  case stack of
    (cmd:rest) -> do
      putMVar (redoStack manager) rest
      undoStack' <- takeMVar (undoStack manager)
      putMVar (undoStack manager) (cmd:undoStack')
      execute cmd
      return $ Just cmd
    [] -> do
      putMVar (redoStack manager) []
      return Nothing
```

## 7. 最佳实践

### 7.1 设计原则

- **命令对象轻量化**: 避免命令对象过于复杂
- **支持撤销操作**: 为每个命令提供撤销功能
- **命令组合**: 支持命令的组合和批处理
- **状态管理**: 正确处理命令执行的状态

### 7.2 实现建议

```haskell
-- 命令工厂
class CommandFactory a where
  createCommand :: String -> [String] -> Maybe a
  listCommandTypes :: [String]
  validateCommand :: a -> Bool

-- 命令注册表
data CommandRegistry = CommandRegistry {
  commands :: Map String (forall a. Command a => a),
  metadata :: Map String String
}

-- 线程安全命令执行器
data ThreadSafeCommandExecutor = ThreadSafeCommandExecutor {
  executor :: MVar CommandExecutor,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 命令测试
testCommand :: Command a => a -> Bool
testCommand command = 
  let description = getDescription command
      canUndo = canUndo command
  in not (null description) && canUndo

-- 性能测试
benchmarkCommand :: Command a => a -> IO Double
benchmarkCommand command = do
  start <- getCurrentTime
  replicateM_ 1000 $ execute command
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的命令类型
- **序列化**: 支持命令的序列化和反序列化
- **版本控制**: 支持命令的版本管理
- **分布式**: 支持跨网络的命令执行

## 8. 总结

命令模式是封装请求的强大工具，通过将请求封装为对象提供了灵活的参数化、排队、日志记录和撤销功能。在实现时需要注意命令对象的轻量化、状态管理和性能优化。该模式在GUI事件处理、宏录制、事务处理、撤销重做等场景中都有广泛应用。
