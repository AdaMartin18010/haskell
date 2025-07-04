# 002 命令模式

## 1. 理论基础

命令模式是一种行为型设计模式，将请求封装成对象，从而可以用不同的请求对客户进行参数化。支持撤销操作、宏命令、事务处理等。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Command a where
  execute :: a -> IO ()
  undo :: a -> IO ()

-- 接收者
data Receiver = Receiver String

-- 具体命令
data ConcreteCommand = ConcreteCommand Receiver String
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 命令接口
class Command a where
  execute :: a -> IO ()
  undo :: a -> IO ()

-- 接收者
data Receiver = Receiver String deriving Show

-- 具体命令
data ConcreteCommand = ConcreteCommand Receiver String deriving Show

instance Command ConcreteCommand where
  execute (ConcreteCommand (Receiver name) action) = 
    putStrLn $ "Executing " ++ action ++ " on " ++ name
  undo (ConcreteCommand (Receiver name) action) = 
    putStrLn $ "Undoing " ++ action ++ " on " ++ name

-- 调用者
data Invoker = Invoker [ConcreteCommand] deriving Show

-- 调用者操作
addCommand :: Invoker -> ConcreteCommand -> Invoker
addCommand (Invoker commands) command = Invoker (command : commands)

executeAll :: Invoker -> IO ()
executeAll (Invoker commands) = mapM_ execute commands

-- 使用示例
main :: IO ()
main = do
  let receiver = Receiver "File"
  let command1 = ConcreteCommand receiver "Open"
  let command2 = ConcreteCommand receiver "Save"
  let invoker = Invoker []
  let invoker' = addCommand invoker command1
  let invoker'' = addCommand invoker' command2
  executeAll invoker''
```

### Rust实现

```rust
// 命令trait
trait Command {
    fn execute(&self);
    fn undo(&self);
}

// 接收者
struct Receiver {
    name: String,
}

impl Receiver {
    fn new(name: &str) -> Self {
        Receiver {
            name: name.to_string(),
        }
    }
    
    fn action(&self, action: &str) {
        println!("Executing {} on {}", action, self.name);
    }
}

// 具体命令
struct ConcreteCommand {
    receiver: Receiver,
    action: String,
}

impl ConcreteCommand {
    fn new(receiver: Receiver, action: &str) -> Self {
        ConcreteCommand {
            receiver,
            action: action.to_string(),
        }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) {
        self.receiver.action(&self.action);
    }
    
    fn undo(&self) {
        println!("Undoing {} on {}", self.action, self.receiver.name);
    }
}

// 调用者
struct Invoker {
    commands: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Invoker { commands: Vec::new() }
    }
    
    fn add_command(&mut self, command: Box<dyn Command>) {
        self.commands.push(command);
    }
    
    fn execute_all(&self) {
        for command in &self.commands {
            command.execute();
        }
    }
}
```

### Lean实现

```lean
-- 命令类型
def Command := String → IO Unit

-- 接收者
def Receiver := String

-- 具体命令
def concreteCommand (receiver : Receiver) (action : String) : Command :=
  fun _ => IO.println ("Executing " ++ action ++ " on " ++ receiver)

-- 命令执行
def execute (cmd : Command) : IO Unit :=
  cmd ""

-- 命令撤销
def undo (cmd : Command) : IO Unit :=
  IO.println "Undoing command"

-- 命令模式正确性定理
theorem command_encapsulation :
  ∀ cmd : Command, execute cmd ≠ undo cmd :=
  by simp [execute, undo]
```

## 4. 工程实践

- 撤销/重做功能
- 宏命令
- 事务处理
- 日志记录

## 5. 性能优化

- 命令缓存
- 批量执行
- 异步处理
- 内存管理

## 6. 应用场景

- 文本编辑器
- 图形界面
- 游戏控制
- 数据库事务

## 7. 最佳实践

- 保持命令简单
- 实现撤销功能
- 考虑内存使用
- 支持复合命令
