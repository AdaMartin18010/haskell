# 命令模式（Command Pattern）

## 概述

命令模式是一种行为型设计模式，将请求封装成对象，从而可以用不同的请求对客户进行参数化，对请求排队或记录请求日志，以及支持可撤销的操作。

## 理论基础

- **请求封装**：将请求封装为对象
- **参数化**：支持不同请求的参数化
- **撤销重做**：支持操作的撤销和重做

## Rust实现示例

```rust
trait Command {
    fn execute(&self);
    fn undo(&self);
}

struct Receiver;
impl Receiver {
    fn action(&self) {
        println!("执行操作");
    }
    
    fn undo_action(&self) {
        println!("撤销操作");
    }
}

struct ConcreteCommand {
    receiver: Receiver,
}

impl ConcreteCommand {
    fn new(receiver: Receiver) -> Self {
        Self { receiver }
    }
}

impl Command for ConcreteCommand {
    fn execute(&self) {
        self.receiver.action();
    }
    
    fn undo(&self) {
        self.receiver.undo_action();
    }
}

struct Invoker {
    commands: Vec<Box<dyn Command>>,
}

impl Invoker {
    fn new() -> Self {
        Self { commands: Vec::new() }
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

fn main() {
    let receiver = Receiver;
    let command = ConcreteCommand::new(receiver);
    let mut invoker = Invoker::new();
    
    invoker.add_command(Box::new(command));
    invoker.execute_all();
}
```

## Haskell实现示例

```haskell
class Command a where
    execute :: a -> IO ()
    undo :: a -> IO ()

data Receiver = Receiver
action :: Receiver -> IO ()
action _ = putStrLn "执行操作"
undoAction :: Receiver -> IO ()
undoAction _ = putStrLn "撤销操作"

data ConcreteCommand = ConcreteCommand Receiver
instance Command ConcreteCommand where
    execute (ConcreteCommand receiver) = action receiver
    undo (ConcreteCommand receiver) = undoAction receiver

data Invoker = Invoker [ConcreteCommand]
addCommand :: Invoker -> ConcreteCommand -> Invoker
addCommand (Invoker commands) command = Invoker (command : commands)
executeAll :: Invoker -> IO ()
executeAll (Invoker commands) = mapM_ execute commands

main = do
    let receiver = Receiver
    let command = ConcreteCommand receiver
    let invoker = Invoker []
    let invoker' = addCommand invoker command
    executeAll invoker'
```

## Lean实现思路

```lean
class Command (α : Type) where
  execute : α → IO Unit
  undo : α → IO Unit

structure Receiver
def action (_ : Receiver) : IO Unit := IO.println "执行操作"
def undoAction (_ : Receiver) : IO Unit := IO.println "撤销操作"

structure ConcreteCommand where
  receiver : Receiver

instance : Command ConcreteCommand where
  execute c := action c.receiver
  undo c := undoAction c.receiver

structure Invoker where
  commands : List ConcreteCommand

def addCommand (invoker : Invoker) (command : ConcreteCommand) : Invoker :=
  { invoker with commands := command :: invoker.commands }

def executeAll (invoker : Invoker) : IO Unit :=
  invoker.commands.forM Command.execute
```

## 应用场景

- GUI按钮事件处理
- 宏录制和回放
- 事务处理
- 撤销重做功能

## 最佳实践

- 命令对象应保持轻量
- 支持命令的组合和批处理
- 实现撤销机制时考虑状态管理
