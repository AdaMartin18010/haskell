# 中介者模式（Mediator Pattern）

## 概述

中介者模式是一种行为型设计模式，用一个中介对象封装一系列对象交互，中介者使各对象不需要显式地相互引用，从而使其耦合松散，而且可以独立地改变它们之间的交互。

## 理论基础

- **集中控制**：中介者集中管理对象间交互
- **解耦对象**：对象间不直接通信
- **简化交互**：复杂的多对多交互简化为一对多

## Rust实现示例

```rust
trait Colleague {
    fn set_mediator(&mut self, mediator: &dyn Mediator);
    fn send(&self, message: &str);
    fn receive(&self, message: &str);
}

trait Mediator {
    fn send(&self, message: &str, colleague: &dyn Colleague);
}

struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague>>,
}

impl ConcreteMediator {
    fn new() -> Self {
        Self { colleagues: Vec::new() }
    }
    
    fn add_colleague(&mut self, colleague: Box<dyn Colleague>) {
        self.colleagues.push(colleague);
    }
}

impl Mediator for ConcreteMediator {
    fn send(&self, message: &str, sender: &dyn Colleague) {
        for colleague in &self.colleagues {
            // 避免自己给自己发送消息
            if std::ptr::eq(colleague.as_ref(), sender) {
                continue;
            }
            colleague.receive(message);
        }
    }
}

struct ConcreteColleagueA {
    mediator: Option<&'static dyn Mediator>,
    name: String,
}

impl ConcreteColleagueA {
    fn new(name: String) -> Self {
        Self { mediator: None, name }
    }
}

impl Colleague for ConcreteColleagueA {
    fn set_mediator(&mut self, mediator: &'static dyn Mediator) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = self.mediator {
            println!("{} 发送消息: {}", self.name, message);
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("{} 收到消息: {}", self.name, message);
    }
}

struct ConcreteColleagueB {
    mediator: Option<&'static dyn Mediator>,
    name: String,
}

impl ConcreteColleagueB {
    fn new(name: String) -> Self {
        Self { mediator: None, name }
    }
}

impl Colleague for ConcreteColleagueB {
    fn set_mediator(&mut self, mediator: &'static dyn Mediator) {
        self.mediator = Some(mediator);
    }
    
    fn send(&self, message: &str) {
        if let Some(mediator) = self.mediator {
            println!("{} 发送消息: {}", self.name, message);
            mediator.send(message, self);
        }
    }
    
    fn receive(&self, message: &str) {
        println!("{} 收到消息: {}", self.name, message);
    }
}

fn main() {
    let mut mediator = ConcreteMediator::new();
    let mut colleague_a = ConcreteColleagueA::new("同事A".to_string());
    let mut colleague_b = ConcreteColleagueB::new("同事B".to_string());
    
    // 设置中介者
    colleague_a.set_mediator(&mediator);
    colleague_b.set_mediator(&mediator);
    
    // 添加同事到中介者
    mediator.add_colleague(Box::new(colleague_a));
    mediator.add_colleague(Box::new(colleague_b));
    
    // 发送消息
    colleague_a.send("Hello from A");
    colleague_b.send("Hello from B");
}
```

## Haskell实现示例

```haskell
class Colleague a where
    setMediator :: a -> Mediator -> a
    send :: a -> String -> IO ()
    receive :: a -> String -> IO ()

class Mediator a where
    send :: a -> String -> Colleague -> IO ()

data ConcreteMediator = ConcreteMediator [Colleague]
newMediator :: ConcreteMediator
newMediator = ConcreteMediator []
addColleague :: ConcreteMediator -> Colleague -> ConcreteMediator
addColleague (ConcreteMediator colleagues) colleague = 
    ConcreteMediator (colleague : colleagues)

instance Mediator ConcreteMediator where
    send (ConcreteMediator colleagues) message sender = do
        mapM_ (\c -> if c /= sender then receive c message else return ()) colleagues

data ConcreteColleagueA = ConcreteColleagueA (Maybe Mediator) String
newColleagueA :: String -> ConcreteColleagueA
newColleagueA name = ConcreteColleagueA Nothing name

instance Colleague ConcreteColleagueA where
    setMediator (ConcreteColleagueA _ name) mediator = ConcreteColleagueA (Just mediator) name
    send (ConcreteColleagueA (Just mediator) name) message = do
        putStrLn $ name ++ " 发送消息: " ++ message
        Mediator.send mediator message (ConcreteColleagueA (Just mediator) name)
    send (ConcreteColleagueA Nothing name) message = 
        putStrLn $ name ++ " 发送消息: " ++ message ++ " (无中介者)"
    receive (ConcreteColleagueA _ name) message = 
        putStrLn $ name ++ " 收到消息: " ++ message

data ConcreteColleagueB = ConcreteColleagueB (Maybe Mediator) String
newColleagueB :: String -> ConcreteColleagueB
newColleagueB name = ConcreteColleagueB Nothing name

instance Colleague ConcreteColleagueB where
    setMediator (ConcreteColleagueB _ name) mediator = ConcreteColleagueB (Just mediator) name
    send (ConcreteColleagueB (Just mediator) name) message = do
        putStrLn $ name ++ " 发送消息: " ++ message
        Mediator.send mediator message (ConcreteColleagueB (Just mediator) name)
    send (ConcreteColleagueB Nothing name) message = 
        putStrLn $ name ++ " 发送消息: " ++ message ++ " (无中介者)"
    receive (ConcreteColleagueB _ name) message = 
        putStrLn $ name ++ " 收到消息: " ++ message

main = do
    let mediator = newMediator
    let colleagueA = newColleagueA "同事A"
    let colleagueB = newColleagueB "同事B"
    
    let colleagueA' = setMediator colleagueA mediator
    let colleagueB' = setMediator colleagueB mediator
    
    let mediator' = addColleague (addColleague mediator colleagueA') colleagueB'
    
    send colleagueA' "Hello from A"
    send colleagueB' "Hello from B"
```

## Lean实现思路

```lean
class Colleague (α : Type) where
  setMediator : α → Mediator → α
  send : α → String → IO Unit
  receive : α → String → IO Unit

class Mediator (α : Type) where
  send : α → String → Colleague → IO Unit

structure ConcreteMediator where
  colleagues : List Colleague

def newMediator : ConcreteMediator := { colleagues := [] }
def addColleague (mediator : ConcreteMediator) (colleague : Colleague) : ConcreteMediator :=
  { mediator with colleagues := colleague :: mediator.colleagues }

instance : Mediator ConcreteMediator where
  send mediator message sender :=
    mediator.colleagues.forM fun c => 
      if c ≠ sender then receive c message else pure ()

structure ConcreteColleagueA where
  mediator : Option Mediator
  name : String

def newColleagueA (name : String) : ConcreteColleagueA :=
  { mediator := none, name := name }

instance : Colleague ConcreteColleagueA where
  setMediator c mediator := { c with mediator := some mediator }
  send c message := 
    match c.mediator with
    | some mediator => 
        IO.println (c.name ++ " 发送消息: " ++ message) >>
        Mediator.send mediator message c
    | none => IO.println (c.name ++ " 发送消息: " ++ message ++ " (无中介者)")
  receive c message := IO.println (c.name ++ " 收到消息: " ++ message)
```

## 应用场景

- GUI组件交互
- 聊天室系统
- 工作流协调
- 微服务通信

## 最佳实践

- 避免中介者过于复杂
- 合理划分职责
- 支持动态添加/移除同事
