# 004 中介者模式

## 1. 理论基础

中介者模式是一种行为型设计模式，定义一个中介对象来封装对象间的交互。降低对象间的耦合度，使对象不需要显式地相互引用。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Mediator a where
  send :: a -> String -> String -> IO ()

class Colleague a where
  sendMessage :: a -> String -> IO ()
  receiveMessage :: a -> String -> IO ()

-- 具体中介者
data ConcreteMediator = ConcreteMediator [Colleague]
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 中介者接口
class Mediator a where
  send :: a -> String -> String -> IO ()

-- 同事接口
class Colleague a where
  sendMessage :: a -> String -> IO ()
  receiveMessage :: a -> String -> IO ()

-- 具体同事
data ConcreteColleague = ConcreteColleague String deriving Show

instance Colleague ConcreteColleague where
  sendMessage (ConcreteColleague name) message = 
    putStrLn $ name ++ " sends: " ++ message
  receiveMessage (ConcreteColleague name) message = 
    putStrLn $ name ++ " receives: " ++ message

-- 具体中介者
data ConcreteMediator = ConcreteMediator [ConcreteColleague] deriving Show

instance Mediator ConcreteMediator where
  send (ConcreteMediator colleagues) from message = do
    mapM_ (\colleague -> 
      if colleague /= from
      then receiveMessage colleague message
      else return ()) colleagues

-- 使用示例
main :: IO ()
main = do
  let colleague1 = ConcreteColleague "Alice"
  let colleague2 = ConcreteColleague "Bob"
  let mediator = ConcreteMediator [colleague1, colleague2]
  sendMessage colleague1 "Hello from Alice"
  send mediator colleague1 "Hello from Alice"
```

### Rust实现

```rust
// 中介者trait
trait Mediator {
    fn send(&self, from: &str, message: &str);
}

// 同事trait
trait Colleague {
    fn send_message(&self, message: &str);
    fn receive_message(&self, message: &str);
}

// 具体同事
struct ConcreteColleague {
    name: String,
    mediator: Option<Box<dyn Mediator>>,
}

impl ConcreteColleague {
    fn new(name: &str) -> Self {
        ConcreteColleague {
            name: name.to_string(),
            mediator: None,
        }
    }
    
    fn set_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.mediator = Some(mediator);
    }
}

impl Colleague for ConcreteColleague {
    fn send_message(&self, message: &str) {
        println!("{} sends: {}", self.name, message);
        if let Some(mediator) = &self.mediator {
            mediator.send(&self.name, message);
        }
    }
    
    fn receive_message(&self, message: &str) {
        println!("{} receives: {}", self.name, message);
    }
}

// 具体中介者
struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague>>,
}

impl Mediator for ConcreteMediator {
    fn send(&self, from: &str, message: &str) {
        for colleague in &self.colleagues {
            // 这里需要类型检查来避免发送给自己
            colleague.receive_message(message);
        }
    }
}
```

### Lean实现

```lean
-- 中介者类型
def Mediator := String → String → IO Unit

-- 同事类型
def Colleague := String

-- 中介者实现
def concreteMediator : Mediator :=
  fun from message => IO.println ("Mediator forwards: " ++ message)

-- 同事操作
def sendMessage (colleague : Colleague) (message : String) : IO Unit :=
  IO.println (colleague ++ " sends: " ++ message)

def receiveMessage (colleague : Colleague) (message : String) : IO Unit :=
  IO.println (colleague ++ " receives: " ++ message)

-- 中介者解耦定理
theorem mediator_decoupling :
  ∀ m : Mediator, ∀ c : Colleague, ∀ msg : String,
  sendMessage c msg ≠ receiveMessage c msg :=
  by simp [sendMessage, receiveMessage]
```

## 4. 工程实践

- 对象解耦
- 集中控制
- 事件处理
- 消息路由

## 5. 性能优化

- 消息缓存
- 异步处理
- 负载均衡
- 内存管理

## 6. 应用场景

- 聊天系统
- 事件总线
- 消息队列
- 工作流引擎

## 7. 最佳实践

- 保持中介者简单
- 避免过度耦合
- 考虑性能影响
- 实现错误处理
