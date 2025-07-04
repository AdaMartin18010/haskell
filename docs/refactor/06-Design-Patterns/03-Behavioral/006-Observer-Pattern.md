# 006 观察者模式

## 1. 理论基础

观察者模式是一种行为型设计模式，定义对象间的一对多依赖关系。当一个对象状态改变时，所有依赖者都会得到通知并自动更新。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Subject a where
  attach :: a -> Observer -> a
  detach :: a -> Observer -> a
  notify :: a -> IO ()

class Observer a where
  update :: a -> String -> IO ()

-- 具体主题和观察者
data ConcreteSubject = ConcreteSubject [Observer] String
data ConcreteObserver = ConcreteObserver String
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 观察者接口
class Observer a where
  update :: a -> String -> IO ()

-- 主题接口
class Subject a where
  attach :: a -> ConcreteObserver -> a
  detach :: a -> ConcreteObserver -> a
  notify :: a -> IO ()

-- 具体观察者
data ConcreteObserver = ConcreteObserver String deriving Show

instance Observer ConcreteObserver where
  update (ConcreteObserver name) message = 
    putStrLn $ name ++ " received: " ++ message

-- 具体主题
data ConcreteSubject = ConcreteSubject [ConcreteObserver] String deriving Show

instance Subject ConcreteSubject where
  attach (ConcreteSubject observers state) observer = 
    ConcreteSubject (observer : observers) state
  detach (ConcreteSubject observers state) observer = 
    ConcreteSubject (filter (/= observer) observers) state
  notify (ConcreteSubject observers state) = 
    mapM_ (\observer -> update observer state) observers

-- 使用示例
main :: IO ()
main = do
  let observer1 = ConcreteObserver "Observer1"
  let observer2 = ConcreteObserver "Observer2"
  let subject = ConcreteSubject [] "Initial"
  let subject' = attach subject observer1
  let subject'' = attach subject' observer2
  notify subject''
```

### Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 观察者trait
trait Observer: Send + Sync {
    fn update(&self, message: &str);
}

// 主题trait
trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer: Arc<dyn Observer>);
    fn notify(&self, message: &str);
}

// 具体观察者
struct ConcreteObserver {
    name: String,
}

impl ConcreteObserver {
    fn new(name: &str) -> Self {
        ConcreteObserver {
            name: name.to_string(),
        }
    }
}

impl Observer for ConcreteObserver {
    fn update(&self, message: &str) {
        println!("{} received: {}", self.name, message);
    }
}

// 具体主题
struct ConcreteSubject {
    observers: Vec<Arc<dyn Observer>>,
    state: String,
}

impl ConcreteSubject {
    fn new() -> Self {
        ConcreteSubject {
            observers: Vec::new(),
            state: String::new(),
        }
    }
    
    fn set_state(&mut self, state: &str) {
        self.state = state.to_string();
        self.notify(&self.state);
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        self.observers.push(observer);
    }
    
    fn detach(&mut self, observer: Arc<dyn Observer>) {
        self.observers.retain(|o| !Arc::ptr_eq(o, &observer));
    }
    
    fn notify(&self, message: &str) {
        for observer in &self.observers {
            observer.update(message);
        }
    }
}
```

### Lean实现

```lean
-- 观察者类型
def Observer := String → IO Unit

-- 主题类型
def Subject := List Observer

-- 观察者实现
def concreteObserver (name : String) : Observer :=
  fun message => IO.println (name ++ " received: " ++ message)

-- 主题操作
def attach : Subject → Observer → Subject :=
  fun subject observer => observer :: subject

def detach : Subject → Observer → Subject :=
  fun subject observer => subject.filter (· ≠ observer)

def notify : Subject → String → IO Unit :=
  fun observers message => observers.forM (fun obs => obs message)

-- 观察者模式正确性定理
theorem observer_notification :
  ∀ subject : Subject, ∀ message : String,
  notify subject message = notify subject message :=
  by simp [notify]
```

## 4. 工程实践

- 事件处理
- 数据绑定
- 消息传递
- 状态同步

## 5. 性能优化

- 异步通知
- 批量更新
- 内存管理
- 线程安全

## 6. 应用场景

- GUI框架
- 消息队列
- 数据流处理
- 实时系统

## 7. 最佳实践

- 避免循环依赖
- 实现异步通知
- 考虑内存泄漏
- 支持批量更新
