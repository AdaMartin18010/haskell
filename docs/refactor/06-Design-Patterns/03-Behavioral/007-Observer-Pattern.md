# 观察者模式（Observer Pattern）

## 概述
观察者模式是一种行为型设计模式，定义对象间的一种一对多的依赖关系，当一个对象的状态发生改变时，所有依赖于它的对象都得到通知并被自动更新。

## 理论基础
- **发布订阅**：主题发布，观察者订阅
- **松耦合**：主题与观察者松耦合
- **自动通知**：状态变化时自动通知

## Rust实现示例
```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

trait Observer {
    fn update(&self, message: &str);
}

trait Subject {
    fn attach(&mut self, observer: Arc<dyn Observer>);
    fn detach(&mut self, observer: Arc<dyn Observer>);
    fn notify(&self, message: &str);
}

struct ConcreteSubject {
    observers: Arc<Mutex<Vec<Arc<dyn Observer>>>>,
}

impl ConcreteSubject {
    fn new() -> Self {
        Self {
            observers: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    fn set_state(&self, state: &str) {
        println!("主题状态改变为: {}", state);
        self.notify(state);
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Arc<dyn Observer>) {
        if let Ok(mut observers) = self.observers.lock() {
            observers.push(observer);
        }
    }
    
    fn detach(&mut self, observer: Arc<dyn Observer>) {
        if let Ok(mut observers) = self.observers.lock() {
            observers.retain(|obs| !Arc::ptr_eq(obs, &observer));
        }
    }
    
    fn notify(&self, message: &str) {
        if let Ok(observers) = self.observers.lock() {
            for observer in observers.iter() {
                observer.update(message);
            }
        }
    }
}

struct ConcreteObserverA {
    name: String,
}

impl ConcreteObserverA {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserverA {
    fn update(&self, message: &str) {
        println!("观察者A {} 收到通知: {}", self.name, message);
    }
}

struct ConcreteObserverB {
    name: String,
}

impl ConcreteObserverB {
    fn new(name: String) -> Self {
        Self { name }
    }
}

impl Observer for ConcreteObserverB {
    fn update(&self, message: &str) {
        println!("观察者B {} 收到通知: {}", self.name, message);
    }
}

fn main() {
    let mut subject = ConcreteSubject::new();
    
    let observer_a1 = Arc::new(ConcreteObserverA::new("观察者A1".to_string()));
    let observer_a2 = Arc::new(ConcreteObserverA::new("观察者A2".to_string()));
    let observer_b = Arc::new(ConcreteObserverB::new("观察者B".to_string()));
    
    subject.attach(observer_a1.clone());
    subject.attach(observer_a2.clone());
    subject.attach(observer_b.clone());
    
    subject.set_state("状态1");
    
    subject.detach(observer_a1.clone());
    subject.set_state("状态2");
}
```

## Haskell实现示例
```haskell
import Data.IORef
import Control.Monad

class Observer a where
    update :: a -> String -> IO ()

class Subject a where
    attach :: a -> Observer -> IO ()
    detach :: a -> Observer -> IO ()
    notify :: a -> String -> IO ()

data ConcreteSubject = ConcreteSubject (IORef [Observer])
newSubject :: IO ConcreteSubject
newSubject = ConcreteSubject <$> newIORef []
setState :: ConcreteSubject -> String -> IO ()
setState subject state = do
    putStrLn $ "主题状态改变为: " ++ state
    notify subject state

instance Subject ConcreteSubject where
    attach (ConcreteSubject observersRef) observer = do
        observers <- readIORef observersRef
        writeIORef observersRef (observer : observers)
    detach (ConcreteSubject observersRef) observer = do
        observers <- readIORef observersRef
        writeIORef observersRef (filter (/= observer) observers)
    notify (ConcreteSubject observersRef) message = do
        observers <- readIORef observersRef
        mapM_ (\obs -> update obs message) observers

data ConcreteObserverA = ConcreteObserverA String
newObserverA :: String -> ConcreteObserverA
newObserverA name = ConcreteObserverA name
instance Observer ConcreteObserverA where
    update (ConcreteObserverA name) message = 
        putStrLn $ "观察者A " ++ name ++ " 收到通知: " ++ message

data ConcreteObserverB = ConcreteObserverB String
newObserverB :: String -> ConcreteObserverB
newObserverB name = ConcreteObserverB name
instance Observer ConcreteObserverB where
    update (ConcreteObserverB name) message = 
        putStrLn $ "观察者B " ++ name ++ " 收到通知: " ++ message

main = do
    subject <- newSubject
    let observerA1 = newObserverA "观察者A1"
    let observerA2 = newObserverA "观察者A2"
    let observerB = newObserverB "观察者B"
    
    attach subject observerA1
    attach subject observerA2
    attach subject observerB
    
    setState subject "状态1"
    
    detach subject observerA1
    setState subject "状态2"
```

## Lean实现思路
```lean
class Observer (α : Type) where
  update : α → String → IO Unit

class Subject (α : Type) where
  attach : α → Observer → IO Unit
  detach : α → Observer → IO Unit
  notify : α → String → IO Unit

structure ConcreteSubject where
  observers : List Observer

def newSubject : IO ConcreteSubject :=
  pure { observers := [] }

def setState (subject : ConcreteSubject) (state : String) : IO Unit := do
  IO.println ("主题状态改变为: " ++ state)
  Subject.notify subject state

instance : Subject ConcreteSubject where
  attach subject observer := 
    pure { subject with observers := observer :: subject.observers }
  detach subject observer :=
    pure { subject with observers := subject.observers.filter (· ≠ observer) }
  notify subject message :=
    subject.observers.forM fun obs => Observer.update obs message

structure ConcreteObserverA where
  name : String

def newObserverA (name : String) : ConcreteObserverA := { name := name }

instance : Observer ConcreteObserverA where
  update obs message := 
    IO.println ("观察者A " ++ obs.name ++ " 收到通知: " ++ message)

structure ConcreteObserverB where
  name : String

def newObserverB (name : String) : ConcreteObserverB := { name := name }

instance : Observer ConcreteObserverB where
  update obs message := 
    IO.println ("观察者B " ++ obs.name ++ " 收到通知: " ++ message)
```

## 应用场景
- GUI事件处理
- 数据绑定
- 消息推送
- 日志系统

## 最佳实践
- 避免观察者链过长
- 防止循环依赖
- 支持异步通知 