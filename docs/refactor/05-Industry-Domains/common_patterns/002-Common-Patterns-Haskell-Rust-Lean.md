# 通用模式的多语言实现：Haskell、Rust、Lean

## 概述

本文档探讨如何用Haskell、Rust和Lean三种语言实现软件工程中的通用设计模式，包括单例、工厂、观察者、策略、装饰器等。

## 理论基础

### 通用设计模式类型系统

```haskell
-- Haskell: 通用设计模式类型系统
data DesignPattern = Singleton | Factory | Observer | Strategy | Decorator

data Singleton a = Singleton { getInstance :: IO a }

data Factory a = Factory { create :: String -> a }

data Observer a = Observer { subscribe :: (a -> IO ()) -> IO (), notify :: a -> IO () }

data Strategy a = Strategy { execute :: a -> IO () }

data Decorator a = Decorator { decorate :: a -> a }
```

```rust
// Rust: 通用设计模式结构
pub enum DesignPattern {
    Singleton,
    Factory,
    Observer,
    Strategy,
    Decorator,
}

pub struct Singleton<T> {
    instance: Option<T>,
}

impl<T> Singleton<T> {
    pub fn get_instance() -> &'static T {
        // 静态单例实现
        unimplemented!()
    }
}

pub struct Factory<T> {
    create: fn(&str) -> T,
}

pub struct Observer<T> {
    subscribers: Vec<Box<dyn Fn(&T)>>,
}

pub struct Strategy<T> {
    execute: fn(T),
}

pub struct Decorator<T> {
    decorate: fn(T) -> T,
}
```

```lean
-- Lean: 通用设计模式形式化定义
inductive DesignPattern
| singleton
| factory
| observer
| strategy
| decorator

structure Singleton (α : Type) :=
(get_instance : IO α)

structure Factory (α : Type) :=
(create : String → α)

structure Observer (α : Type) :=
(subscribe : (α → IO Unit) → IO Unit)
(notify : α → IO Unit)

structure Strategy (α : Type) :=
(execute : α → IO Unit)

structure Decorator (α : Type) :=
(decorate : α → α)
```

## 单例模式

### Haskell实现

```haskell
-- 单例模式
module Patterns.Singleton where

import Data.IORef
import System.IO.Unsafe

singleton :: IORef (Maybe a) -> IO a -> IO a
singleton ref create = do
  mVal <- readIORef ref
  case mVal of
    Just val -> return val
    Nothing -> do
      val <- create
      writeIORef ref (Just val)
      return val
```

### Rust实现

```rust
// 单例模式
use std::sync::{Once, ONCE_INIT};

static mut INSTANCE: Option<MyType> = None;
static INIT: Once = ONCE_INIT;

fn get_instance() -> &'static MyType {
    unsafe {
        INIT.call_once(|| {
            INSTANCE = Some(MyType::new());
        });
        INSTANCE.as_ref().unwrap()
    }
}
```

### Lean实现

```lean
-- 单例模式
structure Singleton (α : Type) :=
(get_instance : IO α)

def singleton (create : IO α) : IO α :=
  let ref := IO.mkRef none in
  match ← ref.get with
  | some val => pure val
  | none => do val ← create; ref.set (some val); pure val
```

## 工厂模式

### Haskell实现

```haskell
-- 工厂模式
module Patterns.Factory where

factory :: (String -> a) -> String -> a
factory create name = create name
```

### Rust实现

```rust
// 工厂模式
fn factory<T, F: Fn(&str) -> T>(create: F, name: &str) -> T {
    create(name)
}
```

### Lean实现

```lean
-- 工厂模式
def factory {α : Type} (create : String → α) (name : String) : α :=
  create name
```

## 观察者模式

### Haskell实现

```haskell
-- 观察者模式
module Patterns.Observer where

import Data.IORef

observer :: IORef [a -> IO ()] -> (a -> IO ()) -> IO ()
observer ref callback = modifyIORef ref (callback:)

notify :: IORef [a -> IO ()] -> a -> IO ()
notify ref val = do
  callbacks <- readIORef ref
  mapM_ ($ val) callbacks
```

### Rust实现

```rust
// 观察者模式
struct Observer<T> {
    subscribers: Vec<Box<dyn Fn(&T)>>,
}

impl<T> Observer<T> {
    fn subscribe(&mut self, callback: Box<dyn Fn(&T)>) {
        self.subscribers.push(callback);
    }
    fn notify(&self, value: &T) {
        for cb in &self.subscribers {
            cb(value);
        }
    }
}
```

### Lean实现

```lean
-- 观察者模式
structure Observer (α : Type) :=
(subscribers : IO.Ref (List (α → IO Unit)))

 def subscribe (obs : Observer α) (cb : α → IO Unit) : IO Unit :=
  obs.subscribers.modify (λ l => cb :: l)

def notify (obs : Observer α) (val : α) : IO Unit :=
  obs.subscribers.get >>= λ cbs => cbs.mmap' (λ cb => cb val)
```

## 策略模式

### Haskell实现

```haskell
-- 策略模式
module Patterns.Strategy where

strategy :: (a -> IO ()) -> a -> IO ()
strategy exec val = exec val
```

### Rust实现

```rust
// 策略模式
struct Strategy<T> {
    execute: fn(T),
}

fn use_strategy<T>(strategy: &Strategy<T>, value: T) {
    (strategy.execute)(value);
}
```

### Lean实现

```lean
-- 策略模式
def strategy {α : Type} (exec : α → IO Unit) (val : α) : IO Unit :=
  exec val
```

## 装饰器模式

### Haskell实现

```haskell
-- 装饰器模式
module Patterns.Decorator where

decorator :: (a -> a) -> a -> a
decorator decorate val = decorate val
```

### Rust实现

```rust
// 装饰器模式
fn decorator<T, F: Fn(T) -> T>(decorate: F, value: T) -> T {
    decorate(value)
}
```

### Lean实现

```lean
-- 装饰器模式
def decorator {α : Type} (decorate : α → α) (val : α) : α :=
  decorate val
```

## 总结

本文档展示了通用设计模式在Haskell、Rust和Lean中的实现方式，涵盖单例、工厂、观察者、策略、装饰器等模式，为多语言工程实践提供参考。 