# 责任链模式（Chain of Responsibility Pattern）

## 概述

责任链模式是一种行为型设计模式，允许多个对象处理同一个请求，而无需明确指定接收者。请求沿着处理者链进行传递，直到有一个处理者处理它。

## 理论基础

- **请求传递**：请求在链中依次传递
- **处理者解耦**：发送者与接收者解耦
- **动态链构建**：运行时动态构建处理链

## Rust实现示例

```rust
trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>);
    fn handle(&self, request: &str) -> Option<String>;
}

struct ConcreteHandlerA {
    next: Option<Box<dyn Handler>>,
}

impl ConcreteHandlerA {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for ConcreteHandlerA {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }
    
    fn handle(&self, request: &str) -> Option<String> {
        if request.contains("A") {
            Some("HandlerA处理了请求".to_string())
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}

struct ConcreteHandlerB {
    next: Option<Box<dyn Handler>>,
}

impl ConcreteHandlerB {
    fn new() -> Self {
        Self { next: None }
    }
}

impl Handler for ConcreteHandlerB {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }
    
    fn handle(&self, request: &str) -> Option<String> {
        if request.contains("B") {
            Some("HandlerB处理了请求".to_string())
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}

fn main() {
    let mut handler_a = ConcreteHandlerA::new();
    let mut handler_b = ConcreteHandlerB::new();
    
    handler_a.set_next(Box::new(handler_b));
    
    println!("{:?}", handler_a.handle("请求A"));
    println!("{:?}", handler_a.handle("请求B"));
    println!("{:?}", handler_a.handle("请求C"));
}
```

## Haskell实现示例

```haskell
class Handler a where
    setNext :: a -> a -> a
    handle :: a -> String -> Maybe String

data ConcreteHandlerA = ConcreteHandlerA (Maybe ConcreteHandlerB)
instance Handler ConcreteHandlerA where
    setNext (ConcreteHandlerA _) next = ConcreteHandlerA (Just next)
    handle (ConcreteHandlerA next) request
        | "A" `isInfixOf` request = Just "HandlerA处理了请求"
        | otherwise = case next of
            Just h -> handle h request
            Nothing -> Nothing

data ConcreteHandlerB = ConcreteHandlerB (Maybe ConcreteHandlerA)
instance Handler ConcreteHandlerB where
    setNext (ConcreteHandlerB _) next = ConcreteHandlerB (Just next)
    handle (ConcreteHandlerB next) request
        | "B" `isInfixOf` request = Just "HandlerB处理了请求"
        | otherwise = case next of
            Just h -> handle h request
            Nothing -> Nothing

main = do
    let handlerA = ConcreteHandlerA Nothing
    let handlerB = ConcreteHandlerB Nothing
    let chain = setNext handlerA handlerB
    
    putStrLn $ show $ handle chain "请求A"
    putStrLn $ show $ handle chain "请求B"
    putStrLn $ show $ handle chain "请求C"
```

## Lean实现思路

```lean
class Handler (α : Type) where
  setNext : α → α → α
  handle : α → String → Option String

structure ConcreteHandlerA where
  next : Option ConcreteHandlerB

instance : Handler ConcreteHandlerA where
  setNext h next := { h with next := some next }
  handle h request :=
    if "A" ∈ request then some "HandlerA处理了请求"
    else match h.next with
    | some next => handle next request
    | none => none

structure ConcreteHandlerB where
  next : Option ConcreteHandlerA

instance : Handler ConcreteHandlerB where
  setNext h next := { h with next := some next }
  handle h request :=
    if "B" ∈ request then some "HandlerB处理了请求"
    else match h.next with
    | some next => handle next request
    | none => none
```

## 应用场景

- 异常处理链
- 中间件处理
- 权限验证链
- 日志处理链

## 最佳实践

- 避免链过长影响性能
- 确保链的完整性
- 提供默认处理机制
