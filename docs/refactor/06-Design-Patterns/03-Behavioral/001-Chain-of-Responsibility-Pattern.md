# 001 责任链模式

## 1. 理论基础

责任链模式是一种行为型设计模式，将请求的发送者和接收者解耦，沿着链传递请求直到被处理。每个处理器决定是否处理请求或传递给下一个处理器。

## 2. 接口设计

```haskell
-- Haskell接口设计
class Handler a where
  setNext :: a -> a -> a
  handle :: a -> Request -> Maybe Response

-- 请求和响应
data Request = Request String deriving Show
data Response = Response String deriving Show

-- 处理器基类
data BaseHandler = BaseHandler (Maybe BaseHandler)
```

## 3. 多语言实现

### Haskell实现

```haskell
-- 请求和响应类型
data Request = Request String deriving Show
data Response = Response String deriving Show

-- 处理器接口
class Handler a where
  setNext :: a -> a -> a
  handle :: a -> Request -> Maybe Response

-- 具体处理器
data ConcreteHandlerA = ConcreteHandlerA (Maybe ConcreteHandlerA) deriving Show
data ConcreteHandlerB = ConcreteHandlerB (Maybe ConcreteHandlerB) deriving Show

instance Handler ConcreteHandlerA where
  setNext handler next = ConcreteHandlerA (Just next)
  handle (ConcreteHandlerA _) (Request req) = 
    if "A" `isInfixOf` req
    then Just $ Response "Handled by A"
    else Nothing

instance Handler ConcreteHandlerB where
  setNext handler next = ConcreteHandlerB (Just next)
  handle (ConcreteHandlerB _) (Request req) = 
    if "B" `isInfixOf` req
    then Just $ Response "Handled by B"
    else Nothing

-- 使用示例
main :: IO ()
main = do
  let handlerA = ConcreteHandlerA Nothing
  let handlerB = ConcreteHandlerB Nothing
  let chain = setNext handlerA handlerB
  let request = Request "Request for B"
  print $ handle chain request
```

### Rust实现

```rust
// 请求和响应
#[derive(Debug)]
struct Request {
    content: String,
}

#[derive(Debug)]
struct Response {
    content: String,
}

// 处理器trait
trait Handler {
    fn set_next(&mut self, next: Box<dyn Handler>);
    fn handle(&self, request: &Request) -> Option<Response>;
}

// 具体处理器A
struct ConcreteHandlerA {
    next: Option<Box<dyn Handler>>,
}

impl ConcreteHandlerA {
    fn new() -> Self {
        ConcreteHandlerA { next: None }
    }
}

impl Handler for ConcreteHandlerA {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }
    
    fn handle(&self, request: &Request) -> Option<Response> {
        if request.content.contains("A") {
            Some(Response {
                content: "Handled by A".to_string(),
            })
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}

// 具体处理器B
struct ConcreteHandlerB {
    next: Option<Box<dyn Handler>>,
}

impl ConcreteHandlerB {
    fn new() -> Self {
        ConcreteHandlerB { next: None }
    }
}

impl Handler for ConcreteHandlerB {
    fn set_next(&mut self, next: Box<dyn Handler>) {
        self.next = Some(next);
    }
    
    fn handle(&self, request: &Request) -> Option<Response> {
        if request.content.contains("B") {
            Some(Response {
                content: "Handled by B".to_string(),
            })
        } else {
            self.next.as_ref().and_then(|h| h.handle(request))
        }
    }
}
```

### Lean实现

```lean
-- 请求和响应类型
def Request := String
def Response := String

-- 处理器类型
inductive Handler where
  | ConcreteA : Option Handler → Handler
  | ConcreteB : Option Handler → Handler

-- 处理函数
def handle : Handler → Request → Option Response
  | Handler.ConcreteA next, req => 
    if "A" ∈ req then some "Handled by A"
    else match next with
      | none => none
      | some h => handle h req
  | Handler.ConcreteB next, req => 
    if "B" ∈ req then some "Handled by B"
    else match next with
      | none => none
      | some h => handle h req

-- 责任链正确性定理
theorem chain_termination :
  ∀ h : Handler, ∀ req : Request,
  handle h req ≠ none ∨ handle h req = none :=
  by simp [handle]
```

## 4. 工程实践

- 请求处理流程
- 异常处理链
- 中间件模式
- 过滤器链

## 5. 性能优化

- 避免过长链
- 缓存处理结果
- 异步处理
- 负载均衡

## 6. 应用场景

- 异常处理
- 日志记录
- 权限验证
- 请求过滤

## 7. 最佳实践

- 保持链简洁
- 避免循环引用
- 考虑性能影响
- 实现默认处理
