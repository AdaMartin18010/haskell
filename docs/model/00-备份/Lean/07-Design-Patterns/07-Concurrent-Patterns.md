# Lean 并发设计模式

## 🎯 概述

并发设计模式在Lean中通过IO Monad、异步编程和类型安全的并发原语实现高效的并发和并行计算。

## 🎭 Actor模式

### 基础Actor

```lean
-- Actor模式
namespace ActorPattern

-- Actor消息类型
inductive Message : Type
  | Ping : Message
  | Pong : Message
  | Data : String → Message
  | Stop : Message

-- Actor状态
structure ActorState where
  name : String
  messageCount : Nat
  isRunning : Bool

-- Actor行为
def ActorState.handleMessage (state : ActorState) (msg : Message) : IO ActorState :=
  match msg with
  | Message.Ping => do
    IO.println s!"{state.name}: Received Ping"
    return { state with messageCount := state.messageCount + 1 }
  | Message.Pong => do
    IO.println s!"{state.name}: Received Pong"
    return { state with messageCount := state.messageCount + 1 }
  | Message.Data content => do
    IO.println s!"{state.name}: Received data: {content}"
    return { state with messageCount := state.messageCount + 1 }
  | Message.Stop => do
    IO.println s!"{state.name}: Stopping"
    return { state with isRunning := false }

-- Actor循环
def actorLoop (state : ActorState) (mailbox : IO.Ref (List Message)) : IO Unit := do
  if !state.isRunning then
    return ()
  else
    let messages ← mailbox.get
    match messages with
    | [] => 
      IO.sleep 100
      actorLoop state mailbox
    | msg :: rest => do
      mailbox.set rest
      let newState ← ActorState.handleMessage state msg
      actorLoop newState mailbox

-- 创建Actor
def createActor (name : String) : IO (IO.Ref (List Message)) := do
  let mailbox ← IO.mkRef ([] : List Message)
  let initialState := { name := name, messageCount := 0, isRunning := true }
  
  -- 启动Actor线程
  IO.asTask (actorLoop initialState mailbox)
  
  return mailbox

-- 发送消息
def sendMessage (mailbox : IO.Ref (List Message)) (msg : Message) : IO Unit := do
  let messages ← mailbox.get
  mailbox.set (msg :: messages)

-- 使用Actor
def actorExample : IO Unit := do
  let actor1 ← createActor "Actor1"
  let actor2 ← createActor "Actor2"
  
  sendMessage actor1 Message.Ping
  sendMessage actor2 (Message.Data "Hello from Actor1")
  sendMessage actor1 Message.Pong
  
  IO.sleep 1000
  
  sendMessage actor1 Message.Stop
  sendMessage actor2 Message.Stop

end ActorPattern
```

### 类型安全Actor

```lean
-- 类型安全Actor
namespace TypeSafeActor

-- 类型化消息
inductive TypedMessage (α : Type) : Type
  | Value : α → TypedMessage α
  | Request : (α → IO Unit) → TypedMessage α

-- 类型化Actor
structure TypedActor (α : Type) where
  state : α
  mailbox : IO.Ref (List (TypedMessage α))

-- 创建类型化Actor
def TypedActor.create {α : Type} (initialState : α) (name : String) : IO (TypedActor α) := do
  let mailbox ← IO.mkRef ([] : List (TypedMessage α))
  let actor := { state := initialState, mailbox := mailbox }
  
  -- 启动处理循环
  IO.asTask (TypedActor.processLoop actor)
  
  return actor

-- 处理循环
def TypedActor.processLoop {α : Type} (actor : TypedActor α) : IO Unit := do
  let messages ← actor.mailbox.get
  match messages with
  | [] => 
    IO.sleep 100
    TypedActor.processLoop actor
  | msg :: rest => do
    actor.mailbox.set rest
    match msg with
    | TypedMessage.Value value => 
      IO.println s!"Received value: {value}"
    | TypedMessage.Request handler => 
      handler actor.state
    TypedActor.processLoop actor

-- 发送消息
def TypedActor.send {α : Type} (actor : TypedActor α) (msg : TypedMessage α) : IO Unit := do
  let messages ← actor.mailbox.get
  actor.mailbox.set (msg :: messages)

-- 使用类型化Actor
def counterActor : IO Unit := do
  let actor ← TypedActor.create 0 "Counter"
  
  TypedActor.send actor (TypedMessage.Value 42)
  TypedActor.send actor (TypedMessage.Request (fun state => 
    IO.println s!"Current state: {state}"))
  
  IO.sleep 1000

end TypeSafeActor
```

## ⚡ Future模式

### 基础Future

```lean
-- Future模式
namespace FuturePattern

-- Future类型
structure Future (α : Type) where
  task : IO.Task α
  completed : IO.Ref Bool

-- 创建Future
def Future.create {α : Type} (computation : IO α) : IO (Future α) := do
  let task ← IO.asTask computation
  let completed ← IO.mkRef false
  return { task := task, completed := completed }

-- 获取结果
def Future.get {α : Type} (future : Future α) : IO α := do
  let result ← IO.wait future.task
  future.completed.set true
  return result

-- 检查完成状态
def Future.isCompleted {α : Type} (future : Future α) : IO Bool :=
  future.completed.get

-- 组合Future
def Future.map {α β : Type} (f : α → β) (future : Future α) : IO (Future β) := do
  let computation := do
    let result ← Future.get future
    return f result
  Future.create computation

def Future.flatMap {α β : Type} (f : α → IO β) (future : Future α) : IO (Future β) := do
  let computation := do
    let result ← Future.get future
    f result
  Future.create computation

-- 并行执行
def Future.parallel {α β : Type} (f1 : IO α) (f2 : IO β) : IO (Future (α × β)) := do
  let future1 ← Future.create f1
  let future2 ← Future.create f2
  
  let computation := do
    let result1 ← Future.get future1
    let result2 ← Future.get future2
    return (result1, result2)
  
  Future.create computation

-- 使用Future
def futureExample : IO Unit := do
  let future1 ← Future.create (do IO.sleep 1000; return "Hello")
  let future2 ← Future.create (do IO.sleep 500; return "World")
  
  let combined ← Future.parallel (Future.get future1) (Future.get future2)
  let result ← Future.get combined
  
  IO.println s!"Result: {result.1} {result.2}"

end FuturePattern
```

### 高级Future

```lean
-- 高级Future
namespace AdvancedFuture

-- Future组合器
def Future.sequence {α : Type} (futures : List (Future α)) : IO (Future (List α)) := do
  let computation := do
    List.mapM Future.get futures
  Future.create computation

def Future.traverse {α β : Type} (f : α → IO β) (items : List α) : IO (Future (List β)) := do
  let futures ← List.mapM (fun x => Future.create (f x)) items
  Future.sequence futures

-- 超时Future
def Future.withTimeout {α : Type} (timeout : Nat) (future : Future α) : IO (Option α) := do
  let computation := do
    let timeoutTask ← IO.asTask (IO.sleep timeout)
    let resultTask ← IO.asTask (Future.get future)
    
    let timeoutResult ← IO.wait timeoutTask
    let result ← IO.wait resultTask
    
    return some result
  
  Future.create computation

-- 错误处理Future
def Future.catch {α : Type} (future : Future α) (handler : String → IO α) : IO (Future α) := do
  let computation := do
    try
      Future.get future
    catch e =>
      handler e.toString
  Future.create computation

-- 使用高级Future
def advancedFutureExample : IO Unit := do
  let computations := 
    [ Future.create (do IO.sleep 100; return 1)
    , Future.create (do IO.sleep 200; return 2)
    , Future.create (do IO.sleep 300; return 3) ]
  
  let sequenceFuture ← Future.sequence computations
  let result ← Future.get sequenceFuture
  
  IO.println s!"Sequence result: {result}"

end AdvancedFuture
```

## 🔄 STM模式 (Software Transactional Memory)

### 基础STM

```lean
-- STM模式
namespace STMPattern

-- STM变量
structure STMVar (α : Type) where
  value : IO.Ref α

-- 创建STM变量
def STMVar.new {α : Type} (initialValue : α) : IO (STMVar α) := do
  let ref ← IO.mkRef initialValue
  return { value := ref }

-- STM操作
def STMVar.read {α : Type} (var : STMVar α) : IO α :=
  var.value.get

def STMVar.write {α : Type} (var : STMVar α) (newValue : α) : IO Unit :=
  var.value.set newValue

def STMVar.modify {α : Type} (var : STMVar α) (f : α → α) : IO Unit := do
  let current ← var.value.get
  var.value.set (f current)

-- 原子操作
def STMVar.atomic {α : Type} (var : STMVar α) (operation : α → α) : IO α := do
  let current ← var.value.get
  let newValue := operation current
  var.value.set newValue
  return newValue

-- 使用STM
def stmExample : IO Unit := do
  let counter ← STMVar.new 0
  
  -- 并发修改
  let task1 ← IO.asTask (do
    STMVar.modify counter (· + 1)
    STMVar.modify counter (· + 1))
  
  let task2 ← IO.asTask (do
    STMVar.modify counter (· * 2))
  
  IO.wait task1
  IO.wait task2
  
  let finalValue ← STMVar.read counter
  IO.println s!"Final counter value: {finalValue}"

end STMPattern
```

### 高级STM

```lean
-- 高级STM
namespace AdvancedSTM

-- STM事务
structure STMTransaction (α : Type) where
  operations : IO (List (IO Unit))
  result : α

-- 事务构建器
def STMTransaction.pure {α : Type} (value : α) : STMTransaction α :=
  { operations := pure [], result := value }

def STMTransaction.bind {α β : Type} (tx : STMTransaction α) 
  (f : α → STMTransaction β) : STMTransaction β :=
  { operations := do
      let ops1 ← tx.operations
      let tx2 := f tx.result
      let ops2 ← tx2.operations
      return ops1 ++ ops2
    result := (f tx.result).result }

-- 事务执行
def STMTransaction.execute {α : Type} (tx : STMTransaction α) : IO α := do
  let operations ← tx.operations
  List.forM operations (fun op => op)
  return tx.result

-- STM变量操作
def STMVar.readSTM {α : Type} (var : STMVar α) : STMTransaction α :=
  { operations := pure [], result := var.value.get }

def STMVar.writeSTM {α : Type} (var : STMVar α) (value : α) : STMTransaction Unit :=
  { operations := pure [var.value.set value], result := () }

-- 使用高级STM
def advancedSTMExample : IO Unit := do
  let account1 ← STMVar.new 100
  let account2 ← STMVar.new 50
  
  let transfer := do
    let balance1 ← STMVar.readSTM account1
    let balance2 ← STMVar.readSTM account2
    
    if balance1 >= 30 then
      STMVar.writeSTM account1 (balance1 - 30)
      STMVar.writeSTM account2 (balance2 + 30)
    else
      STMTransaction.pure ()
  
  STMTransaction.execute transfer
  
  let final1 ← STMVar.read account1
  let final2 ← STMVar.read account2
  
  IO.println s!"Account1: {final1}, Account2: {final2}"

end AdvancedSTM
```

## 🔄 并发集合模式

### 并发队列

```lean
-- 并发集合模式
namespace ConcurrentCollections

-- 并发队列
structure ConcurrentQueue (α : Type) where
  items : IO.Ref (List α)

-- 创建队列
def ConcurrentQueue.new {α : Type} : IO (ConcurrentQueue α) := do
  let ref ← IO.mkRef ([] : List α)
  return { items := ref }

-- 队列操作
def ConcurrentQueue.enqueue {α : Type} (queue : ConcurrentQueue α) (item : α) : IO Unit := do
  let items ← queue.items.get
  queue.items.set (item :: items)

def ConcurrentQueue.dequeue {α : Type} (queue : ConcurrentQueue α) : IO (Option α) := do
  let items ← queue.items.get
  match items with
  | [] => return none
  | x :: xs => do
    queue.items.set xs
    return some x

def ConcurrentQueue.isEmpty {α : Type} (queue : ConcurrentQueue α) : IO Bool := do
  let items ← queue.items.get
  return items.isEmpty

-- 并发映射
structure ConcurrentMap (α β : Type) where
  data : IO.Ref (List (α × β))

-- 创建映射
def ConcurrentMap.new {α β : Type} : IO (ConcurrentMap α β) := do
  let ref ← IO.mkRef ([] : List (α × β))
  return { data := ref }

-- 映射操作
def ConcurrentMap.put {α β : Type} (map : ConcurrentMap α β) (key : α) (value : β) : IO Unit := do
  let data ← map.data.get
  let filtered := List.filter (fun (k, _) => k != key) data
  map.data.set ((key, value) :: filtered)

def ConcurrentMap.get {α β : Type} (map : ConcurrentMap α β) (key : α) : IO (Option β) := do
  let data ← map.data.get
  match List.find? data (fun (k, _) => k == key) with
  | some (_, value) => return some value
  | none => return none

-- 使用并发集合
def concurrentCollectionsExample : IO Unit := do
  let queue ← ConcurrentQueue.new
  let map ← ConcurrentMap.new
  
  -- 生产者
  let producer ← IO.asTask (do
    for i in [0:10] do
      ConcurrentQueue.enqueue queue i
      ConcurrentMap.put map i (s!"Value {i}")
      IO.sleep 100)
  
  -- 消费者
  let consumer ← IO.asTask (do
    for _ in [0:10] do
      let item ← ConcurrentQueue.dequeue queue
      match item with
      | some i => 
        let value ← ConcurrentMap.get map i
        IO.println s!"Consumed: {i} -> {value}"
      | none => IO.sleep 50)
  
  IO.wait producer
  IO.wait consumer

end ConcurrentCollections
```

## 🎯 应用场景

### 1. 并发服务器

```lean
-- 并发服务器
namespace ConcurrentServer

-- 请求类型
inductive Request : Type
  | Get : String → Request
  | Post : String → String → Request
  | Delete : String → Request

-- 响应类型
inductive Response : Type
  | Success : String → Response
  | Error : String → Response

-- 服务器状态
structure ServerState where
  data : IO.Ref (List (String × String))
  requestCount : IO.Ref Nat

-- 请求处理器
def handleRequest (state : ServerState) (request : Request) : IO Response :=
  match request with
  | Request.Get key => do
    let data ← state.data.get
    match List.find? data (fun (k, _) => k == key) with
    | some (_, value) => return Response.Success value
    | none => return Response.Error "Key not found"
  
  | Request.Post key value => do
    let data ← state.data.get
    let filtered := List.filter (fun (k, _) => k != key) data
    state.data.set ((key, value) :: filtered)
    let count ← state.requestCount.get
    state.requestCount.set (count + 1)
    return Response.Success "OK"
  
  | Request.Delete key => do
    let data ← state.data.get
    let filtered := List.filter (fun (k, _) => k != key) data
    state.data.set filtered
    return Response.Success "Deleted"

-- 服务器循环
def serverLoop (state : ServerState) (mailbox : IO.Ref (List Request)) : IO Unit := do
  let requests ← mailbox.get
  match requests with
  | [] => 
    IO.sleep 10
    serverLoop state mailbox
  | request :: rest => do
    mailbox.set rest
    let response ← handleRequest state request
    IO.println s!"Response: {response}"
    serverLoop state mailbox

-- 启动服务器
def startServer : IO (IO.Ref (List Request)) := do
  let state := { 
    data := (← IO.mkRef []), 
    requestCount := (← IO.mkRef 0) 
  }
  let mailbox ← IO.mkRef ([] : List Request)
  
  IO.asTask (serverLoop state mailbox)
  
  return mailbox

end ConcurrentServer
```

### 2. 并行计算

```lean
-- 并行计算
namespace ParallelComputation

-- 并行映射
def parallelMap {α β : Type} (f : α → β) (items : List α) : IO (List β) := do
  let futures ← List.mapM (fun x => Future.create (pure (f x))) items
  let results ← Future.sequence futures
  Future.get results

-- 并行归约
def parallelReduce {α : Type} (f : α → α → α) (init : α) (items : List α) : IO α := do
  if items.length <= 1 then
    return List.foldr f init items
  else
    let mid := items.length / 2
    let (left, right) := List.splitAt mid items
    
    let leftFuture ← Future.create (parallelReduce f init left)
    let rightFuture ← Future.create (parallelReduce f init right)
    
    let leftResult ← Future.get leftFuture
    let rightResult ← Future.get rightFuture
    
    return f leftResult rightResult

-- 使用并行计算
def parallelExample : IO Unit := do
  let numbers := List.range 1000
  
  let doubled ← parallelMap (· * 2) numbers
  let sum ← parallelReduce (· + ·) 0 numbers
  
  IO.println s!"Sum: {sum}"

end ParallelComputation
```

## 🚀 最佳实践

### 1. 设计原则

- **不可变性**: 优先使用不可变数据结构
- **类型安全**: 充分利用类型系统
- **组合性**: 使用可组合的并发原语

### 2. 实现策略

- **渐进式**: 从简单模式开始
- **模块化**: 清晰的模块边界
- **可测试性**: 便于验证和测试

### 3. 性能考虑

- **内存效率**: 注意内存使用模式
- **并发控制**: 合理使用锁和同步
- **资源管理**: 及时释放资源

---

**下一节**: [形式化模式](./08-Formal-Patterns.md)

**相关链接**:

- [类型级模式](./06-Type-Level-Patterns.md)
- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
