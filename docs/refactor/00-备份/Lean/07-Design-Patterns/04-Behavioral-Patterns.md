# Lean 行为型设计模式

## 🎯 概述

行为型设计模式关注对象间的通信和职责分配，在Lean中通过类型系统、Monad和函数式编程实现灵活的行为组合。

## 👁️ 观察者模式 (Observer Pattern)

### 基础观察者

```lean
-- 观察者模式
namespace Observer

-- 观察者接口
class Observer (α : Type) where
  update : String → α → α

-- 主题接口
class Subject (α : Type) where
  attach : Observer β → α → α
  detach : Observer β → α → α
  notify : String → α → IO α

-- 具体观察者
structure NewsObserver where
  name : String

instance : Observer NewsObserver where
  update news observer := { observer with name := s!"{observer.name} (updated)" }

-- 具体主题
structure NewsSubject where
  observers : List (String → IO Unit)
  news : String

instance : Subject NewsSubject where
  attach observer subject := 
    { subject with observers := observer :: subject.observers }
  
  detach observer subject := 
    { subject with observers := List.filter (· != observer) subject.observers }
  
  notify news subject := do
    List.forM subject.observers (fun obs => obs news)
    return { subject with news := news }

-- 使用观察者
def createSubject : NewsSubject :=
  { observers := [], news := "" }

def observer1 := fun news => IO.println s!"Observer 1: {news}"
def observer2 := fun news => IO.println s!"Observer 2: {news}"

def subject1 := Subject.attach observer1 createSubject
def subject2 := Subject.attach observer2 subject1
def result ← Subject.notify "Breaking news!" subject2
```

### 类型安全观察者

```lean
-- 类型安全观察者
namespace TypeSafeObserver

-- 事件类型
inductive Event
  | UserCreated : String → Event
  | UserUpdated : String → Event
  | UserDeleted : String → Event

-- 类型安全观察者
class TypeSafeObserver (α : Type) where
  handleEvent : Event → α → α

-- 具体观察者
structure UserObserver where
  name : String
  eventCount : Nat

instance : TypeSafeObserver UserObserver where
  handleEvent event observer := 
    { observer with eventCount := observer.eventCount + 1 }

-- 类型安全主题
structure TypeSafeSubject where
  observers : List (Event → IO Unit)
  state : String

instance : Subject TypeSafeSubject where
  attach observer subject := 
    { subject with observers := observer :: subject.observers }
  
  detach observer subject := 
    { subject with observers := List.filter (· != observer) subject.observers }
  
  notify event subject := do
    List.forM subject.observers (fun obs => obs event)
    return { subject with state := toString event }

end TypeSafeObserver
```

## 🎯 策略模式 (Strategy Pattern)

### 算法策略

```lean
-- 策略模式
namespace Strategy

-- 策略接口
class Strategy (α : Type) where
  algorithm : List Int → Int

-- 具体策略
structure BubbleSortStrategy where

instance : Strategy BubbleSortStrategy where
  algorithm list := 
    let sorted := List.sort list
    List.length sorted

structure QuickSortStrategy where

instance : Strategy QuickSortStrategy where
  algorithm list := 
    let sorted := List.sort list
    List.sum sorted

structure MergeSortStrategy where

instance : Strategy MergeSortStrategy where
  algorithm list := 
    let sorted := List.sort list
    List.maximum sorted

-- 上下文
structure Context where
  strategy : Strategy
  data : List Int

def Context.execute (context : Context) : Int :=
  Strategy.algorithm context.strategy context.data

-- 使用策略
def data := [3, 1, 4, 1, 5, 9, 2, 6]

def bubbleContext := { strategy := BubbleSortStrategy {}, data := data }
def quickContext := { strategy := QuickSortStrategy {}, data := data }
def mergeContext := { strategy := MergeSortStrategy {}, data := data }

def bubbleResult := Context.execute bubbleContext
def quickResult := Context.execute quickContext
def mergeResult := Context.execute mergeContext
```

### 支付策略

```lean
-- 支付策略
namespace PaymentStrategy

-- 支付策略接口
class PaymentStrategy (α : Type) where
  pay : α → Float → String

-- 具体支付策略
structure CreditCardStrategy where
  cardNumber : String

instance : PaymentStrategy CreditCardStrategy where
  pay strategy amount := s!"Paid ${amount} with credit card {strategy.cardNumber}"

structure PayPalStrategy where
  email : String

instance : PaymentStrategy PayPalStrategy where
  pay strategy amount := s!"Paid ${amount} with PayPal {strategy.email}"

structure BitcoinStrategy where
  walletAddress : String

instance : PaymentStrategy BitcoinStrategy where
  pay strategy amount := s!"Paid ${amount} with Bitcoin {strategy.walletAddress}"

-- 支付处理器
structure PaymentProcessor where
  strategy : PaymentStrategy
  amount : Float

def PaymentProcessor.process (processor : PaymentProcessor) : String :=
  PaymentStrategy.pay processor.strategy processor.amount

-- 使用支付策略
def creditCard := { cardNumber := "1234-5678-9012-3456" }
def paypal := { email := "user@example.com" }
def bitcoin := { walletAddress := "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa" }

def processor1 := { strategy := creditCard, amount := 100.0 }
def processor2 := { strategy := paypal, amount := 50.0 }
def processor3 := { strategy := bitcoin, amount := 25.0 }

def result1 := PaymentProcessor.process processor1
def result2 := PaymentProcessor.process processor2
def result3 := PaymentProcessor.process processor3
```

## 📋 命令模式 (Command Pattern)

### 基础命令

```lean
-- 命令模式
namespace Command

-- 命令接口
class Command (α : Type) where
  execute : α → String
  undo : α → String

-- 具体命令
structure LightOnCommand where
  lightId : String

instance : Command LightOnCommand where
  execute command := s!"Light {command.lightId} turned ON"
  undo command := s!"Light {command.lightId} turned OFF"

structure LightOffCommand where
  lightId : String

instance : Command LightOffCommand where
  execute command := s!"Light {command.lightId} turned OFF"
  undo command := s!"Light {command.lightId} turned ON"

-- 调用者
structure RemoteControl where
  commands : List Command

def RemoteControl.pressButton (remote : RemoteControl) (index : Nat) : String :=
  match List.get? remote.commands index with
  | some command => Command.execute command
  | none => "No command at this slot"

def RemoteControl.addCommand (remote : RemoteControl) (command : Command) : RemoteControl :=
  { remote with commands := command :: remote.commands }

-- 使用命令
def lightOn := { lightId := "Living Room" }
def lightOff := { lightId := "Living Room" }

def remote := { commands := [] }
def remote1 := RemoteControl.addCommand remote lightOn
def remote2 := RemoteControl.addCommand remote1 lightOff

def result1 := RemoteControl.pressButton remote2 0
def result2 := RemoteControl.pressButton remote2 1
```

### 宏命令

```lean
-- 宏命令
namespace MacroCommand

-- 宏命令
structure MacroCommand where
  commands : List Command

instance : Command MacroCommand where
  execute macro := 
    let results := List.map Command.execute macro.commands
    s!"Macro executed: {results}"
  
  undo macro := 
    let results := List.map Command.undo macro.commands
    s!"Macro undone: {results}"

-- 创建宏命令
def createPartyMode : MacroCommand :=
  { commands := 
    [ { lightId := "Living Room" } : LightOnCommand
    , { lightId := "Kitchen" } : LightOnCommand
    , { lightId := "Bedroom" } : LightOnCommand ] }

def createSleepMode : MacroCommand :=
  { commands := 
    [ { lightId := "Living Room" } : LightOffCommand
    , { lightId := "Kitchen" } : LightOffCommand
    , { lightId := "Bedroom" } : LightOffCommand ] }

-- 使用宏命令
def partyMode := createPartyMode
def sleepMode := createSleepMode

def partyResult := Command.execute partyMode
def sleepResult := Command.execute sleepMode
```

## 🔄 状态模式 (State Pattern)

### 状态机

```lean
-- 状态模式
namespace State

-- 状态接口
class State (α : Type) where
  handle : α → String

-- 具体状态
structure IdleState where

instance : State IdleState where
  handle state := "System is idle"

structure WorkingState where

instance : State WorkingState where
  handle state := "System is working"

structure ErrorState where
  errorMessage : String

instance : State ErrorState where
  handle state := s!"System error: {state.errorMessage}"

-- 上下文
structure Context where
  state : State
  data : String

def Context.request (context : Context) : String :=
  State.handle context.state

def Context.changeState (context : Context) (newState : State) : Context :=
  { context with state := newState }

-- 使用状态
def idleState := IdleState {}
def workingState := WorkingState {}
def errorState := { errorMessage := "Connection failed" }

def context := { state := idleState, data := "Initial data" }

def result1 := Context.request context
def context2 := Context.changeState context workingState
def result2 := Context.request context2
def context3 := Context.changeState context2 errorState
def result3 := Context.request context3
```

## 🔗 责任链模式 (Chain of Responsibility)

### 处理链

```lean
-- 责任链模式
namespace ChainOfResponsibility

-- 处理器接口
class Handler (α : Type) where
  handle : α → String → Option String
  setNext : Handler β → α → α

-- 具体处理器
structure ConsoleHandler where
  next : Option Handler

instance : Handler ConsoleHandler where
  handle handler request := 
    if request.contains "console" then
      some s!"ConsoleHandler: {request}"
    else
      none
  
  setNext next handler := 
    { handler with next := some next }

structure FileHandler where
  next : Option Handler

instance : Handler FileHandler where
  handle handler request := 
    if request.contains "file" then
      some s!"FileHandler: {request}"
    else
      none
  
  setNext next handler := 
    { handler with next := some next }

structure EmailHandler where
  next : Option Handler

instance : Handler EmailHandler where
  handle handler request := 
    if request.contains "email" then
      some s!"EmailHandler: {request}"
    else
      some s!"EmailHandler: Default handler for {request}"
  
  setNext next handler := 
    { handler with next := some next }

-- 使用责任链
def consoleHandler := { next := none }
def fileHandler := { next := none }
def emailHandler := { next := none }

def chain1 := Handler.setNext fileHandler consoleHandler
def chain2 := Handler.setNext emailHandler chain1

def result1 := Handler.handle chain2 "console request"
def result2 := Handler.handle chain2 "file request"
def result3 := Handler.handle chain2 "email request"
def result4 := Handler.handle chain2 "unknown request"
```

## 🎯 模板方法模式 (Template Method)

### 算法模板

```lean
-- 模板方法模式
namespace TemplateMethod

-- 抽象类
class AbstractClass (α : Type) where
  templateMethod : α → String
  primitiveOperation1 : α → String
  primitiveOperation2 : α → String
  hook : α → String

-- 具体实现
structure ConcreteClass where
  name : String

instance : AbstractClass ConcreteClass where
  templateMethod concrete := 
    let step1 := AbstractClass.primitiveOperation1 concrete
    let step2 := AbstractClass.primitiveOperation2 concrete
    let hook := AbstractClass.hook concrete
    s!"Template: {step1} + {step2} + {hook}"
  
  primitiveOperation1 concrete := s!"Operation1: {concrete.name}"
  primitiveOperation2 concrete := s!"Operation2: {concrete.name}"
  hook concrete := s!"Hook: {concrete.name}"

-- 使用模板方法
def concrete := { name := "MyClass" }
def result := AbstractClass.templateMethod concrete
```

## 🎯 应用场景

### 1. 事件处理

```lean
-- 事件处理系统
namespace EventHandling

-- 事件类型
inductive Event
  | UserLogin : String → Event
  | UserLogout : String → Event
  | DataUpdate : String → Event

-- 事件处理器
class EventHandler (α : Type) where
  handle : Event → α → α

-- 日志处理器
structure LoggingHandler where
  logLevel : String

instance : EventHandler LoggingHandler where
  handle event handler := 
    { handler with logLevel := s!"{handler.logLevel} (processed)" }

-- 通知处理器
structure NotificationHandler where
  notifications : List String

instance : EventHandler NotificationHandler where
  handle event handler := 
    { handler with notifications := toString event :: handler.notifications }

end EventHandling
```

### 2. 算法选择

```lean
-- 算法选择系统
namespace AlgorithmSelection

-- 排序策略
class SortStrategy (α : Type) where
  sort : List Int → List Int

-- 冒泡排序
structure BubbleSort where

instance : SortStrategy BubbleSort where
  sort list := List.sort list

-- 快速排序
structure QuickSort where

instance : SortStrategy QuickSort where
  sort list := List.sort list

-- 排序上下文
structure SortContext where
  strategy : SortStrategy
  data : List Int

def SortContext.execute (context : SortContext) : List Int :=
  SortStrategy.sort context.strategy context.data

end AlgorithmSelection
```

## 🚀 最佳实践

### 1. 设计原则

- **单一职责**: 每个模式只负责一个行为
- **开闭原则**: 对扩展开放，对修改封闭
- **依赖倒置**: 依赖抽象而非具体实现

### 2. 实现策略

- **类型安全**: 充分利用类型系统
- **不可变性**: 优先使用不可变对象
- **函数式**: 利用函数式编程特性

### 3. 性能考虑

- **内存效率**: 注意内存使用模式
- **计算效率**: 选择合适的算法策略
- **并发安全**: 考虑并发访问情况

---

**下一节**: [函数式模式](./05-Functional-Patterns.md)

**相关链接**:

- [结构型模式](./03-Structural-Patterns.md)
- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
