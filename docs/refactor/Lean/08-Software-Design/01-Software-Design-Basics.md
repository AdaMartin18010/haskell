# Lean 软件设计基础

## 🎯 概述

Lean的软件设计基于数学理论和形式化方法，强调类型安全、不可变性和证明驱动开发。本章介绍Lean中的软件设计基础概念、原则和方法。

## 🏗️ 软件设计层次

### 1. 架构设计层

```lean
-- 系统架构：分层设计
namespace SystemArchitecture

-- 表示层
structure View where
  render : Data → String

-- 业务逻辑层
structure BusinessLogic where
  process : Input → Output

-- 数据访问层
structure DataAccess where
  query : Query → Result

-- 系统组合
structure System where
  view : View
  logic : BusinessLogic
  data : DataAccess

end SystemArchitecture
```

### 2. 模块设计层

```lean
-- 模块化设计：功能分离
namespace ModuleDesign

-- 用户模块
namespace User
  structure User where
    id : Nat
    name : String
    email : String

  def createUser (name email : String) : User :=
    { id := 0, name := name, email := email }

  def updateUser (user : User) (newName : String) : User :=
    { user with name := newName }
end User

-- 订单模块
namespace Order
  structure Order where
    id : Nat
    userId : Nat
    items : List String
    total : Float

  def createOrder (userId : Nat) (items : List String) : Order :=
    { id := 0, userId := userId, items := items, total := 0.0 }
end Order

end ModuleDesign
```

### 3. 接口设计层

```lean
-- 接口设计：抽象和契约
namespace InterfaceDesign

-- 抽象接口
class Repository (α : Type) where
  find : Nat → Option α
  save : α → Bool
  delete : Nat → Bool

-- 具体实现
structure UserRepository where
  users : List User

instance : Repository User where
  find id := List.find? (fun u => u.id == id) users
  save user := true -- 简化实现
  delete id := true -- 简化实现

-- 服务接口
class UserService where
  createUser : String → String → User
  getUser : Nat → Option User
  updateUser : Nat → String → Option User

end InterfaceDesign
```

## 🔧 设计原则

### 1. 单一职责原则 (SRP)

```lean
-- 每个模块只负责一个功能
namespace SingleResponsibility

-- 用户管理
namespace UserManagement
  def createUser (name email : String) : User := sorry
  def updateUser (user : User) (newName : String) : User := sorry
  def deleteUser (userId : Nat) : Bool := sorry
end UserManagement

-- 用户验证
namespace UserValidation
  def validateEmail (email : String) : Bool := sorry
  def validateName (name : String) : Bool := sorry
end UserValidation

-- 用户权限
namespace UserAuthorization
  def hasPermission (user : User) (resource : String) : Bool := sorry
  def grantPermission (user : User) (resource : String) : User := sorry
end UserAuthorization

end SingleResponsibility
```

### 2. 开闭原则 (OCP)

```lean
-- 对扩展开放，对修改封闭
namespace OpenClosed

-- 基础接口
class PaymentMethod where
  process : Float → Bool

-- 具体实现
structure CreditCard where
  number : String
  expiry : String

instance : PaymentMethod CreditCard where
  process amount := true -- 简化实现

structure PayPal where
  email : String

instance : PaymentMethod PayPal where
  process amount := true -- 简化实现

-- 支付处理器：无需修改即可支持新的支付方式
def processPayment {α : Type} [PaymentMethod α] (method : α) (amount : Float) : Bool :=
  PaymentMethod.process method amount

end OpenClosed
```

### 3. 里氏替换原则 (LSP)

```lean
-- 子类型必须可替换父类型
namespace LiskovSubstitution

-- 基础类型
class Animal where
  makeSound : String

-- 子类型
structure Dog where
  name : String

instance : Animal Dog where
  makeSound := "Woof!"

structure Cat where
  name : String

instance : Animal Cat where
  makeSound := "Meow!"

-- 使用基类，可接受任何子类型
def animalSound {α : Type} [Animal α] (animal : α) : String :=
  Animal.makeSound animal

end LiskovSubstitution
```

### 4. 接口隔离原则 (ISP)

```lean
-- 客户端不应依赖它不使用的接口
namespace InterfaceSegregation

-- 细粒度接口
class Readable (α : Type) where
  read : α → String

class Writable (α : Type) where
  write : α → String → α

class Deletable (α : Type) where
  delete : α → Bool

-- 组合接口
class Repository (α : Type) [Readable α] [Writable α] [Deletable α] where
  find : Nat → Option α
  save : α → Bool
  remove : Nat → Bool

end InterfaceSegregation
```

### 5. 依赖倒置原则 (DIP)

```lean
-- 依赖抽象而非具体实现
namespace DependencyInversion

-- 抽象接口
class Logger where
  log : String → IO Unit

class Database where
  query : String → IO (List String)

-- 具体实现
structure FileLogger where
  filename : String

instance : Logger FileLogger where
  log message := IO.println s!"[FILE] {message}"

structure SQLDatabase where
  connection : String

instance : Database SQLDatabase where
  query sql := IO.println s!"[SQL] {sql}"; return []

-- 业务逻辑依赖抽象
structure UserService (logger : Logger) (db : Database) where
  createUser : String → IO User
  getUser : Nat → IO (Option User)

end DependencyInversion
```

## 🏛️ 架构模式

### 1. 分层架构

```lean
-- 经典三层架构
namespace LayeredArchitecture

-- 表示层
structure PresentationLayer where
  render : Data → String
  handleInput : String → Command

-- 业务逻辑层
structure BusinessLayer where
  processCommand : Command → Result
  validateData : Data → Bool

-- 数据访问层
structure DataLayer where
  save : Data → Bool
  load : Query → Option Data

-- 系统组合
structure LayeredSystem where
  presentation : PresentationLayer
  business : BusinessLayer
  data : DataLayer

end LayeredArchitecture
```

### 2. 微服务架构

```lean
-- 微服务设计
namespace Microservices

-- 用户服务
namespace UserService
  structure UserService where
    createUser : String → String → User
    getUser : Nat → Option User
    updateUser : Nat → String → Option User
end UserService

-- 订单服务
namespace OrderService
  structure OrderService where
    createOrder : Nat → List String → Order
    getOrder : Nat → Option Order
    updateOrder : Nat → List String → Option Order
end OrderService

-- 支付服务
namespace PaymentService
  structure PaymentService where
    processPayment : Nat → Float → Bool
    refundPayment : Nat → Float → Bool
end PaymentService

end Microservices
```

### 3. 事件驱动架构

```lean
-- 事件驱动设计
namespace EventDriven

-- 事件定义
inductive Event
  | UserCreated : User → Event
  | OrderPlaced : Order → Event
  | PaymentProcessed : Payment → Event

-- 事件处理器
class EventHandler (α : Type) where
  handle : Event → α → α

-- 事件总线
structure EventBus where
  handlers : List (Event → IO Unit)
  publish : Event → IO Unit
  subscribe : (Event → IO Unit) → IO Unit

end EventDriven
```

## 🔄 设计模式应用

### 1. 工厂模式

```lean
-- 工厂模式：创建对象
namespace FactoryPattern

-- 产品接口
class Product where
  name : String
  price : Float

-- 具体产品
structure Book where
  title : String
  author : String
  price : Float

instance : Product Book where
  name := Book.title
  price := Book.price

structure Electronics where
  brand : String
  model : String
  price : Float

instance : Product Electronics where
  name := s!"{Electronics.brand} {Electronics.model}"
  price := Electronics.price

-- 工厂
class ProductFactory where
  createBook : String → String → Float → Book
  createElectronics : String → String → Float → Electronics

end FactoryPattern
```

### 2. 观察者模式

```lean
-- 观察者模式：事件通知
namespace ObserverPattern

-- 观察者接口
class Observer (α : Type) where
  update : String → α → α

-- 主题接口
class Subject (α : Type) where
  attach : Observer α → α → α
  detach : Observer α → α → α
  notify : String → α → α

-- 具体实现
structure NewsSubject where
  observers : List (String → IO Unit)
  news : String

instance : Subject NewsSubject where
  attach observer subject := { subject with observers := observer :: subject.observers }
  detach observer subject := { subject with observers := List.filter (· != observer) subject.observers }
  notify news subject := { subject with news := news }

end ObserverPattern
```

## 📊 设计质量评估

### 1. 内聚性

- **功能内聚**: 模块内功能相关
- **数据内聚**: 模块操作相同数据
- **时间内聚**: 模块在相同时间执行

### 2. 耦合性

- **数据耦合**: 通过参数传递数据
- **控制耦合**: 一个模块控制另一个模块
- **外部耦合**: 依赖外部环境

### 3. 可维护性

- **可读性**: 代码易于理解
- **可修改性**: 易于修改和扩展
- **可测试性**: 易于测试和验证

## 🚀 最佳实践

### 1. 设计策略

- **渐进式设计**: 从简单开始，逐步复杂化
- **原型设计**: 快速构建原型验证想法
- **重构**: 持续改进设计质量

### 2. 实现原则

- **类型安全**: 充分利用类型系统
- **不可变性**: 优先使用不可变数据
- **纯函数**: 避免副作用

### 3. 质量保证

- **代码审查**: 人工检查设计质量
- **自动化测试**: 验证设计正确性
- **形式化验证**: 证明关键性质

---

**下一节**: [架构设计](./02-Architecture-Design.md)

**相关链接**:

- [设计模式](../07-Design-Patterns/)
- [应用模型](../09-Application-Models/)
- [形式模型](../10-Formal-Models/)
- [高级架构](../12-Advanced-Architecture/)
