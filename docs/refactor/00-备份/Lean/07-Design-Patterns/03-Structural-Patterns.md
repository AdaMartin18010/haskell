# Lean 结构型设计模式

## 🎯 概述

结构型设计模式关注类和对象的组合，在Lean中通过类型系统、类型类和依赖类型实现灵活的对象结构组合。

## 🔌 适配器模式 (Adapter Pattern)

### 接口适配器

```lean
-- 适配器模式
namespace Adapter

-- 目标接口
class Target (α : Type) where
  request : α → String

-- 被适配的类
structure Adaptee where
  specificRequest : String

-- 适配器
structure Adapter where
  adaptee : Adaptee

instance : Target Adapter where
  request adapter := 
    let specific := adapter.adaptee.specificRequest
    s!"Adapter: {specific}"

-- 使用适配器
def useTarget {α : Type} [Target α] (target : α) : String :=
  Target.request target

def adaptee := { specificRequest := "Special request" }
def adapter := { adaptee := adaptee }
def result := useTarget adapter
```

### 类适配器

```lean
-- 类适配器
namespace ClassAdapter

-- 旧接口
class OldInterface where
  oldMethod : String

-- 新接口
class NewInterface where
  newMethod : String

-- 适配器类
structure ClassAdapter where
  oldInterface : OldInterface

instance : NewInterface ClassAdapter where
  newMethod adapter := 
    let old := OldInterface.oldMethod adapter.oldInterface
    s!"Adapted: {old}"

-- 使用
def oldImpl : OldInterface where
  oldMethod := "Old implementation"

def adapter := { oldInterface := oldImpl }
def result := NewInterface.newMethod adapter
```

## 🎨 装饰器模式 (Decorator Pattern)

### 基础装饰器

```lean
-- 装饰器模式
namespace Decorator

-- 组件接口
class Component (α : Type) where
  operation : α → String

-- 具体组件
structure ConcreteComponent where
  name : String

instance : Component ConcreteComponent where
  operation component := s!"ConcreteComponent: {component.name}"

-- 装饰器基类
structure BaseDecorator (α : Type) where
  component : α

instance {α : Type} [Component α] : Component (BaseDecorator α) where
  operation decorator := 
    let base := Component.operation decorator.component
    s!"BaseDecorator({base})"

-- 具体装饰器
structure ConcreteDecoratorA (α : Type) where
  baseDecorator : BaseDecorator α

instance {α : Type} [Component α] : Component (ConcreteDecoratorA α) where
  operation decorator := 
    let base := Component.operation decorator.baseDecorator
    s!"ConcreteDecoratorA({base})"

structure ConcreteDecoratorB (α : Type) where
  baseDecorator : BaseDecorator α

instance {α : Type} [Component α] : Component (ConcreteDecoratorB α) where
  operation decorator := 
    let base := Component.operation decorator.baseDecorator
    s!"ConcreteDecoratorB({base})"

-- 使用装饰器
def component := { name := "Simple Component" }
def decoratedA := { baseDecorator := { component := component } }
def decoratedB := { baseDecorator := { component := decoratedA } }

def result1 := Component.operation component
def result2 := Component.operation decoratedA
def result3 := Component.operation decoratedB
```

### 功能装饰器

```lean
-- 功能装饰器
namespace FunctionalDecorator

-- 日志装饰器
structure LoggingDecorator (α : Type) where
  component : α

instance {α : Type} [Component α] : Component (LoggingDecorator α) where
  operation decorator := 
    let result := Component.operation decorator.component
    s!"[LOG] {result}"

-- 缓存装饰器
structure CachingDecorator (α : Type) where
  component : α
  cache : Option String

instance {α : Type} [Component α] : Component (CachingDecorator α) where
  operation decorator := 
    match decorator.cache with
    | some cached => s!"[CACHED] {cached}"
    | none => 
      let result := Component.operation decorator.component
      s!"[COMPUTED] {result}"

-- 组合装饰器
def createDecoratedComponent (component : ConcreteComponent) : 
  CachingDecorator (LoggingDecorator ConcreteComponent) :=
  { component := { component := component }
    cache := none }

end FunctionalDecorator
```

## 🎭 代理模式 (Proxy Pattern)

### 虚拟代理

```lean
-- 代理模式
namespace Proxy

-- 服务接口
class Service (α : Type) where
  operation : α → String

-- 真实服务
structure RealService where
  name : String

instance : Service RealService where
  operation service := s!"RealService: {service.name}"

-- 虚拟代理
structure VirtualProxy where
  realService : Option RealService

instance : Service VirtualProxy where
  operation proxy := 
    match proxy.realService with
    | some service => Service.operation service
    | none => "VirtualProxy: Service not initialized"

-- 初始化代理
def VirtualProxy.initialize (proxy : VirtualProxy) (name : String) : VirtualProxy :=
  { proxy with realService := some { name := name } }

-- 使用代理
def proxy := { realService := none }
def result1 := Service.operation proxy
def initialized := VirtualProxy.initialize proxy "MyService"
def result2 := Service.operation initialized
```

### 保护代理

```lean
-- 保护代理
namespace ProtectionProxy

-- 用户权限
structure User where
  name : String
  role : String

-- 受保护的服务
structure ProtectedService where
  name : String

instance : Service ProtectedService where
  operation service := s!"ProtectedService: {service.name}"

-- 保护代理
structure ProtectionProxy where
  service : ProtectedService
  user : User

instance : Service ProtectionProxy where
  operation proxy := 
    if proxy.user.role == "admin" then
      Service.operation proxy.service
    else
      "Access denied: Admin role required"

-- 使用保护代理
def adminUser := { name := "Admin", role := "admin" }
def regularUser := { name := "User", role := "user" }
def service := { name := "Sensitive Service" }

def adminProxy := { service := service, user := adminUser }
def userProxy := { service := service, user := regularUser }

def adminResult := Service.operation adminProxy
def userResult := Service.operation userProxy
```

### 缓存代理

```lean
-- 缓存代理
namespace CacheProxy

-- 缓存代理
structure CacheProxy where
  service : RealService
  cache : Option String

instance : Service CacheProxy where
  operation proxy := 
    match proxy.cache with
    | some cached => s!"[CACHED] {cached}"
    | none => 
      let result := Service.operation proxy.service
      s!"[FRESH] {result}"

-- 更新缓存
def CacheProxy.updateCache (proxy : CacheProxy) (value : String) : CacheProxy :=
  { proxy with cache := some value }

-- 清除缓存
def CacheProxy.clearCache (proxy : CacheProxy) : CacheProxy :=
  { proxy with cache := none }

end CacheProxy
```

## 🏗️ 桥接模式 (Bridge Pattern)

### 实现桥接

```lean
-- 桥接模式
namespace Bridge

-- 实现接口
class Implementation (α : Type) where
  operationImpl : α → String

-- 具体实现
structure ConcreteImplementationA where
  name : String

instance : Implementation ConcreteImplementationA where
  operationImpl impl := s!"ConcreteA: {impl.name}"

structure ConcreteImplementationB where
  name : String

instance : Implementation ConcreteImplementationB where
  operationImpl impl := s!"ConcreteB: {impl.name}"

-- 抽象类
class Abstraction (α β : Type) [Implementation β] where
  implementation : β
  operation : α → String

-- 具体抽象
structure RefinedAbstraction (β : Type) [Implementation β] where
  implementation : β
  data : String

instance {β : Type} [Implementation β] : Abstraction (RefinedAbstraction β) β where
  implementation := RefinedAbstraction.implementation
  operation abstraction := 
    let impl := Implementation.operationImpl abstraction.implementation
    s!"Refined({impl}): {abstraction.data}"

-- 使用桥接
def implA := { name := "Implementation A" }
def implB := { name := "Implementation B" }

def abstraction1 := { implementation := implA, data := "Data 1" }
def abstraction2 := { implementation := implB, data := "Data 2" }

def result1 := Abstraction.operation abstraction1
def result2 := Abstraction.operation abstraction2
```

## 🎯 组合模式 (Composite Pattern)

### 树形结构

```lean
-- 组合模式
namespace Composite

-- 组件接口
class Component (α : Type) where
  operation : α → String
  add : α → α → α
  remove : α → α → Option α
  getChild : α → Nat → Option α

-- 叶子节点
structure Leaf where
  name : String

instance : Component Leaf where
  operation leaf := s!"Leaf: {leaf.name}"
  add leaf _ := leaf
  remove leaf _ := none
  getChild leaf _ := none

-- 复合节点
structure Composite where
  name : String
  children : List (Leaf ⊕ Composite)

instance : Component Composite where
  operation composite := 
    let childrenStr := List.map (fun child =>
      match child with
      | Sum.inl leaf => Component.operation leaf
      | Sum.inr comp => Component.operation comp) composite.children
    s!"Composite({composite.name}): {childrenStr}"
  
  add composite child := 
    { composite with children := child :: composite.children }
  
  remove composite child := 
    let filtered := List.filter (fun c => c != child) composite.children
    some { composite with children := filtered }
  
  getChild composite index := 
    List.get? composite.children index

-- 使用组合
def leaf1 := { name := "Leaf 1" }
def leaf2 := { name := "Leaf 2" }
def composite1 := { name := "Composite 1", children := [] }
def composite2 := { name := "Composite 2", children := [] }

def tree := Component.add composite1 (Sum.inl leaf1)
def tree2 := Component.add tree (Sum.inl leaf2)
def tree3 := Component.add tree2 (Sum.inr composite2)

def result := Component.operation tree3
```

## 🎨 外观模式 (Facade Pattern)

### 系统外观

```lean
-- 外观模式
namespace Facade

-- 子系统A
class SubsystemA (α : Type) where
  operationA : α → String

-- 子系统B
class SubsystemB (α : Type) where
  operationB : α → String

-- 子系统C
class SubsystemC (α : Type) where
  operationC : α → String

-- 外观
structure Facade where
  subsystemA : SubsystemA
  subsystemB : SubsystemB
  subsystemC : SubsystemC

-- 外观操作
def Facade.operation (facade : Facade) : String :=
  let a := SubsystemA.operationA facade.subsystemA
  let b := SubsystemB.operationB facade.subsystemB
  let c := SubsystemC.operationC facade.subsystemC
  s!"Facade: {a} + {b} + {c}"

-- 简化操作
def Facade.simpleOperation (facade : Facade) : String :=
  let a := SubsystemA.operationA facade.subsystemA
  let b := SubsystemB.operationB facade.subsystemB
  s!"Simple: {a} + {b}"

-- 使用外观
def createFacade : Facade :=
  { subsystemA := subsystemA
    subsystemB := subsystemB
    subsystemC := subsystemC }

def facade := createFacade
def result := Facade.operation facade
def simpleResult := Facade.simpleOperation facade
```

## 🎯 享元模式 (Flyweight Pattern)

### 对象共享

```lean
-- 享元模式
namespace Flyweight

-- 享元接口
class Flyweight (α : Type) where
  operation : α → String → String

-- 具体享元
structure ConcreteFlyweight where
  intrinsicState : String

instance : Flyweight ConcreteFlyweight where
  operation flyweight extrinsicState := 
    s!"Flyweight({flyweight.intrinsicState}): {extrinsicState}"

-- 享元工厂
structure FlyweightFactory where
  flyweights : List (String × ConcreteFlyweight)

def FlyweightFactory.getFlyweight (factory : FlyweightFactory) (key : String) : 
  ConcreteFlyweight × FlyweightFactory :=
  match List.find? factory.flyweights (fun (k, _) => k == key) with
  | some (_, flyweight) => (flyweight, factory)
  | none => 
    let newFlyweight := { intrinsicState := key }
    let newFactory := { factory with flyweights := (key, newFlyweight) :: factory.flyweights }
    (newFlyweight, newFactory)

-- 使用享元
def factory := { flyweights := [] }
def (flyweight1, factory1) := FlyweightFactory.getFlyweight factory "shared"
let (flyweight2, factory2) := FlyweightFactory.getFlyweight factory1 "shared"

def result1 := Flyweight.operation flyweight1 "extrinsic1"
def result2 := Flyweight.operation flyweight2 "extrinsic2"
```

## 🎯 应用场景

### 1. 接口适配

```lean
-- 第三方库适配
namespace ThirdPartyAdapter

-- 第三方库接口
structure ThirdPartyLibrary where
  oldMethod : String

-- 新系统接口
class NewSystemInterface where
  newMethod : String

-- 适配器
structure LibraryAdapter where
  library : ThirdPartyLibrary

instance : NewSystemInterface LibraryAdapter where
  newMethod adapter := 
    let old := adapter.library.oldMethod
    s!"Adapted: {old}"

end ThirdPartyAdapter
```

### 2. 功能扩展

```lean
-- 功能装饰器
namespace FeatureDecorator

-- 基础服务
structure BaseService where
  name : String

instance : Service BaseService where
  operation service := s!"Base: {service.name}"

-- 日志装饰器
structure LoggingDecorator (α : Type) where
  service : α

instance {α : Type} [Service α] : Service (LoggingDecorator α) where
  operation decorator := 
    let result := Service.operation decorator.service
    s!"[LOG] {result}"

-- 缓存装饰器
structure CachingDecorator (α : Type) where
  service : α
  cache : Option String

instance {α : Type} [Service α] : Service (CachingDecorator α) where
  operation decorator := 
    match decorator.cache with
    | some cached => s!"[CACHED] {cached}"
    | none => 
      let result := Service.operation decorator.service
      s!"[FRESH] {result}"

end FeatureDecorator
```

## 🚀 最佳实践

### 1. 设计原则

- **组合优于继承**: 使用组合实现灵活的结构
- **接口隔离**: 定义清晰的接口边界
- **依赖倒置**: 依赖抽象而非具体实现

### 2. 实现策略

- **类型安全**: 充分利用类型系统
- **不可变性**: 优先使用不可变对象
- **模块化**: 清晰的模块边界

### 3. 性能考虑

- **对象共享**: 合理使用享元模式
- **缓存策略**: 适当的缓存机制
- **内存管理**: 注意内存使用模式

---

**下一节**: [行为型模式](./04-Behavioral-Patterns.md)

**相关链接**:

- [创建型模式](./02-Creational-Patterns.md)
- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
