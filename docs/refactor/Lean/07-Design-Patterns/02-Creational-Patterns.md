# Lean 创建型设计模式

## 🎯 概述

创建型设计模式关注对象的创建过程，在Lean中通过类型系统、依赖类型和形式化方法实现类型安全的对象创建。本章介绍Lean中的各种创建型设计模式。

## 🏭 工厂模式 (Factory Pattern)

### 1. 简单工厂模式

```lean
-- 简单工厂模式
namespace SimpleFactory

-- 产品接口
class Product (α : Type) where
  name : α → String
  price : α → Float

-- 具体产品
structure Book where
  title : String
  author : String
  bookPrice : Float

structure Electronics where
  brand : String
  model : String
  elecPrice : Float

-- 产品实例
instance : Product Book where
  name := Book.title
  price := Book.bookPrice

instance : Product Electronics where
  name := s!"{Electronics.brand} {Electronics.model}"
  price := Electronics.elecPrice

-- 工厂
inductive ProductType
  | Book
  | Electronics

def createProduct (productType : ProductType) (params : String × String × Float) : 
  match productType with
  | ProductType.Book => Book
  | ProductType.Electronics => Electronics :=
  match productType, params with
  | ProductType.Book, (title, author, price) => 
    { title := title, author := author, bookPrice := price }
  | ProductType.Electronics, (brand, model, price) => 
    { brand := brand, model := model, elecPrice := price }

end SimpleFactory
```

### 2. 工厂方法模式

```lean
-- 工厂方法模式
namespace FactoryMethod

-- 抽象产品
class Product (α : Type) where
  name : α → String
  price : α → Float

-- 抽象工厂
class Factory (Product : Type) where
  createProduct : String → String → Float → Product

-- 具体产品
structure Book where
  title : String
  author : String
  price : Float

structure Electronics where
  brand : String
  model : String
  price : Float

-- 产品实例
instance : Product Book where
  name := Book.title
  price := Book.price

instance : Product Electronics where
  name := s!"{Electronics.brand} {Electronics.model}"
  price := Electronics.price

-- 具体工厂
structure BookFactory where

instance : Factory Book BookFactory where
  createProduct title author price := { title := title, author := author, price := price }

structure ElectronicsFactory where

instance : Factory Electronics ElectronicsFactory where
  createProduct brand model price := { brand := brand, model := model, price := price }

-- 使用工厂
def createBook : Book :=
  Factory.createProduct BookFactory {} "Lean Programming" "Author" 29.99

def createElectronics : Electronics :=
  Factory.createProduct ElectronicsFactory {} "Apple" "iPhone" 999.99

end FactoryMethod
```

### 3. 抽象工厂模式

```lean
-- 抽象工厂模式
namespace AbstractFactory

-- 产品族
class ProductFamily (α β : Type) where
  productA : α
  productB : β

-- 抽象工厂
class AbstractFactory (ProductA ProductB : Type) where
  createProductA : String → ProductA
  createProductB : String → ProductB

-- 具体产品
structure ModernChair where
  material : String
  color : String

structure ModernTable where
  material : String
  size : String

structure ClassicChair where
  wood : String
  style : String

structure ClassicTable where
  wood : String
  design : String

-- 现代风格工厂
structure ModernFactory where

instance : AbstractFactory ModernChair ModernTable ModernFactory where
  createProductA material := { material := material, color := "White" }
  createProductB material := { material := material, size := "Large" }

-- 古典风格工厂
structure ClassicFactory where

instance : AbstractFactory ClassicChair ClassicTable ClassicFactory where
  createProductA wood := { wood := wood, style := "Traditional" }
  createProductB wood := { wood := wood, design := "Classic" }

-- 使用抽象工厂
def createModernSet : ModernChair × ModernTable :=
  let factory := ModernFactory {}
  (AbstractFactory.createProductA factory "Steel",
   AbstractFactory.createProductB factory "Glass")

def createClassicSet : ClassicChair × ClassicTable :=
  let factory := ClassicFactory {}
  (AbstractFactory.createProductA factory "Oak",
   AbstractFactory.createProductB factory "Mahogany")

end AbstractFactory
```

## 🏗️ 建造者模式 (Builder Pattern)

### 1. 基础建造者模式

```lean
-- 建造者模式
namespace Builder

-- 复杂产品
structure Computer where
  cpu : String
  memory : String
  storage : String
  graphics : String
  deriving Repr

-- 抽象建造者
class Builder (Product : Type) where
  reset : Unit → Builder Product
  setCPU : String → Builder Product → Builder Product
  setMemory : String → Builder Product → Builder Product
  setStorage : String → Builder Product → Builder Product
  setGraphics : String → Builder Product → Builder Product
  build : Builder Product → Product

-- 具体建造者
structure ComputerBuilder where
  cpu : Option String
  memory : Option String
  storage : Option String
  graphics : Option String

instance : Builder Computer ComputerBuilder where
  reset _ := { cpu := none, memory := none, storage := none, graphics := none }
  
  setCPU cpu builder := { builder with cpu := some cpu }
  
  setMemory memory builder := { builder with memory := some memory }
  
  setStorage storage builder := { builder with storage := some storage }
  
  setGraphics graphics builder := { builder with graphics := some graphics }
  
  build builder := 
    { cpu := builder.cpu.getD "Default CPU"
      memory := builder.memory.getD "8GB"
      storage := builder.storage.getD "256GB SSD"
      graphics := builder.graphics.getD "Integrated" }

-- 使用建造者
def buildGamingComputer : Computer :=
  Builder.build (Builder.setGraphics "RTX 3080" 
    (Builder.setStorage "1TB NVMe" 
    (Builder.setMemory "32GB" 
    (Builder.setCPU "Intel i9" 
    (Builder.reset ComputerBuilder {})))))

def buildOfficeComputer : Computer :=
  Builder.build (Builder.setStorage "512GB SSD" 
    (Builder.setMemory "16GB" 
    (Builder.setCPU "Intel i5" 
    (Builder.reset ComputerBuilder {}))))

end Builder
```

### 2. 流式建造者模式

```lean
-- 流式建造者模式
namespace FluentBuilder

-- 产品
structure Car where
  brand : String
  model : String
  engine : String
  transmission : String
  color : String
  deriving Repr

-- 流式建造者
structure CarBuilder where
  brand : Option String
  model : Option String
  engine : Option String
  transmission : Option String
  color : Option String

-- 建造者方法
def CarBuilder.setBrand (brand : String) (builder : CarBuilder) : CarBuilder :=
  { builder with brand := some brand }

def CarBuilder.setModel (model : String) (builder : CarBuilder) : CarBuilder :=
  { builder with model := some model }

def CarBuilder.setEngine (engine : String) (builder : CarBuilder) : CarBuilder :=
  { builder with engine := some engine }

def CarBuilder.setTransmission (transmission : String) (builder : CarBuilder) : CarBuilder :=
  { builder with transmission := some transmission }

def CarBuilder.setColor (color : String) (builder : CarBuilder) : CarBuilder :=
  { builder with color := some color }

def CarBuilder.build (builder : CarBuilder) : Car :=
  { brand := builder.brand.getD "Unknown"
    model := builder.model.getD "Unknown"
    engine := builder.engine.getD "2.0L"
    transmission := builder.transmission.getD "Automatic"
    color := builder.color.getD "White" }

-- 使用流式建造者
def buildSportsCar : Car :=
  CarBuilder.build 
    (CarBuilder.setColor "Red"
    (CarBuilder.setTransmission "Manual"
    (CarBuilder.setEngine "3.0L V6"
    (CarBuilder.setModel "GT"
    (CarBuilder.setBrand "Toyota" {})))))

def buildFamilyCar : Car :=
  CarBuilder.build 
    (CarBuilder.setColor "Blue"
    (CarBuilder.setTransmission "Automatic"
    (CarBuilder.setEngine "2.5L I4"
    (CarBuilder.setModel "Camry"
    (CarBuilder.setBrand "Toyota" {})))))

end FluentBuilder
```

## 🎯 单例模式 (Singleton Pattern)

### 1. 类型级单例模式

```lean
-- 单例模式
namespace Singleton

-- 单例类型
structure Singleton (α : Type) where
  instance : α

-- 全局配置单例
structure GlobalConfig where
  databaseUrl : String
  apiKey : String
  debugMode : Bool
  deriving Repr

-- 单例实例
def globalConfig : Singleton GlobalConfig :=
  { instance := 
    { databaseUrl := "postgresql://localhost:5432/mydb"
      apiKey := "secret-key"
      debugMode := true } }

-- 访问单例
def getConfig : GlobalConfig := globalConfig.instance

def getDatabaseUrl : String := getConfig.databaseUrl

def getApiKey : String := getConfig.apiKey

def isDebugMode : Bool := getConfig.debugMode

-- 更新配置（创建新实例）
def updateConfig (newConfig : GlobalConfig) : Singleton GlobalConfig :=
  { instance := newConfig }

end Singleton
```

### 2. 线程安全单例模式

```lean
-- 线程安全单例模式
namespace ThreadSafeSingleton

-- 线程安全单例
structure ThreadSafeSingleton (α : Type) where
  instance : IO α

-- 日志单例
structure Logger where
  logLevel : String
  logFile : String
  deriving Repr

-- 创建单例
def createLogger : IO (ThreadSafeSingleton Logger) := do
  let logger := { logLevel := "INFO", logFile := "app.log" }
  return { instance := return logger }

-- 获取单例实例
def getLogger (singleton : ThreadSafeSingleton Logger) : IO Logger :=
  singleton.instance

-- 使用单例
def logMessage (message : String) (singleton : ThreadSafeSingleton Logger) : IO Unit := do
  let logger ← getLogger singleton
  IO.println s!"[{logger.logLevel}] {message}"

end ThreadSafeSingleton
```

## 🔧 原型模式 (Prototype Pattern)

### 1. 基础原型模式

```lean
-- 原型模式
namespace Prototype

-- 可克隆接口
class Cloneable (α : Type) where
  clone : α → α

-- 具体原型
structure Document where
  title : String
  content : String
  author : String
  deriving Repr

-- 文档克隆
instance : Cloneable Document where
  clone doc := { doc with title := doc.title ++ " (Copy)" }

-- 使用原型
def createDocument : Document :=
  { title := "Original Document"
    content := "This is the original content"
    author := "John Doe" }

def cloneDocument (doc : Document) : Document :=
  Cloneable.clone doc

-- 原型注册表
structure PrototypeRegistry (α : Type) where
  prototypes : List (String × α)

def PrototypeRegistry.register {α : Type} (name : String) (prototype : α) 
  (registry : PrototypeRegistry α) : PrototypeRegistry α :=
  { registry with prototypes := (name, prototype) :: registry.prototypes }

def PrototypeRegistry.clone {α : Type} [Cloneable α] (name : String) 
  (registry : PrototypeRegistry α) : Option α :=
  match List.find? registry.prototypes (fun (n, _) => n == name) with
  | some (_, prototype) => some (Cloneable.clone prototype)
  | none => none

end Prototype
```

### 2. 深度克隆原型模式

```lean
-- 深度克隆原型模式
namespace DeepClone

-- 深度可克隆接口
class DeepCloneable (α : Type) where
  deepClone : α → α

-- 复杂对象
structure ComplexObject where
  id : Nat
  name : String
  children : List ComplexObject
  metadata : List String
  deriving Repr

-- 深度克隆实现
instance : DeepCloneable ComplexObject where
  deepClone obj := 
    { obj with 
      children := List.map DeepCloneable.deepClone obj.children
      metadata := List.map (fun s => s ++ " (cloned)") obj.metadata }

-- 使用深度克隆
def createComplexObject : ComplexObject :=
  { id := 1
    name := "Root"
    children := 
      [ { id := 2, name := "Child 1", children := [], metadata := ["meta1"] }
      , { id := 3, name := "Child 2", children := [], metadata := ["meta2"] } ]
    metadata := ["root-meta"] }

def cloneComplexObject (obj : ComplexObject) : ComplexObject :=
  DeepCloneable.deepClone obj

end DeepClone
```

## 🎨 对象池模式 (Object Pool Pattern)

### 1. 基础对象池模式

```lean
-- 对象池模式
namespace ObjectPool

-- 可重用对象
class Reusable (α : Type) where
  reset : α → α
  isAvailable : α → Bool

-- 对象池
structure ObjectPool (α : Type) where
  available : List α
  inUse : List α

-- 对象池操作
def ObjectPool.acquire {α : Type} [Reusable α] (pool : ObjectPool α) : 
  Option (α × ObjectPool α) :=
  match pool.available with
  | [] => none
  | obj :: rest => 
    some (obj, { pool with available := rest, inUse := obj :: pool.inUse })

def ObjectPool.release {α : Type} [Reusable α] (obj : α) (pool : ObjectPool α) : 
  ObjectPool α :=
  let resetObj := Reusable.reset obj
  { pool with 
    available := resetObj :: pool.available
    inUse := List.filter (fun x => x != obj) pool.inUse }

-- 数据库连接池
structure DatabaseConnection where
  id : Nat
  url : String
  isConnected : Bool
  deriving Repr

instance : Reusable DatabaseConnection where
  reset conn := { conn with isConnected := false }
  isAvailable conn := !conn.isConnected

-- 创建连接池
def createConnectionPool (size : Nat) : ObjectPool DatabaseConnection :=
  let connections := List.map (fun i => 
    { id := i, url := "db://localhost", isConnected := false }) 
    (List.range size)
  { available := connections, inUse := [] }

end ObjectPool
```

## 🎯 应用场景

### 1. 配置管理

```lean
-- 配置管理应用
namespace ConfigManagement

-- 配置单例
structure AppConfig where
  databaseUrl : String
  apiKey : String
  debugMode : Bool
  maxConnections : Nat
  deriving Repr

def appConfig : Singleton AppConfig :=
  { instance := 
    { databaseUrl := "postgresql://localhost:5432/app"
      apiKey := "production-key"
      debugMode := false
      maxConnections := 100 } }

-- 配置工厂
class ConfigFactory where
  createDevConfig : AppConfig
  createProdConfig : AppConfig
  createTestConfig : AppConfig

instance : ConfigFactory where
  createDevConfig := 
    { databaseUrl := "postgresql://localhost:5432/dev"
      apiKey := "dev-key"
      debugMode := true
      maxConnections := 10 }
  createProdConfig := 
    { databaseUrl := "postgresql://prod:5432/app"
      apiKey := "prod-key"
      debugMode := false
      maxConnections := 1000 }
  createTestConfig := 
    { databaseUrl := "postgresql://localhost:5432/test"
      apiKey := "test-key"
      debugMode := true
      maxConnections := 5 }

end ConfigManagement
```

### 2. 资源管理

```lean
-- 资源管理应用
namespace ResourceManagement

-- 资源对象
structure Resource where
  id : Nat
  name : String
  isAllocated : Bool
  deriving Repr

instance : Reusable Resource where
  reset res := { res with isAllocated := false }
  isAvailable res := !res.isAllocated

-- 资源池
def createResourcePool (size : Nat) : ObjectPool Resource :=
  let resources := List.map (fun i => 
    { id := i, name := s!"Resource {i}", isAllocated := false }) 
    (List.range size)
  { available := resources, inUse := [] }

-- 资源分配
def allocateResource (pool : ObjectPool Resource) : Option (Resource × ObjectPool Resource) :=
  ObjectPool.acquire pool

-- 资源释放
def releaseResource (resource : Resource) (pool : ObjectPool Resource) : ObjectPool Resource :=
  ObjectPool.release resource pool

end ResourceManagement
```

## 🚀 最佳实践

### 1. 设计原则

- **类型安全**: 充分利用Lean的类型系统
- **不可变性**: 优先使用不可变对象
- **形式化验证**: 为关键部分提供证明

### 2. 实现策略

- **渐进式**: 从简单模式开始
- **模块化**: 清晰的模块边界
- **可测试性**: 便于验证和测试

### 3. 性能考虑

- **内存效率**: 注意内存使用模式
- **类型推断**: 减少类型注解
- **编译优化**: 利用编译时优化

---

**下一节**: [结构型模式](./03-Structural-Patterns.md)

**相关链接**:

- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
- [应用模型](../09-Application-Models/)
- [形式模型](../10-Formal-Models/)
