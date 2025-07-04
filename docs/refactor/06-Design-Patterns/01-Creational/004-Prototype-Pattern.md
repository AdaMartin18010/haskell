# 原型模式 (Prototype Pattern)

## 概述
原型模式是一种创建型设计模式，它允许你通过复制现有对象来创建新对象，而不是通过类来创建。原型模式特别适用于创建成本高昂的对象，或者需要避免与产品类层次结构耦合的场景。

## 核心概念

### 1. 基本特征
- **对象复制**: 通过复制现有对象创建新对象
- **避免耦合**: 不依赖具体的类结构
- **性能优化**: 避免昂贵的初始化过程
- **灵活性**: 支持动态创建对象

### 2. 复制类型
- **浅拷贝**: 只复制对象引用
- **深拷贝**: 复制对象及其所有引用
- **自定义拷贝**: 根据需求定制复制行为

## 理论基础

### 1. 基本原型模式
```rust
use std::collections::HashMap;

// 原型特征
trait Prototype {
    fn clone(&self) -> Box<dyn Prototype>;
    fn get_name(&self) -> &str;
}

// 具体原型
#[derive(Clone)]
struct ConcretePrototype {
    name: String,
    data: Vec<String>,
    config: HashMap<String, String>,
}

impl ConcretePrototype {
    fn new(name: String) -> Self {
        let mut config = HashMap::new();
        config.insert("version".to_string(), "1.0".to_string());
        config.insert("environment".to_string(), "production".to_string());
        
        Self {
            name,
            data: vec!["default".to_string()],
            config,
        }
    }
    
    fn add_data(&mut self, item: String) {
        self.data.push(item);
    }
    
    fn set_config(&mut self, key: String, value: String) {
        self.config.insert(key, value);
    }
    
    fn get_data(&self) -> &Vec<String> {
        &self.data
    }
    
    fn get_config(&self) -> &HashMap<String, String> {
        &self.config
    }
}

impl Prototype for ConcretePrototype {
    fn clone(&self) -> Box<dyn Prototype> {
        Box::new(self.clone())
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 原型管理器
struct PrototypeManager {
    prototypes: HashMap<String, Box<dyn Prototype>>,
}

impl PrototypeManager {
    fn new() -> Self {
        Self {
            prototypes: HashMap::new(),
        }
    }
    
    fn register(&mut self, name: String, prototype: Box<dyn Prototype>) {
        self.prototypes.insert(name, prototype);
    }
    
    fn create(&self, name: &str) -> Option<Box<dyn Prototype>> {
        self.prototypes.get(name).map(|p| p.clone())
    }
    
    fn list_prototypes(&self) -> Vec<&str> {
        self.prototypes.keys().map(|k| k.as_str()).collect()
    }
}

// 使用示例
fn use_basic_prototype() {
    let mut manager = PrototypeManager::new();
    
    // 创建原型
    let prototype = ConcretePrototype::new("base_config".to_string());
    manager.register("base_config".to_string(), Box::new(prototype));
    
    // 从原型创建新对象
    if let Some(new_prototype) = manager.create("base_config") {
        println!("Created prototype: {}", new_prototype.get_name());
    }
}
```

### 2. 深拷贝原型
```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 复杂对象
#[derive(Clone)]
struct ComplexObject {
    id: String,
    data: Vec<String>,
    nested: NestedObject,
    shared: Arc<Mutex<SharedData>>,
}

#[derive(Clone)]
struct NestedObject {
    name: String,
    properties: HashMap<String, String>,
}

#[derive(Clone)]
struct SharedData {
    counter: u32,
    metadata: HashMap<String, String>,
}

impl ComplexObject {
    fn new(id: String) -> Self {
        let mut properties = HashMap::new();
        properties.insert("type".to_string(), "complex".to_string());
        properties.insert("version".to_string(), "1.0".to_string());
        
        let mut metadata = HashMap::new();
        metadata.insert("created".to_string(), "2024-01-01".to_string());
        
        Self {
            id,
            data: vec!["initial".to_string()],
            nested: NestedObject {
                name: "nested".to_string(),
                properties,
            },
            shared: Arc::new(Mutex::new(SharedData {
                counter: 0,
                metadata,
            })),
        }
    }
    
    fn add_data(&mut self, item: String) {
        self.data.push(item);
    }
    
    fn update_nested_property(&mut self, key: String, value: String) {
        self.nested.properties.insert(key, value);
    }
    
    fn increment_counter(&self) {
        if let Ok(mut shared) = self.shared.lock() {
            shared.counter += 1;
        }
    }
    
    fn get_counter(&self) -> u32 {
        if let Ok(shared) = self.shared.lock() {
            shared.counter
        } else {
            0
        }
    }
}

// 深拷贝特征
trait DeepClone {
    fn deep_clone(&self) -> Self;
}

impl DeepClone for ComplexObject {
    fn deep_clone(&self) -> Self {
        // 深拷贝所有字段
        let mut new_data = Vec::new();
        for item in &self.data {
            new_data.push(item.clone());
        }
        
        let mut new_properties = HashMap::new();
        for (key, value) in &self.nested.properties {
            new_properties.insert(key.clone(), value.clone());
        }
        
        let mut new_metadata = HashMap::new();
        if let Ok(shared) = self.shared.lock() {
            for (key, value) in &shared.metadata {
                new_metadata.insert(key.clone(), value.clone());
            }
        }
        
        Self {
            id: format!("{}_copy", self.id),
            data: new_data,
            nested: NestedObject {
                name: format!("{}_copy", self.nested.name),
                properties: new_properties,
            },
            shared: Arc::new(Mutex::new(SharedData {
                counter: 0, // 重置计数器
                metadata: new_metadata,
            })),
        }
    }
}

// 原型特征
trait Prototype {
    fn clone_prototype(&self) -> Box<dyn Prototype>;
    fn deep_clone_prototype(&self) -> Box<dyn Prototype>;
    fn get_id(&self) -> &str;
}

impl Prototype for ComplexObject {
    fn clone_prototype(&self) -> Box<dyn Prototype> {
        Box::new(self.clone()) // 浅拷贝
    }
    
    fn deep_clone_prototype(&self) -> Box<dyn Prototype> {
        Box::new(self.deep_clone()) // 深拷贝
    }
    
    fn get_id(&self) -> &str {
        &self.id
    }
}
```

### 3. 自定义拷贝原型
```rust
use std::collections::HashMap;

// 自定义拷贝策略
enum CopyStrategy {
    Shallow,
    Deep,
    Custom(Box<dyn Fn(&str) -> String>),
}

// 可配置原型
#[derive(Clone)]
struct ConfigurablePrototype {
    name: String,
    data: Vec<String>,
    config: HashMap<String, String>,
    copy_strategy: CopyStrategy,
}

impl ConfigurablePrototype {
    fn new(name: String, strategy: CopyStrategy) -> Self {
        let mut config = HashMap::new();
        config.insert("version".to_string(), "1.0".to_string());
        
        Self {
            name,
            data: vec!["default".to_string()],
            config,
            copy_strategy,
        }
    }
    
    fn custom_clone(&self) -> Self {
        match &self.copy_strategy {
            CopyStrategy::Shallow => self.clone(),
            CopyStrategy::Deep => {
                let mut new_data = Vec::new();
                for item in &self.data {
                    new_data.push(item.clone());
                }
                
                let mut new_config = HashMap::new();
                for (key, value) in &self.config {
                    new_config.insert(key.clone(), value.clone());
                }
                
                Self {
                    name: format!("{}_copy", self.name),
                    data: new_data,
                    config: new_config,
                    copy_strategy: self.copy_strategy.clone(),
                }
            }
            CopyStrategy::Custom(func) => {
                let new_name = func(&self.name);
                Self {
                    name: new_name,
                    data: self.data.clone(),
                    config: self.config.clone(),
                    copy_strategy: self.copy_strategy.clone(),
                }
            }
        }
    }
}

// 原型工厂
struct PrototypeFactory {
    prototypes: HashMap<String, ConfigurablePrototype>,
}

impl PrototypeFactory {
    fn new() -> Self {
        Self {
            prototypes: HashMap::new(),
        }
    }
    
    fn register(&mut self, name: String, prototype: ConfigurablePrototype) {
        self.prototypes.insert(name, prototype);
    }
    
    fn create(&self, name: &str) -> Option<ConfigurablePrototype> {
        self.prototypes.get(name).map(|p| p.custom_clone())
    }
    
    fn create_with_strategy(&self, name: &str, strategy: CopyStrategy) -> Option<ConfigurablePrototype> {
        self.prototypes.get(name).map(|p| {
            let mut new_prototype = p.clone();
            new_prototype.copy_strategy = strategy;
            new_prototype.custom_clone()
        })
    }
}
```

### 4. 异步原型
```rust
use std::future::Future;
use std::pin::Pin;
use tokio::sync::Mutex;

// 异步原型特征
trait AsyncPrototype {
    fn clone_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = Box<dyn AsyncPrototype>> + Send + 'a>>;
    fn get_name(&self) -> &str;
}

// 异步复杂对象
struct AsyncComplexObject {
    name: String,
    data: Arc<Mutex<Vec<String>>>,
    config: Arc<Mutex<HashMap<String, String>>>,
}

impl AsyncComplexObject {
    fn new(name: String) -> Self {
        let mut config = HashMap::new();
        config.insert("async".to_string(), "true".to_string());
        
        Self {
            name,
            data: Arc::new(Mutex::new(vec!["async_default".to_string()])),
            config: Arc::new(Mutex::new(config)),
        }
    }
    
    async fn add_data(&self, item: String) {
        let mut data = self.data.lock().await;
        data.push(item);
    }
    
    async fn get_data(&self) -> Vec<String> {
        let data = self.data.lock().await;
        data.clone()
    }
}

impl AsyncPrototype for AsyncComplexObject {
    fn clone_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = Box<dyn AsyncPrototype>> + Send + 'a>> {
        Box::pin(async move {
            let data = self.data.lock().await.clone();
            let config = self.config.lock().await.clone();
            
            let new_object = AsyncComplexObject {
                name: format!("{}_async_copy", self.name),
                data: Arc::new(Mutex::new(data)),
                config: Arc::new(Mutex::new(config)),
            };
            
            Box::new(new_object) as Box<dyn AsyncPrototype>
        })
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 异步原型管理器
struct AsyncPrototypeManager {
    prototypes: Arc<Mutex<HashMap<String, Box<dyn AsyncPrototype>>>>,
}

impl AsyncPrototypeManager {
    fn new() -> Self {
        Self {
            prototypes: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn register(&self, name: String, prototype: Box<dyn AsyncPrototype>) {
        let mut prototypes = self.prototypes.lock().await;
        prototypes.insert(name, prototype);
    }
    
    async fn create(&self, name: &str) -> Option<Box<dyn AsyncPrototype>> {
        let prototypes = self.prototypes.lock().await;
        prototypes.get(name).map(|p| p.clone_async().await)
    }
}
```

## Haskell实现示例

```haskell
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Concurrent.MVar
import Control.Monad.IO.Class

-- 原型类型类
class Prototype a where
    clone :: a -> a
    getName :: a -> String

-- 具体原型
data ConcretePrototype = ConcretePrototype
    { name :: String
    , data :: [String]
    , config :: Map String String
    } deriving (Show, Eq)

instance Prototype ConcretePrototype where
    clone prototype = prototype { name = name prototype ++ "_copy" }
    getName = name

-- 创建原型
newConcretePrototype :: String -> ConcretePrototype
newConcretePrototype name = ConcretePrototype
    { name = name
    , data = ["default"]
    , config = Map.fromList [("version", "1.0"), ("environment", "production")]
    }

-- 原型管理器
data PrototypeManager = PrototypeManager
    { prototypes :: Map String ConcretePrototype
    }

newPrototypeManager :: PrototypeManager
newPrototypeManager = PrototypeManager Map.empty

registerPrototype :: String -> ConcretePrototype -> PrototypeManager -> PrototypeManager
registerPrototype name prototype manager = 
    manager { prototypes = Map.insert name prototype (prototypes manager) }

createFromPrototype :: String -> PrototypeManager -> Maybe ConcretePrototype
createFromPrototype name manager = 
    Map.lookup name (prototypes manager) >>= Just . clone

listPrototypes :: PrototypeManager -> [String]
listPrototypes manager = Map.keys (prototypes manager)

-- 深拷贝原型
data ComplexObject = ComplexObject
    { objectId :: String
    , objectData :: [String]
    , nestedObject :: NestedObject
    , sharedData :: MVar SharedData
    }

data NestedObject = NestedObject
    { nestedName :: String
    , properties :: Map String String
    } deriving (Show, Eq)

data SharedData = SharedData
    { counter :: Int
    , metadata :: Map String String
    } deriving (Show, Eq)

instance Prototype ComplexObject where
    clone = deepClone
    getName = objectId

deepClone :: ComplexObject -> ComplexObject
deepClone obj = ComplexObject
    { objectId = objectId obj ++ "_deep_copy"
    , objectData = map id (objectData obj) -- 深拷贝列表
    , nestedObject = deepCloneNested (nestedObject obj)
    , sharedData = unsafePerformIO $ do
        shared <- readMVar (sharedData obj)
        newMVar $ shared { counter = 0 } -- 重置计数器
    }

deepCloneNested :: NestedObject -> NestedObject
deepCloneNested nested = NestedObject
    { nestedName = nestedName nested ++ "_copy"
    , properties = Map.map id (properties nested) -- 深拷贝Map
    }

-- 自定义拷贝策略
data CopyStrategy = Shallow | Deep | Custom (String -> String)

data ConfigurablePrototype = ConfigurablePrototype
    { configName :: String
    , configData :: [String]
    , configConfig :: Map String String
    , copyStrategy :: CopyStrategy
    }

customClone :: ConfigurablePrototype -> ConfigurablePrototype
customClone prototype = 
    case copyStrategy prototype of
        Shallow -> prototype { configName := configName prototype ++ "_shallow" }
        Deep -> prototype { 
            configName := configName prototype ++ "_deep"
            , configData := map id (configData prototype)
            , configConfig := Map.map id (configConfig prototype)
        }
        Custom func -> prototype { configName := func (configName prototype) }

-- 原型工厂
data PrototypeFactory = PrototypeFactory
    { factoryPrototypes :: Map String ConfigurablePrototype
    }

newPrototypeFactory :: PrototypeFactory
newPrototypeFactory = PrototypeFactory Map.empty

registerPrototypeFactory :: String -> ConfigurablePrototype -> PrototypeFactory -> PrototypeFactory
registerPrototypeFactory name prototype factory = 
    factory { factoryPrototypes := Map.insert name prototype (factoryPrototypes factory) }

createFromFactory :: String -> PrototypeFactory -> Maybe ConfigurablePrototype
createFromFactory name factory = 
    Map.lookup name (factoryPrototypes factory) >>= Just . customClone

createWithStrategy :: String -> CopyStrategy -> PrototypeFactory -> Maybe ConfigurablePrototype
createWithStrategy name strategy factory = 
    Map.lookup name (factoryPrototypes factory) >>= \prototype ->
        Just $ customClone prototype { copyStrategy := strategy }

-- 异步原型
class AsyncPrototype a where
    cloneAsync :: a -> IO a
    getAsyncName :: a -> String

data AsyncComplexObject = AsyncComplexObject
    { asyncName :: String
    , asyncData :: MVar [String]
    , asyncConfig :: MVar (Map String String)
    }

instance AsyncPrototype AsyncComplexObject where
    cloneAsync obj = do
        data' <- readMVar (asyncData obj)
        config' <- readMVar (asyncConfig obj)
        newData <- newMVar data'
        newConfig <- newMVar config'
        return $ AsyncComplexObject
            { asyncName := asyncName obj ++ "_async_copy"
            , asyncData := newData
            , asyncConfig := newConfig
            }
    getAsyncName = asyncName

-- 异步原型管理器
data AsyncPrototypeManager = AsyncPrototypeManager
    { asyncPrototypes :: MVar (Map String AsyncComplexObject)
    }

newAsyncPrototypeManager :: IO AsyncPrototypeManager
newAsyncPrototypeManager = do
    prototypes <- newMVar Map.empty
    return $ AsyncPrototypeManager prototypes

registerAsyncPrototype :: String -> AsyncComplexObject -> AsyncPrototypeManager -> IO ()
registerAsyncPrototype name prototype manager = do
    prototypes <- takeMVar (asyncPrototypes manager)
    putMVar (asyncPrototypes manager) (Map.insert name prototype prototypes)

createAsyncFromPrototype :: String -> AsyncPrototypeManager -> IO (Maybe AsyncComplexObject)
createAsyncFromPrototype name manager = do
    prototypes <- readMVar (asyncPrototypes manager)
    case Map.lookup name prototypes of
        Just prototype -> Just <$> cloneAsync prototype
        Nothing -> return Nothing
```

## Lean实现思路

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- 原型类型类
class Prototype (α : Type) where
  clone : α → α
  getName : α → String

-- 具体原型
structure ConcretePrototype where
  name : String
  data : List String
  config : HashMap String String

instance : Prototype ConcretePrototype where
  clone prototype := { prototype with name := prototype.name ++ "_copy" }
  getName := ConcretePrototype.name

-- 创建原型
def newConcretePrototype (name : String) : ConcretePrototype :=
  { name := name
  , data := ["default"]
  , config := HashMap.empty.insert "version" "1.0" |>.insert "environment" "production"
  }

-- 原型管理器
structure PrototypeManager where
  prototypes : HashMap String ConcretePrototype

def newPrototypeManager : PrototypeManager :=
  { prototypes := HashMap.empty }

def registerPrototype (name : String) (prototype : ConcretePrototype) 
  (manager : PrototypeManager) : PrototypeManager :=
  { manager with prototypes := manager.prototypes.insert name prototype }

def createFromPrototype (name : String) (manager : PrototypeManager) : 
  Option ConcretePrototype :=
  manager.prototypes.find? name |>.map Prototype.clone

def listPrototypes (manager : PrototypeManager) : List String :=
  manager.prototypes.keys

-- 深拷贝原型
structure ComplexObject where
  objectId : String
  objectData : List String
  nestedObject : NestedObject
  sharedData : SharedData

structure NestedObject where
  nestedName : String
  properties : HashMap String String

structure SharedData where
  counter : Nat
  metadata : HashMap String String

instance : Prototype ComplexObject where
  clone := deepClone
  getName := ComplexObject.objectId

def deepClone (obj : ComplexObject) : ComplexObject :=
  { objectId := obj.objectId ++ "_deep_copy"
  , objectData := obj.objectData.map id -- 深拷贝列表
  , nestedObject := deepCloneNested obj.nestedObject
  , sharedData := { obj.sharedData with counter := 0 } -- 重置计数器
  }

def deepCloneNested (nested : NestedObject) : NestedObject :=
  { nestedName := nestedName nested ++ "_copy"
  , properties := nested.properties.map id -- 深拷贝Map
  }

-- 自定义拷贝策略
inductive CopyStrategy where
  | shallow : CopyStrategy
  | deep : CopyStrategy
  | custom : (String → String) → CopyStrategy

structure ConfigurablePrototype where
  configName : String
  configData : List String
  configConfig : HashMap String String
  copyStrategy : CopyStrategy

def customClone (prototype : ConfigurablePrototype) : ConfigurablePrototype :=
  match prototype.copyStrategy with
  | CopyStrategy.shallow => { prototype with configName := prototype.configName ++ "_shallow" }
  | CopyStrategy.deep => { 
      prototype with 
      configName := prototype.configName ++ "_deep"
      configData := prototype.configData.map id
      configConfig := prototype.configConfig.map id
    }
  | CopyStrategy.custom func => { prototype with configName := func prototype.configName }

-- 原型工厂
structure PrototypeFactory where
  factoryPrototypes : HashMap String ConfigurablePrototype

def newPrototypeFactory : PrototypeFactory :=
  { factoryPrototypes := HashMap.empty }

def registerPrototypeFactory (name : String) (prototype : ConfigurablePrototype) 
  (factory : PrototypeFactory) : PrototypeFactory :=
  { factory with factoryPrototypes := factory.factoryPrototypes.insert name prototype }

def createFromFactory (name : String) (factory : PrototypeFactory) : 
  Option ConfigurablePrototype :=
  factory.factoryPrototypes.find? name |>.map customClone

def createWithStrategy (name : String) (strategy : CopyStrategy) 
  (factory : PrototypeFactory) : Option ConfigurablePrototype :=
  factory.factoryPrototypes.find? name |>.map fun prototype =>
    customClone { prototype with copyStrategy := strategy }
```

## 应用场景

### 1. 对象创建
- **复杂对象**: 创建成本高昂的复杂对象
- **配置对象**: 复制配置模板
- **游戏对象**: 复制游戏中的对象

### 2. 缓存优化
- **对象池**: 复用已创建的对象
- **模板缓存**: 缓存常用对象模板
- **性能优化**: 避免重复初始化

### 3. 状态管理
- **状态快照**: 保存对象状态
- **撤销重做**: 复制对象状态
- **版本控制**: 管理对象版本

### 4. 测试场景
- **测试数据**: 复制测试对象
- **模拟对象**: 创建模拟实例
- **基准测试**: 复制基准对象

## 最佳实践

### 1. 拷贝策略
- 选择合适的拷贝方式
- 考虑性能影响
- 处理循环引用

### 2. 内存管理
- 避免内存泄漏
- 合理使用引用计数
- 优化拷贝性能

### 3. 线程安全
- 处理并发访问
- 使用原子操作
- 避免竞态条件

### 4. 错误处理
- 处理拷贝失败
- 提供回退机制
- 记录错误日志

## 性能考虑

### 1. 拷贝开销
- 深拷贝成本
- 内存分配
- 垃圾回收

### 2. 缓存策略
- 对象缓存
- 模板缓存
- 引用缓存

### 3. 并发性能
- 锁竞争
- 原子操作
- 内存屏障

## 总结

原型模式是创建对象的重要设计模式，通过复制现有对象来创建新对象，避免了昂贵的初始化过程。合理使用原型模式可以优化对象创建性能，提高系统的响应速度。 