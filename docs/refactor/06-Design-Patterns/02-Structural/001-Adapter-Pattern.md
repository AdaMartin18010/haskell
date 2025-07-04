# 适配器模式 (Adapter Pattern)

## 概述

适配器模式是一种结构型设计模式，它允许不兼容的接口能够一起工作。适配器模式通过将一个类的接口转换成客户期望的另一个接口，解决了由于接口不兼容而不能一起工作的类的问题。

## 核心概念

### 1. 基本特征

- **接口转换**: 将不兼容的接口转换为兼容接口
- **透明性**: 客户端无需知道适配器的存在
- **复用性**: 可以复用现有的类
- **扩展性**: 易于添加新的适配器

### 2. 实现方式

- **类适配器**: 使用继承实现适配
- **对象适配器**: 使用组合实现适配
- **双向适配器**: 支持双向适配
- **默认适配器**: 提供默认实现

## 理论基础

### 1. 基本适配器模式

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配的类
struct Adaptee {
    specific_request: String,
}

impl Adaptee {
    fn new() -> Self {
        Self {
            specific_request: String::from("Specific request"),
        }
    }
    
    fn specific_request(&self) -> String {
        self.specific_request.clone()
    }
}

// 类适配器（使用继承）
struct ClassAdapter {
    adaptee: Adaptee,
}

impl ClassAdapter {
    fn new() -> Self {
        Self {
            adaptee: Adaptee::new(),
        }
    }
}

impl Target for ClassAdapter {
    fn request(&self) -> String {
        // 将specific_request转换为request
        format!("Adapter: {}", self.adaptee.specific_request())
    }
}

// 对象适配器（使用组合）
struct ObjectAdapter {
    adaptee: Adaptee,
}

impl ObjectAdapter {
    fn new(adaptee: Adaptee) -> Self {
        Self { adaptee }
    }
}

impl Target for ObjectAdapter {
    fn request(&self) -> String {
        // 将specific_request转换为request
        format!("Adapter: {}", self.adaptee.specific_request())
    }
}

// 使用示例
fn use_adapter() {
    let class_adapter = ClassAdapter::new();
    let object_adapter = ObjectAdapter::new(Adaptee::new());
    
    println!("{}", class_adapter.request());
    println!("{}", object_adapter.request());
}
```

### 2. 高级适配器模式

```rust
use std::collections::HashMap;

// 多个目标接口
trait TargetA {
    fn request_a(&self) -> String;
}

trait TargetB {
    fn request_b(&self) -> String;
}

// 被适配的类
struct ComplexAdaptee {
    data: HashMap<String, String>,
}

impl ComplexAdaptee {
    fn new() -> Self {
        let mut data = HashMap::new();
        data.insert("key1".to_string(), "value1".to_string());
        data.insert("key2".to_string(), "value2".to_string());
        
        Self { data }
    }
    
    fn get_data(&self, key: &str) -> Option<&String> {
        self.data.get(key)
    }
    
    fn process_data(&self, key: &str) -> String {
        match self.get_data(key) {
            Some(value) => format!("Processed: {}", value),
            None => String::from("Not found"),
        }
    }
}

// 双向适配器
struct BidirectionalAdapter {
    adaptee: ComplexAdaptee,
}

impl BidirectionalAdapter {
    fn new(adaptee: ComplexAdaptee) -> Self {
        Self { adaptee }
    }
    
    fn get_adaptee(&self) -> &ComplexAdaptee {
        &self.adaptee
    }
}

impl TargetA for BidirectionalAdapter {
    fn request_a(&self) -> String {
        self.adaptee.process_data("key1")
    }
}

impl TargetB for BidirectionalAdapter {
    fn request_b(&self) -> String {
        self.adaptee.process_data("key2")
    }
}

// 默认适配器
trait DefaultTarget {
    fn request(&self) -> String;
    fn request_with_param(&self, param: &str) -> String;
    fn request_optional(&self) -> Option<String> { None }
}

struct DefaultAdapter {
    adaptee: ComplexAdaptee,
}

impl DefaultAdapter {
    fn new(adaptee: ComplexAdaptee) -> Self {
        Self { adaptee }
    }
}

impl DefaultTarget for DefaultAdapter {
    fn request(&self) -> String {
        self.adaptee.process_data("key1")
    }
    
    fn request_with_param(&self, param: &str) -> String {
        self.adaptee.process_data(param)
    }
    
    fn request_optional(&self) -> Option<String> {
        Some(self.adaptee.process_data("key2"))
    }
}

// 泛型适配器
trait GenericAdaptee<T> {
    fn process(&self, data: T) -> String;
}

struct GenericAdapter<T> {
    adaptee: Box<dyn GenericAdaptee<T>>,
}

impl<T> GenericAdapter<T> {
    fn new(adaptee: Box<dyn GenericAdaptee<T>>) -> Self {
        Self { adaptee }
    }
}

impl<T> Target for GenericAdapter<T> {
    fn request(&self) -> String {
        // 这里需要T的默认值，简化实现
        String::from("Generic adapter request")
    }
}

// 具体实现
struct StringAdaptee;

impl GenericAdaptee<String> for StringAdaptee {
    fn process(&self, data: String) -> String {
        format!("Processed string: {}", data)
    }
}

struct IntAdaptee;

impl GenericAdaptee<i32> for IntAdaptee {
    fn process(&self, data: i32) -> String {
        format!("Processed int: {}", data)
    }
}
```

### 3. 异步适配器

```rust
use std::future::Future;
use std::pin::Pin;
use tokio::sync::Mutex;

// 异步目标接口
trait AsyncTarget {
    fn request_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = String> + Send + 'a>>;
}

// 同步被适配类
struct SyncAdaptee {
    data: String,
}

impl SyncAdaptee {
    fn new(data: String) -> Self {
        Self { data }
    }
    
    fn process(&self) -> String {
        format!("Sync processed: {}", self.data)
    }
}

// 异步适配器
struct AsyncAdapter {
    adaptee: SyncAdaptee,
}

impl AsyncAdapter {
    fn new(adaptee: SyncAdaptee) -> Self {
        Self { adaptee }
    }
}

impl AsyncTarget for AsyncAdapter {
    fn request_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = String> + Send + 'a>> {
        Box::pin(async move {
            // 模拟异步处理
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            self.adaptee.process()
        })
    }
}

// 线程安全适配器
struct ThreadSafeAdapter {
    adaptee: Arc<Mutex<SyncAdaptee>>,
}

impl ThreadSafeAdapter {
    fn new(adaptee: SyncAdaptee) -> Self {
        Self {
            adaptee: Arc::new(Mutex::new(adaptee)),
        }
    }
}

impl Target for ThreadSafeAdapter {
    fn request(&self) -> String {
        // 在实际应用中，这里应该使用异步方法
        // 简化实现
        String::from("Thread safe adapter request")
    }
}
```

### 4. 配置驱动适配器

```rust
use std::collections::HashMap;

// 配置驱动的适配器
struct ConfigurableAdapter {
    adaptee: ComplexAdaptee,
    config: HashMap<String, String>,
}

impl ConfigurableAdapter {
    fn new(adaptee: ComplexAdaptee) -> Self {
        let mut config = HashMap::new();
        config.insert("prefix".to_string(), "ADAPTED: ".to_string());
        config.insert("suffix".to_string(), " :END".to_string());
        
        Self { adaptee, config }
    }
    
    fn set_config(&mut self, key: String, value: String) {
        self.config.insert(key, value);
    }
    
    fn get_config(&self, key: &str) -> Option<&String> {
        self.config.get(key)
    }
}

impl Target for ConfigurableAdapter {
    fn request(&self) -> String {
        let prefix = self.get_config("prefix").unwrap_or(&String::new());
        let suffix = self.get_config("suffix").unwrap_or(&String::new());
        
        format!("{}{}{}", prefix, self.adaptee.process_data("key1"), suffix)
    }
}

// 工厂方法创建适配器
struct AdapterFactory;

impl AdapterFactory {
    fn create_adapter(adapter_type: &str) -> Box<dyn Target> {
        match adapter_type {
            "class" => Box::new(ClassAdapter::new()),
            "object" => {
                let adaptee = Adaptee::new();
                Box::new(ObjectAdapter::new(adaptee))
            }
            "configurable" => {
                let adaptee = ComplexAdaptee::new();
                Box::new(ConfigurableAdapter::new(adaptee))
            }
            _ => {
                let adaptee = Adaptee::new();
                Box::new(ObjectAdapter::new(adaptee))
            }
        }
    }
}
```

## Haskell实现示例

```haskell
-- 目标类型类
class Target a where
    request :: a -> String

-- 被适配的类
data Adaptee = Adaptee
    { specificRequest :: String
    }

newAdaptee :: Adaptee
newAdaptee = Adaptee "Specific request"

-- 类适配器
data ClassAdapter = ClassAdapter
    { adaptee :: Adaptee
    }

newClassAdapter :: ClassAdapter
newClassAdapter = ClassAdapter newAdaptee

instance Target ClassAdapter where
    request adapter = "Adapter: " ++ specificRequest (adaptee adapter)

-- 对象适配器
data ObjectAdapter = ObjectAdapter
    { objectAdaptee :: Adaptee
    }

newObjectAdapter :: Adaptee -> ObjectAdapter
newObjectAdapter adaptee = ObjectAdapter adaptee

instance Target ObjectAdapter where
    request adapter = "Adapter: " ++ specificRequest (objectAdaptee adapter)

-- 多个目标接口
class TargetA a where
    requestA :: a -> String

class TargetB a where
    requestB :: a -> String

-- 复杂被适配类
data ComplexAdaptee = ComplexAdaptee
    { adapteeData :: [(String, String)]
    }

newComplexAdaptee :: ComplexAdaptee
newComplexAdaptee = ComplexAdaptee [("key1", "value1"), ("key2", "value2")]

getData :: ComplexAdaptee -> String -> Maybe String
getData adaptee key = lookup key (adapteeData adaptee)

processData :: ComplexAdaptee -> String -> String
processData adaptee key = 
    case getData adaptee key of
        Just value -> "Processed: " ++ value
        Nothing -> "Not found"

-- 双向适配器
data BidirectionalAdapter = BidirectionalAdapter
    { bidirectionalAdaptee :: ComplexAdaptee
    }

newBidirectionalAdapter :: ComplexAdaptee -> BidirectionalAdapter
newBidirectionalAdapter adaptee = BidirectionalAdapter adaptee

instance TargetA BidirectionalAdapter where
    requestA adapter = processData (bidirectionalAdaptee adapter) "key1"

instance TargetB BidirectionalAdapter where
    requestB adapter = processData (bidirectionalAdaptee adapter) "key2"

-- 默认适配器
class DefaultTarget a where
    request :: a -> String
    requestWithParam :: a -> String -> String
    requestOptional :: a -> Maybe String
    requestOptional _ = Nothing

data DefaultAdapter = DefaultAdapter
    { defaultAdaptee :: ComplexAdaptee
    }

newDefaultAdapter :: ComplexAdaptee -> DefaultAdapter
newDefaultAdapter adaptee = DefaultAdapter adaptee

instance DefaultTarget DefaultAdapter where
    request adapter = processData (defaultAdaptee adapter) "key1"
    requestWithParam adapter param = processData (defaultAdaptee adapter) param
    requestOptional adapter = Just (processData (defaultAdaptee adapter) "key2")

-- 泛型适配器
class GenericAdaptee a where
    process :: a -> String

data GenericAdapter a = GenericAdapter
    { genericAdaptee :: a
    }

instance (GenericAdaptee a) => Target (GenericAdapter a) where
    request adapter = process (genericAdaptee adapter)

-- 具体实现
data StringAdaptee = StringAdaptee

instance GenericAdaptee StringAdaptee where
    process _ = "String adaptee"

data IntAdaptee = IntAdaptee

instance GenericAdaptee IntAdaptee where
    process _ = "Int adaptee"

-- 异步适配器
class AsyncTarget a where
    requestAsync :: a -> IO String

data AsyncAdapter = AsyncAdapter
    { asyncAdaptee :: SyncAdaptee
    }

data SyncAdaptee = SyncAdaptee
    { syncData :: String
    }

newSyncAdaptee :: String -> SyncAdaptee
newSyncAdaptee data' = SyncAdaptee data'

processSync :: SyncAdaptee -> String
processSync adaptee = "Sync processed: " ++ syncData adaptee

newAsyncAdapter :: SyncAdaptee -> AsyncAdapter
newAsyncAdapter adaptee = AsyncAdapter adaptee

instance AsyncTarget AsyncAdapter where
    requestAsync adapter = do
        -- 模拟异步处理
        threadDelay 100000 -- 100ms
        return $ processSync (asyncAdaptee adapter)

-- 配置驱动适配器
data ConfigurableAdapter = ConfigurableAdapter
    { configAdaptee :: ComplexAdaptee
    , config :: [(String, String)]
    }

newConfigurableAdapter :: ComplexAdaptee -> ConfigurableAdapter
newConfigurableAdapter adaptee = ConfigurableAdapter adaptee
    [("prefix", "ADAPTED: "), ("suffix", " :END")]

setConfig :: ConfigurableAdapter -> String -> String -> ConfigurableAdapter
setConfig adapter key value = adapter { config = (key, value) : filter ((/= key) . fst) (config adapter) }

getConfig :: ConfigurableAdapter -> String -> Maybe String
getConfig adapter key = lookup key (config adapter)

instance Target ConfigurableAdapter where
    request adapter = 
        let prefix = getConfig adapter "prefix" |>.getD ""
            suffix = getConfig adapter "suffix" |>.getD ""
            data' = processData (configAdaptee adapter) "key1"
        in prefix ++ data' ++ suffix

-- 使用示例
useAdapter :: IO ()
useAdapter = do
    let classAdapter = newClassAdapter
    let objectAdapter = newObjectAdapter newAdaptee
    
    putStrLn $ request classAdapter
    putStrLn $ request objectAdapter
    
    let bidirectionalAdapter = newBidirectionalAdapter newComplexAdaptee
    putStrLn $ requestA bidirectionalAdapter
    putStrLn $ requestB bidirectionalAdapter
    
    let defaultAdapter = newDefaultAdapter newComplexAdaptee
    putStrLn $ request defaultAdapter
    putStrLn $ requestWithParam defaultAdapter "key2"
    case requestOptional defaultAdapter of
        Just result -> putStrLn result
        Nothing -> putStrLn "No optional result"
    
    let configAdapter = newConfigurableAdapter newComplexAdaptee
    putStrLn $ request configAdapter
    
    let asyncAdapter = newAsyncAdapter (newSyncAdaptee "test data")
    asyncResult <- requestAsync asyncAdapter
    putStrLn asyncResult
```

## Lean实现思路

```lean
-- 目标类型类
class Target (α : Type) where
  request : α → String

-- 被适配的类
structure Adaptee where
  specificRequest : String

def newAdaptee : Adaptee :=
  { specificRequest := "Specific request" }

-- 类适配器
structure ClassAdapter where
  adaptee : Adaptee

def newClassAdapter : ClassAdapter :=
  { adaptee := newAdaptee }

instance : Target ClassAdapter where
  request adapter := "Adapter: " ++ adapter.adaptee.specificRequest

-- 对象适配器
structure ObjectAdapter where
  objectAdaptee : Adaptee

def newObjectAdapter (adaptee : Adaptee) : ObjectAdapter :=
  { objectAdaptee := adaptee }

instance : Target ObjectAdapter where
  request adapter := "Adapter: " ++ adapter.objectAdaptee.specificRequest

-- 多个目标接口
class TargetA (α : Type) where
  requestA : α → String

class TargetB (α : Type) where
  requestB : α → String

-- 复杂被适配类
structure ComplexAdaptee where
  adapteeData : List (String × String)

def newComplexAdaptee : ComplexAdaptee :=
  { adapteeData := [("key1", "value1"), ("key2", "value2")] }

def getData (adaptee : ComplexAdaptee) (key : String) : Option String :=
  adaptee.adapteeData.find? (fun (k, _) => k == key) |>.map (fun (_, v) => v)

def processData (adaptee : ComplexAdaptee) (key : String) : String :=
  match getData adaptee key with
  | some value => "Processed: " ++ value
  | none => "Not found"

-- 双向适配器
structure BidirectionalAdapter where
  bidirectionalAdaptee : ComplexAdaptee

def newBidirectionalAdapter (adaptee : ComplexAdaptee) : BidirectionalAdapter :=
  { bidirectionalAdaptee := adaptee }

instance : TargetA BidirectionalAdapter where
  requestA adapter := processData adapter.bidirectionalAdaptee "key1"

instance : TargetB BidirectionalAdapter where
  requestB adapter := processData adapter.bidirectionalAdaptee "key2"

-- 默认适配器
class DefaultTarget (α : Type) where
  request : α → String
  requestWithParam : α → String → String
  requestOptional : α → Option String
  requestOptional _ := none

structure DefaultAdapter where
  defaultAdaptee : ComplexAdaptee

def newDefaultAdapter (adaptee : ComplexAdaptee) : DefaultAdapter :=
  { defaultAdaptee := adaptee }

instance : DefaultTarget DefaultAdapter where
  request adapter := processData adapter.defaultAdaptee "key1"
  requestWithParam adapter param := processData adapter.defaultAdaptee param
  requestOptional adapter := some (processData adapter.defaultAdaptee "key2")

-- 泛型适配器
class GenericAdaptee (α : Type) where
  process : α → String

structure GenericAdapter (α : Type) where
  genericAdaptee : α

instance (α : Type) [GenericAdaptee α] : Target (GenericAdapter α) where
  request adapter := GenericAdaptee.process adapter.genericAdaptee

-- 具体实现
inductive StringAdaptee where
  | StringAdaptee : StringAdaptee

instance : GenericAdaptee StringAdaptee where
  process _ := "String adaptee"

inductive IntAdaptee where
  | IntAdaptee : IntAdaptee

instance : GenericAdaptee IntAdaptee where
  process _ := "Int adaptee"

-- 配置驱动适配器
structure ConfigurableAdapter where
  configAdaptee : ComplexAdaptee
  config : List (String × String)

def newConfigurableAdapter (adaptee : ComplexAdaptee) : ConfigurableAdapter :=
  { configAdaptee := adaptee
  , config := [("prefix", "ADAPTED: "), ("suffix", " :END")]
  }

def setConfig (adapter : ConfigurableAdapter) (key : String) (value : String) : ConfigurableAdapter :=
  { adapter with config := (key, value) :: adapter.config.filter (fun (k, _) => k != key) }

def getConfig (adapter : ConfigurableAdapter) (key : String) : Option String :=
  adapter.config.find? (fun (k, _) => k == key) |>.map (fun (_, v) => v)

instance : Target ConfigurableAdapter where
  request adapter := 
    let prefix := getConfig adapter "prefix" |>.getD ""
    let suffix := getConfig adapter "suffix" |>.getD ""
    let data' := processData adapter.configAdaptee "key1"
    prefix ++ data' ++ suffix
```

## 应用场景

### 1. 系统集成

- **第三方库集成**: 适配第三方库的接口
- **遗留系统**: 适配旧的系统接口
- **API版本**: 适配不同版本的API

### 2. 数据转换

- **格式转换**: 转换不同的数据格式
- **编码转换**: 转换不同的字符编码
- **协议转换**: 转换不同的通信协议

### 3. 平台适配

- **操作系统**: 适配不同的操作系统
- **硬件平台**: 适配不同的硬件平台
- **运行时环境**: 适配不同的运行时环境

### 4. 接口统一

- **多供应商**: 统一不同供应商的接口
- **多标准**: 统一不同的标准接口
- **多版本**: 统一不同版本的接口

## 最佳实践

### 1. 设计原则

- 遵循单一职责原则
- 保持适配器的简单性
- 避免过度设计

### 2. 性能考虑

- 减少适配开销
- 使用缓存机制
- 优化数据转换

### 3. 错误处理

- 处理适配失败
- 提供默认行为
- 记录错误信息

### 4. 测试策略

- 单元测试适配器
- 集成测试
- 性能测试

## 性能考虑

### 1. 适配开销

- 方法调用开销
- 数据转换成本
- 内存分配

### 2. 缓存策略

- 结果缓存
- 对象缓存
- 配置缓存

### 3. 并发安全

- 线程安全设计
- 锁机制
- 原子操作

## 总结

适配器模式是解决接口不兼容问题的重要设计模式，通过提供统一的接口来适配不同的实现。合理使用适配器模式可以提高系统的兼容性和可维护性，特别是在系统集成和遗留系统改造中发挥重要作用。
