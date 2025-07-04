# 工厂模式 (Factory Pattern)

## 概述

工厂模式是一种创建型设计模式，它提供了一种创建对象的最佳方式。工厂模式封装了对象的创建过程，使代码更加灵活和可维护。

## 核心概念

### 1. 工厂模式类型

- **简单工厂**: 一个工厂类创建所有产品
- **工厂方法**: 每个产品有自己的工厂
- **抽象工厂**: 创建产品族

### 2. 设计原则

- **开闭原则**: 对扩展开放，对修改关闭
- **单一职责**: 每个工厂只负责创建特定产品
- **依赖倒置**: 依赖抽象而非具体实现

## 理论基础

### 1. 简单工厂模式

```rust
// 产品抽象
trait Product {
    fn operation(&self) -> String;
}

// 具体产品
struct ConcreteProductA;

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        String::from("ConcreteProductA operation")
    }
}

struct ConcreteProductB;

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        String::from("ConcreteProductB operation")
    }
}

// 简单工厂
struct SimpleFactory;

impl SimpleFactory {
    fn create_product(product_type: &str) -> Box<dyn Product> {
        match product_type {
            "A" => Box::new(ConcreteProductA),
            "B" => Box::new(ConcreteProductB),
            _ => panic!("Unknown product type"),
        }
    }
}

// 使用示例
fn use_simple_factory() {
    let product_a = SimpleFactory::create_product("A");
    let product_b = SimpleFactory::create_product("B");
    
    println!("{}", product_a.operation());
    println!("{}", product_b.operation());
}
```

### 2. 工厂方法模式

```rust
// 产品抽象
trait Product {
    fn operation(&self) -> String;
}

// 具体产品
struct ConcreteProductA;

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        String::from("ConcreteProductA operation")
    }
}

struct ConcreteProductB;

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        String::from("ConcreteProductB operation")
    }
}

// 工厂抽象
trait Factory {
    fn create_product(&self) -> Box<dyn Product>;
}

// 具体工厂
struct ConcreteFactoryA;

impl Factory for ConcreteFactoryA {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductA)
    }
}

struct ConcreteFactoryB;

impl Factory for ConcreteFactoryB {
    fn create_product(&self) -> Box<dyn Product> {
        Box::new(ConcreteProductB)
    }
}

// 使用示例
fn use_factory_method() {
    let factory_a = ConcreteFactoryA;
    let factory_b = ConcreteFactoryB;
    
    let product_a = factory_a.create_product();
    let product_b = factory_b.create_product();
    
    println!("{}", product_a.operation());
    println!("{}", product_b.operation());
}
```

### 3. 抽象工厂模式

```rust
// 抽象产品A
trait AbstractProductA {
    fn operation_a(&self) -> String;
}

// 抽象产品B
trait AbstractProductB {
    fn operation_b(&self) -> String;
}

// 具体产品A1
struct ConcreteProductA1;

impl AbstractProductA for ConcreteProductA1 {
    fn operation_a(&self) -> String {
        String::from("ConcreteProductA1 operation")
    }
}

// 具体产品A2
struct ConcreteProductA2;

impl AbstractProductA for ConcreteProductA2 {
    fn operation_a(&self) -> String {
        String::from("ConcreteProductA2 operation")
    }
}

// 具体产品B1
struct ConcreteProductB1;

impl AbstractProductB for ConcreteProductB1 {
    fn operation_b(&self) -> String {
        String::from("ConcreteProductB1 operation")
    }
}

// 具体产品B2
struct ConcreteProductB2;

impl AbstractProductB for ConcreteProductB2 {
    fn operation_b(&self) -> String {
        String::from("ConcreteProductB2 operation")
    }
}

// 抽象工厂
trait AbstractFactory {
    fn create_product_a(&self) -> Box<dyn AbstractProductA>;
    fn create_product_b(&self) -> Box<dyn AbstractProductB>;
}

// 具体工厂1
struct ConcreteFactory1;

impl AbstractFactory for ConcreteFactory1 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA1)
    }
    
    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB1)
    }
}

// 具体工厂2
struct ConcreteFactory2;

impl AbstractFactory for ConcreteFactory2 {
    fn create_product_a(&self) -> Box<dyn AbstractProductA> {
        Box::new(ConcreteProductA2)
    }
    
    fn create_product_b(&self) -> Box<dyn AbstractProductB> {
        Box::new(ConcreteProductB2)
    }
}

// 使用示例
fn use_abstract_factory() {
    let factory1 = ConcreteFactory1;
    let factory2 = ConcreteFactory2;
    
    let product_a1 = factory1.create_product_a();
    let product_b1 = factory1.create_product_b();
    let product_a2 = factory2.create_product_a();
    let product_b2 = factory2.create_product_b();
    
    println!("{}", product_a1.operation_a());
    println!("{}", product_b1.operation_b());
    println!("{}", product_a2.operation_a());
    println!("{}", product_b2.operation_b());
}
```

### 4. 高级工厂模式

```rust
// 泛型工厂
trait GenericFactory<T> {
    fn create(&self) -> T;
}

// 配置驱动的工厂
struct ConfigurableFactory {
    config: String,
}

impl ConfigurableFactory {
    fn new(config: String) -> Self {
        Self { config }
    }
    
    fn create_product(&self) -> Box<dyn Product> {
        match self.config.as_str() {
            "development" => Box::new(DevelopmentProduct),
            "production" => Box::new(ProductionProduct),
            "testing" => Box::new(TestingProduct),
            _ => Box::new(DefaultProduct),
        }
    }
}

// 具体产品
struct DevelopmentProduct;
struct ProductionProduct;
struct TestingProduct;
struct DefaultProduct;

impl Product for DevelopmentProduct {
    fn operation(&self) -> String {
        String::from("Development product")
    }
}

impl Product for ProductionProduct {
    fn operation(&self) -> String {
        String::from("Production product")
    }
}

impl Product for TestingProduct {
    fn operation(&self) -> String {
        String::from("Testing product")
    }
}

impl Product for DefaultProduct {
    fn operation(&self) -> String {
        String::from("Default product")
    }
}

// 异步工厂
use std::future::Future;
use std::pin::Pin;

trait AsyncFactory {
    fn create_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = Box<dyn Product>> + Send + 'a>>;
}

struct AsyncConcreteFactory;

impl AsyncFactory for AsyncConcreteFactory {
    fn create_async<'a>(&'a self) -> Pin<Box<dyn Future<Output = Box<dyn Product>> + Send + 'a>> {
        Box::pin(async move {
            // 模拟异步创建过程
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            Box::new(ConcreteProductA)
        })
    }
}

// 使用示例
async fn use_async_factory() {
    let factory = AsyncConcreteFactory;
    let product = factory.create_async().await;
    println!("{}", product.operation());
}
```

## Haskell实现示例

```haskell
-- 产品类型类
class Product a where
    operation :: a -> String

-- 具体产品
data ConcreteProductA = ConcreteProductA
data ConcreteProductB = ConcreteProductB

instance Product ConcreteProductA where
    operation _ = "ConcreteProductA operation"

instance Product ConcreteProductB where
    operation _ = "ConcreteProductB operation"

-- 简单工厂
data SimpleFactory = SimpleFactory

createProduct :: String -> Maybe (Either ConcreteProductA ConcreteProductB)
createProduct productType = 
    case productType of
        "A" -> Just (Left ConcreteProductA)
        "B" -> Just (Right ConcreteProductB)
        _ -> Nothing

-- 工厂方法模式
class Factory f where
    createProduct :: f -> Either ConcreteProductA ConcreteProductB

data ConcreteFactoryA = ConcreteFactoryA
data ConcreteFactoryB = ConcreteFactoryB

instance Factory ConcreteFactoryA where
    createProduct _ = Left ConcreteProductA

instance Factory ConcreteFactoryB where
    createProduct _ = Right ConcreteProductB

-- 抽象工厂模式
class AbstractProductA a where
    operationA :: a -> String

class AbstractProductB b where
    operationB :: b -> String

-- 具体产品A
data ConcreteProductA1 = ConcreteProductA1
data ConcreteProductA2 = ConcreteProductA2

instance AbstractProductA ConcreteProductA1 where
    operationA _ = "ConcreteProductA1 operation"

instance AbstractProductA ConcreteProductA2 where
    operationA _ = "ConcreteProductA2 operation"

-- 具体产品B
data ConcreteProductB1 = ConcreteProductB1
data ConcreteProductB2 = ConcreteProductB2

instance AbstractProductB ConcreteProductB1 where
    operationB _ = "ConcreteProductB1 operation"

instance AbstractProductB ConcreteProductB2 where
    operationB _ = "ConcreteProductB2 operation"

-- 抽象工厂
class AbstractFactory f where
    createProductA :: f -> Either ConcreteProductA1 ConcreteProductA2
    createProductB :: f -> Either ConcreteProductB1 ConcreteProductB2

-- 具体工厂
data ConcreteFactory1 = ConcreteFactory1
data ConcreteFactory2 = ConcreteFactory2

instance AbstractFactory ConcreteFactory1 where
    createProductA _ = Left ConcreteProductA1
    createProductB _ = Left ConcreteProductB1

instance AbstractFactory ConcreteFactory2 where
    createProductA _ = Right ConcreteProductA2
    createProductB _ = Right ConcreteProductB2

-- 泛型工厂
class GenericFactory f a where
    create :: f -> a

-- 配置驱动的工厂
data ConfigurableFactory = ConfigurableFactory String

data DevelopmentProduct = DevelopmentProduct
data ProductionProduct = ProductionProduct
data TestingProduct = TestingProduct
data DefaultProduct = DefaultProduct

instance Product DevelopmentProduct where
    operation _ = "Development product"

instance Product ProductionProduct where
    operation _ = "Production product"

instance Product TestingProduct where
    operation _ = "Testing product"

instance Product DefaultProduct where
    operation _ = "Default product"

createConfigurableProduct :: ConfigurableFactory -> Either DevelopmentProduct (Either ProductionProduct (Either TestingProduct DefaultProduct))
createConfigurableProduct (ConfigurableFactory config) = 
    case config of
        "development" -> Left DevelopmentProduct
        "production" -> Right (Left ProductionProduct)
        "testing" -> Right (Right (Left TestingProduct))
        _ -> Right (Right (Right DefaultProduct))

-- 使用示例
useSimpleFactory :: IO ()
useSimpleFactory = do
    let productA = createProduct "A"
    let productB = createProduct "B"
    case productA of
        Just (Left a) -> putStrLn $ operation a
        Just (Right b) -> putStrLn $ operation b
        Nothing -> putStrLn "Invalid product type"
    case productB of
        Just (Left a) -> putStrLn $ operation a
        Just (Right b) -> putStrLn $ operation b
        Nothing -> putStrLn "Invalid product type"

useFactoryMethod :: IO ()
useFactoryMethod = do
    let factoryA = ConcreteFactoryA
    let factoryB = ConcreteFactoryB
    let productA = createProduct factoryA
    let productB = createProduct factoryB
    case productA of
        Left a -> putStrLn $ operation a
        Right b -> putStrLn $ operation b
    case productB of
        Left a -> putStrLn $ operation a
        Right b -> putStrLn $ operation b

useAbstractFactory :: IO ()
useAbstractFactory = do
    let factory1 = ConcreteFactory1
    let factory2 = ConcreteFactory2
    let productA1 = createProductA factory1
    let productB1 = createProductB factory1
    let productA2 = createProductA factory2
    let productB2 = createProductB factory2
    
    case productA1 of
        Left a1 -> putStrLn $ operationA a1
        Right a2 -> putStrLn $ operationA a2
    case productB1 of
        Left b1 -> putStrLn $ operationB b1
        Right b2 -> putStrLn $ operationB b2
    case productA2 of
        Left a1 -> putStrLn $ operationA a1
        Right a2 -> putStrLn $ operationA a2
    case productB2 of
        Left b1 -> putStrLn $ operationB b1
        Right b2 -> putStrLn $ operationB b2
```

## Lean实现思路

```lean
-- 产品类型类
class Product (α : Type) where
  operation : α → String

-- 具体产品
inductive ConcreteProduct where
  | A : ConcreteProduct
  | B : ConcreteProduct

instance : Product ConcreteProduct where
  operation := fun
    | ConcreteProduct.A => "ConcreteProductA operation"
    | ConcreteProduct.B => "ConcreteProductB operation"

-- 简单工厂
def createProduct (productType : String) : Option ConcreteProduct :=
  match productType with
  | "A" => some ConcreteProduct.A
  | "B" => some ConcreteProduct.B
  | _ => none

-- 工厂方法模式
class Factory (α : Type) where
  createProduct : α → ConcreteProduct

inductive ConcreteFactory where
  | A : ConcreteFactory
  | B : ConcreteFactory

instance : Factory ConcreteFactory where
  createProduct := fun
    | ConcreteFactory.A => ConcreteProduct.A
    | ConcreteFactory.B => ConcreteProduct.B

-- 抽象工厂模式
class AbstractProductA (α : Type) where
  operationA : α → String

class AbstractProductB (α : Type) where
  operationB : α → String

-- 具体产品A
inductive ConcreteProductA where
  | A1 : ConcreteProductA
  | A2 : ConcreteProductA

instance : AbstractProductA ConcreteProductA where
  operationA := fun
    | ConcreteProductA.A1 => "ConcreteProductA1 operation"
    | ConcreteProductA.A2 => "ConcreteProductA2 operation"

-- 具体产品B
inductive ConcreteProductB where
  | B1 : ConcreteProductB
  | B2 : ConcreteProductB

instance : AbstractProductB ConcreteProductB where
  operationB := fun
    | ConcreteProductB.B1 => "ConcreteProductB1 operation"
    | ConcreteProductB.B2 => "ConcreteProductB2 operation"

-- 抽象工厂
class AbstractFactory (α : Type) where
  createProductA : α → ConcreteProductA
  createProductB : α → ConcreteProductB

-- 具体工厂
inductive ConcreteFactory where
  | Factory1 : ConcreteFactory
  | Factory2 : ConcreteFactory

instance : AbstractFactory ConcreteFactory where
  createProductA := fun
    | ConcreteFactory.Factory1 => ConcreteProductA.A1
    | ConcreteFactory.Factory2 => ConcreteProductA.A2
  createProductB := fun
    | ConcreteFactory.Factory1 => ConcreteProductB.B1
    | ConcreteFactory.Factory2 => ConcreteProductB.B2

-- 泛型工厂
class GenericFactory (α β : Type) where
  create : α → β

-- 配置驱动的工厂
structure ConfigurableFactory where
  config : String

inductive ConfigurableProduct where
  | Development : ConfigurableProduct
  | Production : ConfigurableProduct
  | Testing : ConfigurableProduct
  | Default : ConfigurableProduct

instance : Product ConfigurableProduct where
  operation := fun
    | ConfigurableProduct.Development => "Development product"
    | ConfigurableProduct.Production => "Production product"
    | ConfigurableProduct.Testing => "Testing product"
    | ConfigurableProduct.Default => "Default product"

def createConfigurableProduct (factory : ConfigurableFactory) : ConfigurableProduct :=
  match factory.config with
  | "development" => ConfigurableProduct.Development
  | "production" => ConfigurableProduct.Production
  | "testing" => ConfigurableProduct.Testing
  | _ => ConfigurableProduct.Default
```

## 应用场景

### 1. 数据库连接

- **连接池工厂**: 创建不同类型的数据库连接
- **配置驱动**: 根据环境创建不同配置的连接
- **异步工厂**: 异步创建数据库连接

### 2. UI组件

- **组件工厂**: 创建不同类型的UI组件
- **主题工厂**: 根据主题创建不同样式的组件
- **平台工厂**: 根据平台创建原生组件

### 3. 文件系统

- **文件工厂**: 创建不同类型的文件处理器
- **格式工厂**: 根据文件格式创建相应的处理器
- **压缩工厂**: 创建不同压缩算法的处理器

### 4. 网络通信

- **协议工厂**: 创建不同协议的客户端
- **序列化工厂**: 创建不同格式的序列化器
- **认证工厂**: 创建不同类型的认证机制

## 最佳实践

### 1. 设计原则

- 遵循开闭原则
- 使用依赖注入
- 避免过度设计

### 2. 性能考虑

- 使用对象池
- 延迟初始化
- 缓存工厂实例

### 3. 错误处理

- 提供默认实现
- 处理创建失败
- 记录错误日志

### 4. 测试策略

- 单元测试工厂
- 模拟产品对象
- 测试边界条件

## 性能考虑

### 1. 对象创建

- 创建开销
- 内存分配
- 垃圾回收

### 2. 工厂开销

- 工厂实例化
- 方法调用开销
- 类型检查

### 3. 缓存策略

- 对象缓存
- 工厂缓存
- 配置缓存

## 总结

工厂模式是创建对象的重要设计模式，通过封装对象创建过程，提高了代码的灵活性和可维护性。合理使用工厂模式可以简化代码结构，提高系统的可扩展性。
