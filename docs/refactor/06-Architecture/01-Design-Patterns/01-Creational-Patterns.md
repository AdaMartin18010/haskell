# 创建型设计模式 - 形式化理论与Haskell实现

## 📋 概述

创建型设计模式关注对象的创建过程，提供灵活的对象创建机制。本文档从形式化角度分析创建型模式，并提供Haskell实现。

## 🎯 核心概念

### 对象创建的形式化模型

#### 定义 1.1 (对象创建函数)
设 $U$ 为类型宇宙，$A \in U$ 为类型，对象创建函数定义为：
$$\text{create}_A : \text{Config}_A \rightarrow A$$

其中 $\text{Config}_A$ 是类型 $A$ 的配置空间。

#### 定义 1.2 (创建型模式)
创建型模式是一个三元组 $(C, F, \phi)$，其中：
- $C$ 是配置类型
- $F$ 是工厂函数类型
- $\phi$ 是创建策略

## 🏭 工厂模式 (Factory Pattern)

### 形式化定义

#### 定义 2.1 (工厂模式)
工厂模式定义为：
$$\text{Factory}_A = (C_A, \text{create}_A, \text{strategy}_A)$$

其中：
- $C_A$ 是产品配置类型
- $\text{create}_A : C_A \rightarrow A$ 是创建函数
- $\text{strategy}_A : C_A \rightarrow \text{Strategy}$ 是创建策略

### Haskell实现

```haskell
-- 产品类型类
class Product a where
    type Config a
    create :: Config a -> a
    describe :: a -> String

-- 工厂类型类
class Factory f where
    type ProductType f
    makeProduct :: f -> Config (ProductType f) -> ProductType f

-- 具体产品
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

instance Product Shape where
    type Config Shape = String
    create "circle" = Circle 1.0
    create "rectangle" = Rectangle 1.0 1.0
    create "triangle" = Triangle 1.0 1.0 1.0
    create _ = Circle 1.0
    
    describe (Circle r) = "Circle with radius " ++ show r
    describe (Rectangle w h) = "Rectangle " ++ show w ++ "x" ++ show h
    describe (Triangle a b c) = "Triangle with sides " ++ show [a,b,c]

-- 形状工厂
data ShapeFactory = ShapeFactory

instance Factory ShapeFactory where
    type ProductType ShapeFactory = Shape
    makeProduct ShapeFactory config = create config

-- 使用示例
example :: IO ()
example = do
    let factory = ShapeFactory
    let circle = makeProduct factory "circle"
    let rectangle = makeProduct factory "rectangle"
    putStrLn $ describe circle
    putStrLn $ describe rectangle
```

### 形式化证明

#### 定理 2.1 (工厂模式的可组合性)
对于任意类型 $A, B$，如果存在工厂 $\text{Factory}_A$ 和 $\text{Factory}_B$，则存在复合工厂 $\text{Factory}_{A \times B}$。

**证明**：
构造复合工厂：
$$\text{Factory}_{A \times B} = (C_A \times C_B, \text{create}_{A \times B}, \text{strategy}_{A \times B})$$

其中：
$$\text{create}_{A \times B}(c_A, c_B) = (\text{create}_A(c_A), \text{create}_B(c_B))$$

## 🏗️ 抽象工厂模式 (Abstract Factory Pattern)

### 形式化定义

#### 定义 3.1 (抽象工厂)
抽象工厂是一个四元组：
$$\text{AbstractFactory} = (F, P, \text{create}, \text{family})$$

其中：
- $F$ 是工厂族类型
- $P$ 是产品族类型
- $\text{create} : F \rightarrow P$ 是创建函数
- $\text{family} : F \rightarrow \text{ProductFamily}$ 是产品族映射

### Haskell实现

```haskell
-- 产品族类型类
class ProductFamily f where
    type AbstractProduct f
    type ConcreteProduct f
    createProduct :: f -> ConcreteProduct f

-- 具体产品族
data UIFamily = ModernUI | ClassicUI

-- 按钮产品
data Button = ModernButton String | ClassicButton String

-- 文本框产品
data TextBox = ModernTextBox String | ClassicTextBox String

-- UI工厂
class UIFactory f where
    createButton :: f -> String -> Button
    createTextBox :: f -> String -> TextBox

-- 现代UI工厂
data ModernUIFactory = ModernUIFactory

instance UIFactory ModernUIFactory where
    createButton ModernUIFactory text = ModernButton text
    createTextBox ModernUIFactory text = ModernTextBox text

-- 经典UI工厂
data ClassicUIFactory = ClassicUIFactory

instance UIFactory ClassicUIFactory where
    createButton ClassicUIFactory text = ClassicButton text
    createTextBox ClassicUIFactory text = ClassicTextBox text

-- 工厂选择器
getUIFactory :: UIFamily -> (forall f. UIFactory f => f -> r) -> r
getUIFactory ModernUI f = f ModernUIFactory
getUIFactory ClassicUI f = f ClassicUIFactory

-- 使用示例
createUI :: UIFamily -> (Button, TextBox)
createUI family = getUIFactory family $ \factory ->
    (createButton factory "Click me", createTextBox factory "Enter text")
```

### 形式化证明

#### 定理 3.1 (抽象工厂的一致性)
对于任意抽象工厂 $\text{AbstractFactory}$，其创建的产品族具有一致性：
$$\forall f \in F, \text{family}(\text{create}(f)) = \text{family}(f)$$

**证明**：
由抽象工厂的定义，$\text{create}$ 函数保持产品族的一致性，因此：
$$\text{family}(\text{create}(f)) = \text{family}(f)$$

## 🔨 建造者模式 (Builder Pattern)

### 形式化定义

#### 定义 4.1 (建造者模式)
建造者模式定义为：
$$\text{Builder}_A = (S, \text{build}, \text{reset})$$

其中：
- $S$ 是构建状态类型
- $\text{build} : S \rightarrow A$ 是构建函数
- $\text{reset} : S \rightarrow S$ 是重置函数

### Haskell实现

```haskell
-- 构建器类型类
class Builder b where
    type Product b
    type State b
    reset :: State b -> State b
    build :: State b -> Product b

-- 具体构建器
data CarBuilder = CarBuilder
    { engine :: String
    , wheels :: Int
    , color :: String
    }

data Car = Car
    { carEngine :: String
    , carWheels :: Int
    , carColor :: String
    }

instance Builder CarBuilder where
    type Product CarBuilder = Car
    type State CarBuilder = CarBuilder
    
    reset _ = CarBuilder "" 0 ""
    build builder = Car (engine builder) (wheels builder) (color builder)

-- 构建器操作
setEngine :: String -> CarBuilder -> CarBuilder
setEngine eng builder = builder { engine = eng }

setWheels :: Int -> CarBuilder -> CarBuilder
setWheels w builder = builder { wheels = w }

setColor :: String -> CarBuilder -> CarBuilder
setColor c builder = builder { color = c }

-- 导演类
class Director d where
    type BuilderType d
    construct :: d -> State (BuilderType d) -> Product (BuilderType d)

data CarDirector = CarDirector

instance Director CarDirector where
    type BuilderType CarDirector = CarBuilder
    construct CarDirector state = build $ 
        setEngine "V8" $ 
        setWheels 4 $ 
        setColor "Red" state

-- 使用示例
buildCar :: Car
buildCar = construct CarDirector (reset undefined)
```

### 形式化证明

#### 定理 4.1 (建造者的幂等性)
对于任意建造者 $\text{Builder}_A$，重置操作是幂等的：
$$\text{reset} \circ \text{reset} = \text{reset}$$

**证明**：
重置操作将状态恢复到初始状态，再次重置不会改变状态，因此：
$$\text{reset} \circ \text{reset} = \text{reset}$$

## 🎭 原型模式 (Prototype Pattern)

### 形式化定义

#### 定义 5.1 (原型模式)
原型模式定义为：
$$\text{Prototype}_A = (A, \text{clone}, \text{prototype})$$

其中：
- $A$ 是原型类型
- $\text{clone} : A \rightarrow A$ 是克隆函数
- $\text{prototype} : A \rightarrow A$ 是原型函数

### Haskell实现

```haskell
-- 原型类型类
class Prototype a where
    clone :: a -> a
    prototype :: a -> a

-- 具体原型
data Document = Document
    { title :: String
    , content :: String
    , author :: String
    }

instance Prototype Document where
    clone doc = doc
    prototype doc = Document (title doc) "" (author doc)

-- 原型注册表
data PrototypeRegistry = PrototypeRegistry
    { prototypes :: Map String Document
    }

-- 注册原型
registerPrototype :: String -> Document -> PrototypeRegistry -> PrototypeRegistry
registerPrototype name doc registry = 
    registry { prototypes = Map.insert name doc (prototypes registry) }

-- 获取原型
getPrototype :: String -> PrototypeRegistry -> Maybe Document
getPrototype name registry = Map.lookup name (prototypes registry)

-- 克隆原型
clonePrototype :: String -> PrototypeRegistry -> Maybe Document
clonePrototype name registry = clone <$> getPrototype name registry

-- 使用示例
examplePrototype :: IO ()
examplePrototype = do
    let doc = Document "Template" "This is a template" "System"
    let registry = PrototypeRegistry Map.empty
    let registry' = registerPrototype "template" doc registry
    case clonePrototype "template" registry' of
        Just cloned -> putStrLn $ "Cloned: " ++ title cloned
        Nothing -> putStrLn "Prototype not found"
```

### 形式化证明

#### 定理 5.1 (克隆的恒等性)
对于任意原型 $p \in A$，克隆操作满足：
$$\text{clone}(p) \equiv p$$

**证明**：
克隆操作创建对象的副本，在语义上等价于原对象，因此：
$$\text{clone}(p) \equiv p$$

## 🎯 单例模式 (Singleton Pattern)

### 形式化定义

#### 定义 6.1 (单例模式)
单例模式定义为：
$$\text{Singleton}_A = (A, \text{instance}, \text{unique})$$

其中：
- $A$ 是单例类型
- $\text{instance} : \text{Unit} \rightarrow A$ 是实例获取函数
- $\text{unique} : A \rightarrow \text{Bool}$ 是唯一性验证函数

### Haskell实现

```haskell
-- 单例类型类
class Singleton a where
    getInstance :: a
    isUnique :: a -> Bool

-- 具体单例
data DatabaseConnection = DatabaseConnection
    { connectionId :: String
    , isConnected :: Bool
    }

instance Singleton DatabaseConnection where
    getInstance = DatabaseConnection "db-001" True
    isUnique _ = True

-- 线程安全单例
import Control.Concurrent.MVar

data ThreadSafeSingleton = ThreadSafeSingleton
    { instanceMVar :: MVar DatabaseConnection
    }

newThreadSafeSingleton :: IO ThreadSafeSingleton
newThreadSafeSingleton = do
    mvar <- newMVar getInstance
    return $ ThreadSafeSingleton mvar

getThreadSafeInstance :: ThreadSafeSingleton -> IO DatabaseConnection
getThreadSafeInstance singleton = readMVar (instanceMVar singleton)

-- 使用示例
exampleSingleton :: IO ()
exampleSingleton = do
    let db1 = getInstance
    let db2 = getInstance
    putStrLn $ "Same instance: " ++ show (db1 == db2)
    putStrLn $ "Is unique: " ++ show (isUnique db1)
```

### 形式化证明

#### 定理 6.1 (单例的唯一性)
对于任意单例 $\text{Singleton}_A$，其实例是唯一的：
$$\forall x, y \in A, x = y$$

**证明**：
单例模式确保只有一个实例存在，因此任意两个实例都相等：
$$\forall x, y \in A, x = y$$

## 🔗 模式组合与关系

### 模式间的形式化关系

#### 定义 7.1 (模式组合)
两个模式 $P_1 = (C_1, F_1, \phi_1)$ 和 $P_2 = (C_2, F_2, \phi_2)$ 的组合定义为：
$$P_1 \circ P_2 = (C_1 \times C_2, F_1 \circ F_2, \phi_1 \circ \phi_2)$$

### Haskell实现

```haskell
-- 组合模式
data CompositeFactory f1 f2 = CompositeFactory f1 f2

instance (Factory f1, Factory f2) => Factory (CompositeFactory f1 f2) where
    type ProductType (CompositeFactory f1 f2) = (ProductType f1, ProductType f2)
    makeProduct (CompositeFactory f1 f2) (c1, c2) = 
        (makeProduct f1 c1, makeProduct f2 c2)

-- 使用示例
compositeExample :: IO ()
compositeExample = do
    let shapeFactory = ShapeFactory
    let uiFactory = ModernUIFactory
    let composite = CompositeFactory shapeFactory uiFactory
    let (shape, button) = makeProduct composite ("circle", "Click me")
    putStrLn $ "Created: " ++ describe shape
    putStrLn $ "Button: " ++ show button
```

## 📊 性能分析与优化

### 时间复杂度分析

| 模式 | 创建时间复杂度 | 空间复杂度 | 适用场景 |
|------|----------------|------------|----------|
| 工厂模式 | O(1) | O(1) | 简单对象创建 |
| 抽象工厂 | O(1) | O(n) | 产品族创建 |
| 建造者模式 | O(n) | O(n) | 复杂对象构建 |
| 原型模式 | O(1) | O(n) | 对象复制 |
| 单例模式 | O(1) | O(1) | 全局唯一实例 |

### 内存优化策略

```haskell
-- 对象池模式
data ObjectPool a = ObjectPool
    { available :: [a]
    , inUse :: [a]
    }

-- 创建对象池
createPool :: (a -> a) -> Int -> a -> ObjectPool a
createPool clone size template = ObjectPool 
    (replicate size (clone template)) 
    []

-- 获取对象
acquire :: ObjectPool a -> Maybe (a, ObjectPool a)
acquire (ObjectPool [] _) = Nothing
acquire (ObjectPool (x:xs) inUse) = 
    Just (x, ObjectPool xs (x:inUse))

-- 释放对象
release :: a -> ObjectPool a -> ObjectPool a
release obj (ObjectPool available inUse) = 
    ObjectPool (obj:available) (filter (/= obj) inUse)
```

## 🎯 最佳实践

### 1. 模式选择原则

- **简单创建**：使用工厂模式
- **产品族**：使用抽象工厂模式
- **复杂构建**：使用建造者模式
- **对象复制**：使用原型模式
- **全局唯一**：使用单例模式

### 2. 性能考虑

- 避免过度使用单例模式
- 合理使用对象池
- 考虑内存管理
- 优化创建过程

### 3. 可维护性

- 保持接口简洁
- 遵循单一职责原则
- 提供清晰的文档
- 进行充分的测试

## 🔗 相关链接

- [结构型设计模式](../02-Structural-Patterns/README.md)
- [行为型设计模式](../03-Behavioral-Patterns/README.md)
- [并发设计模式](../04-Concurrent-Patterns/README.md)
- [设计模式总览](../README.md)

---

*本文档提供了创建型设计模式的完整形式化理论和Haskell实现，为软件架构设计提供了坚实的理论基础。* 