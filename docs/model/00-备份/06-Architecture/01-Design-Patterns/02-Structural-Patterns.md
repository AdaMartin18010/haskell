# 结构型设计模式 - 形式化理论与Haskell实现

## 📋 概述

结构型设计模式关注类和对象的组合，提供灵活的结构化方式。本文档从形式化角度分析结构型模式，并提供Haskell实现。

## 🎯 核心概念

### 对象组合的形式化模型

#### 定义 1.1 (对象组合)

设 $U$ 为类型宇宙，对象组合定义为：
$$\text{compose} : A \times B \rightarrow C$$

其中 $A, B, C \in U$ 是类型。

#### 定义 1.2 (结构型模式)

结构型模式是一个四元组 $(S, C, \text{compose}, \text{decompose})$，其中：

- $S$ 是结构类型
- $C$ 是组件类型
- $\text{compose}$ 是组合函数
- $\text{decompose}$ 是分解函数

## 🔗 适配器模式 (Adapter Pattern)

### 形式化定义

#### 定义 2.1 (适配器模式)

适配器模式定义为：
$$\text{Adapter}_{A,B} = (A, B, \text{adapt}, \text{target})$$

其中：

- $A$ 是源类型
- $B$ 是目标类型
- $\text{adapt} : A \rightarrow B$ 是适配函数
- $\text{target} : B \rightarrow \text{Interface}$ 是目标接口

### Haskell实现

```haskell
-- 目标接口
class TargetInterface a where
    request :: a -> String

-- 源接口
class SourceInterface a where
    specificRequest :: a -> String

-- 具体源类
data SourceClass = SourceClass { sourceData :: String }

instance SourceInterface SourceClass where
    specificRequest (SourceClass data) = "Source: " ++ data

-- 适配器
data Adapter = Adapter { source :: SourceClass }

instance TargetInterface Adapter where
    request adapter = adapt (source adapter)
  where
    adapt :: SourceClass -> String
    adapt source = "Adapted: " ++ specificRequest source

-- 使用示例
exampleAdapter :: IO ()
exampleAdapter = do
    let source = SourceClass "Hello World"
    let adapter = Adapter source
    putStrLn $ request adapter
```

### 形式化证明

#### 定理 2.1 (适配器的兼容性)

对于任意适配器 $\text{Adapter}_{A,B}$，适配后的对象满足目标接口：
$$\forall a \in A, \text{target}(\text{adapt}(a)) \in \text{Interface}$$

**证明**：
适配器将源接口转换为目标接口，因此适配后的对象满足目标接口规范。

## 🎨 装饰器模式 (Decorator Pattern)

### 形式化定义

#### 定义 3.1 (装饰器模式)

装饰器模式定义为：
$$\text{Decorator}_A = (A, \text{decorate}, \text{base})$$

其中：

- $A$ 是基础类型
- $\text{decorate} : A \rightarrow A$ 是装饰函数
- $\text{base} : A \rightarrow A$ 是基础函数

### Haskell实现

```haskell
-- 基础组件接口
class Component a where
    operation :: a -> String

-- 具体组件
data ConcreteComponent = ConcreteComponent { componentData :: String }

instance Component ConcreteComponent where
    operation (ConcreteComponent data) = "Concrete: " ++ data

-- 装饰器基类
class Decorator d where
    type ComponentType d
    getComponent :: d -> ComponentType d
    decorate :: d -> String -> String

-- 具体装饰器
data BorderDecorator = BorderDecorator
    { component :: ConcreteComponent
    , borderStyle :: String
    }

instance Decorator BorderDecorator where
    type ComponentType BorderDecorator = ConcreteComponent
    getComponent = component
    decorate decorator text = 
        borderStyle decorator ++ " " ++ text ++ " " ++ borderStyle decorator

-- 装饰器组件实例
instance Component BorderDecorator where
    operation decorator = decorate decorator (operation (getComponent decorator))

-- 多重装饰器
data ColorDecorator = ColorDecorator
    { baseComponent :: ConcreteComponent
    , color :: String
    }

instance Decorator ColorDecorator where
    type ComponentType ColorDecorator = ConcreteComponent
    getComponent = baseComponent
    decorate decorator text = 
        "[" ++ color decorator ++ "]" ++ text ++ "[/" ++ color decorator ++ "]"

instance Component ColorDecorator where
    operation decorator = decorate decorator (operation (getComponent decorator))

-- 使用示例
exampleDecorator :: IO ()
exampleDecorator = do
    let component = ConcreteComponent "Hello"
    let bordered = BorderDecorator component "***"
    let colored = ColorDecorator component "red"
    putStrLn $ operation component
    putStrLn $ operation bordered
    putStrLn $ operation colored
```

### 形式化证明

#### 定理 3.1 (装饰器的可组合性)

对于任意装饰器 $\text{Decorator}_A$，装饰操作是可组合的：
$$\text{decorate}_1 \circ \text{decorate}_2 = \text{decorate}_{1,2}$$

**证明**：
装饰器可以链式组合，每个装饰器都增强基础组件的功能，组合后仍保持装饰器性质。

## 🏗️ 桥接模式 (Bridge Pattern)

### 形式化定义

#### 定义 4.1 (桥接模式)

桥接模式定义为：
$$\text{Bridge}_{A,B} = (A, B, \text{implement}, \text{abstract})$$

其中：

- $A$ 是抽象类型
- $B$ 是实现类型
- $\text{implement} : A \rightarrow B$ 是实现函数
- $\text{abstract} : B \rightarrow A$ 是抽象函数

### Haskell实现

```haskell
-- 实现接口
class Implementation a where
    operationImpl :: a -> String

-- 具体实现
data ConcreteImplementationA = ConcreteImplementationA

instance Implementation ConcreteImplementationA where
    operationImpl _ = "Implementation A"

data ConcreteImplementationB = ConcreteImplementationB

instance Implementation ConcreteImplementationB where
    operationImpl _ = "Implementation B"

-- 抽象接口
class Abstraction a where
    type ImplType a
    getImplementation :: a -> ImplType a
    operation :: a -> String

-- 具体抽象
data RefinedAbstraction impl = RefinedAbstraction
    { implementation :: impl
    }

instance Implementation impl => Abstraction (RefinedAbstraction impl) where
    type ImplType (RefinedAbstraction impl) = impl
    getImplementation = implementation
    operation abstraction = 
        "Refined: " ++ operationImpl (getImplementation abstraction)

-- 使用示例
exampleBridge :: IO ()
exampleBridge = do
    let implA = ConcreteImplementationA
    let implB = ConcreteImplementationB
    let abstractionA = RefinedAbstraction implA
    let abstractionB = RefinedAbstraction implB
    putStrLn $ operation abstractionA
    putStrLn $ operation abstractionB
```

### 形式化证明

#### 定理 4.1 (桥接的独立性)

对于任意桥接 $\text{Bridge}_{A,B}$，抽象和实现是独立的：
$$\text{abstract} \circ \text{implement} = \text{id}_A$$

**证明**：
桥接模式将抽象与实现分离，实现可以独立变化而不影响抽象。

## 🎭 外观模式 (Facade Pattern)

### 形式化定义

#### 定义 5.1 (外观模式)

外观模式定义为：
$$\text{Facade} = (S, \text{simplify}, \text{interface})$$

其中：

- $S$ 是子系统类型
- $\text{simplify} : S \rightarrow \text{SimpleInterface}$ 是简化函数
- $\text{interface} : \text{SimpleInterface} \rightarrow S$ 是接口函数

### Haskell实现

```haskell
-- 子系统组件
data SubsystemA = SubsystemA

class SubsystemAOps a where
    operationA1 :: a -> String
    operationA2 :: a -> String

instance SubsystemAOps SubsystemA where
    operationA1 _ = "SubsystemA.operation1"
    operationA2 _ = "SubsystemA.operation2"

data SubsystemB = SubsystemB

class SubsystemBOps a where
    operationB1 :: a -> String
    operationB2 :: a -> String

instance SubsystemBOps SubsystemB where
    operationB1 _ = "SubsystemB.operation1"
    operationB2 _ = "SubsystemB.operation2"

-- 外观
data Facade = Facade
    { subsystemA :: SubsystemA
    , subsystemB :: SubsystemB
    }

-- 简化的外观接口
class FacadeInterface a where
    simpleOperation :: a -> String
    complexOperation :: a -> String

instance FacadeInterface Facade where
    simpleOperation facade = 
        operationA1 (subsystemA facade) ++ " " ++ 
        operationB1 (subsystemB facade)
    
    complexOperation facade = 
        operationA1 (subsystemA facade) ++ " " ++
        operationA2 (subsystemA facade) ++ " " ++
        operationB1 (subsystemB facade) ++ " " ++
        operationB2 (subsystemB facade)

-- 使用示例
exampleFacade :: IO ()
exampleFacade = do
    let facade = Facade SubsystemA SubsystemB
    putStrLn $ simpleOperation facade
    putStrLn $ complexOperation facade
```

### 形式化证明

#### 定理 5.1 (外观的简化性)

对于任意外观 $\text{Facade}$，简化后的接口比原系统简单：
$$|\text{SimpleInterface}| < |S|$$

**证明**：
外观模式提供简化的接口，隐藏了子系统的复杂性，因此接口规模小于原系统。

## 🍃 享元模式 (Flyweight Pattern)

### 形式化定义

#### 定义 6.1 (享元模式)

享元模式定义为：
$$\text{Flyweight} = (I, S, \text{share}, \text{unique})$$

其中：

- $I$ 是内部状态类型
- $S$ 是外部状态类型
- $\text{share} : I \rightarrow \text{Shared}$ 是共享函数
- $\text{unique} : S \rightarrow \text{Unique}$ 是唯一函数

### Haskell实现

```haskell
-- 享元接口
class Flyweight f where
    type IntrinsicState f
    type ExtrinsicState f
    operation :: f -> ExtrinsicState f -> String

-- 具体享元
data ConcreteFlyweight = ConcreteFlyweight
    { intrinsicState :: String
    }

instance Flyweight ConcreteFlyweight where
    type IntrinsicState ConcreteFlyweight = String
    type ExtrinsicState ConcreteFlyweight = String
    operation flyweight extrinsic = 
        "Intrinsic: " ++ intrinsicState flyweight ++ 
        ", Extrinsic: " ++ extrinsic

-- 享元工厂
data FlyweightFactory = FlyweightFactory
    { flyweights :: Map String ConcreteFlyweight
    }

-- 获取享元
getFlyweight :: String -> FlyweightFactory -> (ConcreteFlyweight, FlyweightFactory)
getFlyweight key factory = 
    case Map.lookup key (flyweights factory) of
        Just flyweight -> (flyweight, factory)
        Nothing -> 
            let newFlyweight = ConcreteFlyweight key
                newFactory = factory { flyweights = Map.insert key newFlyweight (flyweights factory) }
            in (newFlyweight, newFactory)

-- 使用示例
exampleFlyweight :: IO ()
exampleFlyweight = do
    let factory = FlyweightFactory Map.empty
    let (flyweight1, factory1) = getFlyweight "shared" factory
    let (flyweight2, factory2) = getFlyweight "shared" factory1
    putStrLn $ operation flyweight1 "state1"
    putStrLn $ operation flyweight2 "state2"
    putStrLn $ "Same flyweight: " ++ show (flyweight1 == flyweight2)
```

### 形式化证明

#### 定理 6.1 (享元的共享性)

对于任意享元 $\text{Flyweight}$，相同内部状态的对象被共享：
$$\forall i \in I, \text{share}(i) = \text{shared}$$

**证明**：
享元模式共享相同内部状态的对象，减少内存使用。

## 🔗 代理模式 (Proxy Pattern)

### 形式化定义

#### 定义 7.1 (代理模式)

代理模式定义为：
$$\text{Proxy}_A = (A, \text{control}, \text{access})$$

其中：

- $A$ 是目标类型
- $\text{control} : A \rightarrow \text{Controlled}$ 是控制函数
- $\text{access} : \text{Controlled} \rightarrow A$ 是访问函数

### Haskell实现

```haskell
-- 主题接口
class Subject a where
    request :: a -> String

-- 真实主题
data RealSubject = RealSubject

instance Subject RealSubject where
    request _ = "RealSubject: Handling request"

-- 代理
data Proxy = Proxy
    { realSubject :: Maybe RealSubject
    , accessCount :: Int
    }

instance Subject Proxy where
    request proxy = 
        case realSubject proxy of
            Just subject -> 
                let newProxy = proxy { accessCount = accessCount proxy + 1 }
                in "Proxy: " ++ request subject ++ " (access #" ++ show (accessCount proxy) ++ ")"
            Nothing -> "Proxy: Creating RealSubject and handling request"

-- 虚拟代理
data VirtualProxy = VirtualProxy
    { lazySubject :: Maybe RealSubject
    }

instance Subject VirtualProxy where
    request proxy = 
        case lazySubject proxy of
            Just subject -> "VirtualProxy: " ++ request subject
            Nothing -> "VirtualProxy: Creating RealSubject on demand"

-- 保护代理
data ProtectionProxy = ProtectionProxy
    { protectedSubject :: RealSubject
    , accessLevel :: String
    }

instance Subject ProtectionProxy where
    request proxy = 
        if accessLevel proxy == "admin"
        then "ProtectionProxy: " ++ request (protectedSubject proxy)
        else "ProtectionProxy: Access denied"

-- 使用示例
exampleProxy :: IO ()
exampleProxy = do
    let proxy = Proxy Nothing 0
    let virtualProxy = VirtualProxy Nothing
    let protectionProxy = ProtectionProxy RealSubject "user"
    putStrLn $ request proxy
    putStrLn $ request virtualProxy
    putStrLn $ request protectionProxy
```

### 形式化证明

#### 定理 7.1 (代理的透明性)

对于任意代理 $\text{Proxy}_A$，代理对客户端透明：
$$\text{access} \circ \text{control} = \text{id}_A$$

**证明**：
代理模式提供与真实对象相同的接口，对客户端透明。

## 🔗 模式组合与关系

### 模式间的形式化关系

#### 定义 8.1 (模式组合)

两个结构型模式 $P_1$ 和 $P_2$ 的组合定义为：
$$P_1 \circ P_2 = (S_1 \times S_2, C_1 \times C_2, \text{compose}_{1,2}, \text{decompose}_{1,2})$$

### Haskell实现

```haskell
-- 组合模式示例：装饰器 + 适配器
data DecoratedAdapter = DecoratedAdapter
    { adapter :: Adapter
    , decorator :: BorderDecorator
    }

instance TargetInterface DecoratedAdapter where
    request decoratedAdapter = 
        operation (decorator decoratedAdapter) ++ 
        " -> " ++ request (adapter decoratedAdapter)
```

## 📊 性能分析与优化

### 时间复杂度分析

| 模式 | 组合时间复杂度 | 访问时间复杂度 | 内存复杂度 |
|------|----------------|----------------|------------|
| 适配器模式 | O(1) | O(1) | O(1) |
| 装饰器模式 | O(n) | O(n) | O(n) |
| 桥接模式 | O(1) | O(1) | O(1) |
| 外观模式 | O(1) | O(n) | O(1) |
| 享元模式 | O(log n) | O(1) | O(1) |
| 代理模式 | O(1) | O(1) | O(1) |

### 内存优化策略

```haskell
-- 对象池与享元结合
data OptimizedFlyweight = OptimizedFlyweight
    { sharedState :: String
    , referenceCount :: Int
    }

-- 引用计数管理
incrementRef :: OptimizedFlyweight -> OptimizedFlyweight
incrementRef flyweight = flyweight { referenceCount = referenceCount flyweight + 1 }

decrementRef :: OptimizedFlyweight -> Maybe OptimizedFlyweight
decrementRef flyweight = 
    if referenceCount flyweight <= 1
    then Nothing
    else Just $ flyweight { referenceCount = referenceCount flyweight - 1 }
```

## 🎯 最佳实践

### 1. 模式选择原则

- **接口不匹配**：使用适配器模式
- **功能扩展**：使用装饰器模式
- **抽象分离**：使用桥接模式
- **简化接口**：使用外观模式
- **内存优化**：使用享元模式
- **访问控制**：使用代理模式

### 2. 性能考虑

- 合理使用享元模式减少内存使用
- 避免过度装饰导致性能下降
- 考虑代理模式的延迟加载
- 优化对象池的使用

### 3. 可维护性

- 保持接口的一致性
- 避免深层嵌套
- 提供清晰的文档
- 进行充分的测试

## 🔗 相关链接

- [创建型设计模式](../01-Creational-Patterns/README.md)
- [行为型设计模式](../03-Behavioral-Patterns/README.md)
- [并发设计模式](../04-Concurrent-Patterns/README.md)
- [设计模式总览](../README.md)

---

*本文档提供了结构型设计模式的完整形式化理论和Haskell实现，为软件架构设计提供了坚实的理论基础。*
