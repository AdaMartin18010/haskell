# 001. 设计模式 (Design Patterns)

## 📋 文档信息

- **文档编号**: 001
- **所属层次**: 实现层 (Implementation Layer)
- **创建时间**: 2024-12-19
- **最后更新**: 2024-12-19
- **版本**: 1.0.0

## 🔗 相关文档

### 上层文档

- [[07-Architecture/002-Software-Architecture]] - 软件架构

### 同层文档

- [[08-Implementation/002-Algorithm-Design]] - 算法设计

---

## 🎯 概述

设计模式是软件开发中常见问题的可重用解决方案。本文档系统梳理设计模式的分类、实现原理、Haskell实现、复杂度分析及其在现代软件开发中的应用。

## 📚 理论基础

### 1. 设计模式基本概念

**定义 1.1** (设计模式): 设计模式是软件设计中常见问题的典型解决方案。

**定义 1.2** (模式要素): 每个模式包含名称、问题、解决方案、效果四个要素。

**定义 1.3** (模式分类): 设计模式分为创建型、结构型、行为型三大类。

### 2. 创建型模式

#### 2.1 单例模式 (Singleton)

- 确保一个类只有一个实例
- 提供全局访问点
- 延迟初始化

#### 2.2 工厂模式 (Factory)

- 封装对象创建逻辑
- 支持多态
- 解耦客户端与具体类

#### 2.3 建造者模式 (Builder)

- 分步骤构建复杂对象
- 支持不同表示
- 控制构建过程

### 3. 结构型模式

#### 3.1 适配器模式 (Adapter)

- 兼容不兼容接口
- 包装现有类
- 支持多态

#### 3.2 装饰器模式 (Decorator)

- 动态添加功能
- 保持接口一致
- 组合优于继承

#### 3.3 代理模式 (Proxy)

- 控制对象访问
- 延迟加载
- 访问控制

### 4. 行为型模式

#### 4.1 观察者模式 (Observer)

- 一对多依赖关系
- 松耦合通信
- 事件驱动

#### 4.2 策略模式 (Strategy)

- 封装算法族
- 运行时切换
- 消除条件语句

#### 4.3 命令模式 (Command)

- 封装请求
- 支持撤销
- 队列处理

## 💻 Haskell 实现

```haskell
-- 设计模式核心类型
module DesignPatterns where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Reader

-- 单例模式
data Singleton = Singleton
  { instanceId :: String
  , data_ :: String
  } deriving (Show, Eq)

-- 单例管理器
data SingletonManager = SingletonManager
  { instances :: Map String Singleton
  } deriving (Show)

-- 创建或获取单例
getSingleton :: SingletonManager -> String -> String -> (SingletonManager, Singleton)
getSingleton manager id_ data_ = 
  case Map.lookup id_ (instances manager) of
    Just instance_ -> (manager, instance_)
    Nothing -> 
      let newInstance = Singleton id_ data_
          newManager = manager { instances = Map.insert id_ newInstance (instances manager) }
      in (newManager, newInstance)

-- 工厂模式
class Factory a where
  create :: String -> a

-- 具体产品
data Product = Product
  { productId :: String
  , productType :: String
  , productData :: String
  } deriving (Show, Eq)

-- 产品工厂
data ProductFactory = ProductFactory
  { factoryType :: String
  } deriving (Show)

instance Factory Product where
  create factoryType = Product "1" factoryType "default"

-- 建造者模式
data Builder = Builder
  { parts :: [String]
  } deriving (Show, Eq)

-- 建造者接口
class ObjectBuilder a where
  buildPart :: a -> String -> a
  getResult :: a -> String

instance ObjectBuilder Builder where
  buildPart builder part = builder { parts = parts builder ++ [part] }
  getResult builder = unwords (parts builder)

-- 适配器模式
-- 目标接口
class Target a where
  request :: a -> String

-- 被适配的类
data Adaptee = Adaptee
  { adapteeData :: String
  } deriving (Show, Eq)

-- 适配器
data Adapter = Adapter
  { adaptee :: Adaptee
  } deriving (Show, Eq)

instance Target Adapter where
  request adapter = "Adapted: " ++ adapteeData (adaptee adapter)

-- 装饰器模式
-- 组件接口
class Component a where
  operation :: a -> String

-- 具体组件
data ConcreteComponent = ConcreteComponent
  { componentData :: String
  } deriving (Show, Eq)

instance Component ConcreteComponent where
  operation component = "Concrete: " ++ componentData component

-- 装饰器基类
data Decorator = Decorator
  { component :: ConcreteComponent
  } deriving (Show, Eq)

instance Component Decorator where
  operation decorator = "Decorated: " ++ operation (component decorator)

-- 具体装饰器
data ConcreteDecorator = ConcreteDecorator
  { decorator :: Decorator
  , additionalData :: String
  } deriving (Show, Eq)

instance Component ConcreteDecorator where
  operation concreteDecorator = 
    operation (decorator concreteDecorator) ++ " + " ++ additionalData concreteDecorator

-- 代理模式
-- 主题接口
class Subject a where
  request :: a -> String

-- 真实主题
data RealSubject = RealSubject
  { subjectData :: String
  } deriving (Show, Eq)

instance Subject RealSubject where
  request subject = "Real: " ++ subjectData subject

-- 代理
data Proxy = Proxy
  { realSubject :: Maybe RealSubject
  } deriving (Show, Eq)

instance Subject Proxy where
  request proxy = 
    case realSubject proxy of
      Just subject -> request subject
      Nothing -> "Proxy: Creating real subject..."

-- 观察者模式
-- 观察者接口
class Observer a where
  update :: a -> String -> a

-- 具体观察者
data ConcreteObserver = ConcreteObserver
  { observerId :: String
  , observerState :: String
  } deriving (Show, Eq)

instance Observer ConcreteObserver where
  update observer message = observer { observerState = message }

-- 主题
data Subject_ = Subject_
  { observers :: [ConcreteObserver]
  , subjectState :: String
  } deriving (Show, Eq)

-- 附加观察者
attach :: Subject_ -> ConcreteObserver -> Subject_
attach subject observer = subject { observers = observers subject ++ [observer] }

-- 通知观察者
notify :: Subject_ -> Subject_
notify subject = 
  let updatedObservers = map (\observer -> update observer (subjectState subject)) (observers subject)
  in subject { observers = updatedObservers }

-- 策略模式
-- 策略接口
class Strategy a where
  algorithm :: a -> String -> String

-- 具体策略
data ConcreteStrategyA = ConcreteStrategyA deriving (Show, Eq)
data ConcreteStrategyB = ConcreteStrategyB deriving (Show, Eq)

instance Strategy ConcreteStrategyA where
  algorithm _ input = "Strategy A: " ++ input

instance Strategy ConcreteStrategyB where
  algorithm _ input = "Strategy B: " ++ input

-- 上下文
data Context = Context
  { strategy :: Maybe (String -> String)
  } deriving (Show)

-- 执行策略
executeStrategy :: Context -> String -> String
executeStrategy context input = 
  case strategy context of
    Just strat -> strat input
    Nothing -> "No strategy"

-- 命令模式
-- 命令接口
class Command a where
  execute :: a -> String
  undo :: a -> String

-- 具体命令
data ConcreteCommand = ConcreteCommand
  { receiver :: String
  , action :: String
  } deriving (Show, Eq)

instance Command ConcreteCommand where
  execute command = "Execute: " ++ action command ++ " on " ++ receiver command
  undo command = "Undo: " ++ action command ++ " on " ++ receiver command

-- 调用者
data Invoker = Invoker
  { commands :: [ConcreteCommand]
  } deriving (Show, Eq)

-- 执行命令
executeCommands :: Invoker -> [String]
executeCommands invoker = map execute (commands invoker)

-- 模式管理器
data PatternManager = PatternManager
  { patterns :: Map String PatternInfo
  } deriving (Show)

-- 模式信息
data PatternInfo = PatternInfo
  { patternName :: String
  , patternType :: PatternType
  , description :: String
  , useCases :: [String]
  } deriving (Show, Eq)

-- 模式类型
data PatternType = 
    Creational
  | Structural
  | Behavioral
  deriving (Show, Eq)

-- 注册模式
registerPattern :: PatternManager -> PatternInfo -> PatternManager
registerPattern manager patternInfo = 
  manager { patterns = Map.insert (patternName patternInfo) patternInfo (patterns manager) }

-- 查找模式
findPattern :: PatternManager -> String -> Maybe PatternInfo
findPattern manager name = Map.lookup name (patterns manager)

-- 模式分析器
data PatternAnalyzer = PatternAnalyzer
  { manager :: PatternManager
  , analysisRules :: [AnalysisRule]
  } deriving (Show)

-- 分析规则
data AnalysisRule = 
    ApplicabilityRule
  | ComplexityRule
  | MaintainabilityRule
  deriving (Show, Eq)

-- 分析结果
data PatternAnalysisResult = PatternAnalysisResult
  { pattern :: String
  , rule :: AnalysisRule
  , status :: AnalysisStatus
  , message :: String
  , recommendations :: [String]
  } deriving (Show, Eq)

-- 分析状态
data AnalysisStatus = 
    Suitable
  | Unsuitable
  | NeedsModification
  deriving (Show, Eq)

-- 分析模式适用性
analyzePatternApplicability :: PatternAnalyzer -> String -> String -> [PatternAnalysisResult]
analyzePatternApplicability analyzer patternName context = 
  let patternInfo = findPattern (manager analyzer) patternName
  in case patternInfo of
       Just info -> analyzePattern analyzer info context
       Nothing -> [PatternAnalysisResult patternName ApplicabilityRule Unsuitable "模式不存在" []]

-- 分析特定模式
analyzePattern :: PatternAnalyzer -> PatternInfo -> String -> [PatternAnalysisResult]
analyzePattern analyzer info context = 
  [PatternAnalysisResult (patternName info) ApplicabilityRule Suitable "模式适用" ["考虑实现细节"]]
```

## 📊 复杂度分析

### 1. 模式实现复杂度

**定理 4.1** (单例模式复杂度): 单例模式的实现复杂度为 $O(1)$。

**证明**: 单例模式只需要简单的实例检查和创建。

**定理 4.2** (工厂模式复杂度): 工厂模式的实现复杂度为 $O(1)$。

**证明**: 工厂模式只需要根据类型创建对象。

**定理 4.3** (观察者模式复杂度): 观察者模式的实现复杂度为 $O(n)$，其中 $n$ 是观察者数量。

**证明**: 需要通知所有观察者。

### 2. 空间复杂度

**定理 4.4** (模式空间复杂度): 大多数设计模式的空间复杂度为 $O(1)$，除了需要存储多个对象的模式。

**证明**: 大多数模式只需要存储引用和基本数据。

## 🔗 与其他理论的关系

### 1. 与软件架构的关系

设计模式是软件架构的微观体现，软件架构是设计模式的宏观组织。

### 2. 与面向对象的关系

设计模式基于面向对象原则，体现了封装、继承、多态等概念。

### 3. 与重构的关系

设计模式为重构提供目标，重构为实现设计模式提供手段。

### 4. 与代码质量的关系

设计模式提高代码的可读性、可维护性和可扩展性。

## 🔬 应用实例

### 1. 编译器中的设计模式

```haskell
-- 编译器中的设计模式示例
compilerPatterns :: PatternManager
compilerPatterns = PatternManager $ Map.fromList
  [ ("lexer-factory", PatternInfo "Lexer Factory" Creational "创建不同类型的词法分析器" ["支持多种语言"])
  , ("parser-strategy", PatternInfo "Parser Strategy" Behavioral "支持不同的解析策略" ["LL解析", "LR解析"])
  , ("ast-visitor", PatternInfo "AST Visitor" Behavioral "遍历抽象语法树" ["代码生成", "优化"])
  , ("optimizer-decorator", PatternInfo "Optimizer Decorator" Structural "动态添加优化" ["常量折叠", "死代码消除"])
  ]
```

### 2. 微服务中的设计模式

```haskell
-- 微服务中的设计模式示例
microservicePatterns :: PatternManager
microservicePatterns = PatternManager $ Map.fromList
  [ ("service-factory", PatternInfo "Service Factory" Creational "创建服务实例" ["负载均衡", "服务发现"])
  , ("circuit-breaker", PatternInfo "Circuit Breaker" Behavioral "故障隔离" ["服务降级", "故障恢复"])
  , ("api-gateway", PatternInfo "API Gateway" Structural "统一入口" ["路由", "认证", "限流"])
  , ("event-sourcing", PatternInfo "Event Sourcing" Behavioral "事件溯源" ["数据一致性", "审计"])
  ]
```

## 📚 参考文献

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). *Design Patterns: Elements of Reusable Object-Oriented Software*. Addison-Wesley.

2. Freeman, E., Robson, E., Sierra, K., & Bates, B. (2004). *Head First Design Patterns*. O'Reilly Media.

3. Martin, R. C. (2000). *Design Principles and Design Patterns*. Object Mentor.

4. Larman, C. (2004). *Applying UML and Patterns: An Introduction to Object-Oriented Analysis and Design and Iterative Development* (3rd ed.). Prentice Hall.

5. Shalloway, A., & Trott, J. R. (2004). *Design Patterns Explained: A New Perspective on Object-Oriented Design* (2nd ed.). Addison-Wesley.

---

**文档版本**: 1.0.0  
**最后更新**: 2024年12月19日  
**维护者**: AI Assistant
