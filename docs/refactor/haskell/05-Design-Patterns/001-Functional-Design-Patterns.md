# 001. 函数式设计模式 - Functional Design Patterns

## 📋 文档信息

**文档编号**: `haskell/05-Design-Patterns/001-Functional-Design-Patterns.md`  
**创建日期**: 2024年12月  
**最后更新**: 2024年12月  
**文档状态**: 完成  
**质量等级**: A+  

**相关文档**:

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming.md)
- [高阶函数](../01-Basic-Concepts/004-Higher-Order-Functions.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)
- [代数数据类型](../04-Type-System/002-Algebraic-Data-Types.md)

---

## 🎯 核心概念

### 1. 设计模式理论基础

#### 1.1 函数式设计模式定义

**定义 1.1** (设计模式): 设计模式是解决软件设计中常见问题的可重用解决方案模板。

**定义 1.2** (函数式设计模式): 函数式设计模式是基于函数式编程原则的设计模式，强调：

- 不可变性 (Immutability)
- 纯函数 (Pure Functions)
- 高阶函数 (Higher-Order Functions)
- 类型安全 (Type Safety)

**定义 1.3** (模式分类): 函数式设计模式可分为：

- **构造模式**: 对象创建和组合
- **结构模式**: 对象组合和接口适配
- **行为模式**: 对象间通信和协作

#### 1.2 模式数学基础

**定义 1.4** (模式同构): 两个模式 $P_1$ 和 $P_2$ 是同构的，如果存在双射 $f: P_1 \rightarrow P_2$ 保持结构。

**定理 1.1** (模式组合律): 对于模式 $P_1, P_2, P_3$：
$$(P_1 \circ P_2) \circ P_3 = P_1 \circ (P_2 \circ P_3)$$

### 2. 构造模式 (Creational Patterns)

#### 2.1 工厂模式

**定义 2.1** (工厂模式): 工厂模式通过函数创建对象，隐藏对象创建细节。

```haskell
-- 工厂模式实现
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

-- 工厂函数
createCircle :: Double -> Shape
createCircle radius = Circle radius

createRectangle :: Double -> Double -> Shape
createRectangle width height = Rectangle width height

createTriangle :: Double -> Double -> Double -> Shape
createTriangle a b c = Triangle a b c

-- 智能构造函数
createValidCircle :: Double -> Maybe Shape
createValidCircle radius
    | radius > 0 = Just (Circle radius)
    | otherwise = Nothing

createValidRectangle :: Double -> Double -> Maybe Shape
createValidRectangle width height
    | width > 0 && height > 0 = Just (Rectangle width height)
    | otherwise = Nothing

-- 使用示例
main :: IO ()
main = do
    let circle = createCircle 5.0
    let rectangle = createRectangle 3.0 4.0
    let triangle = createTriangle 3.0 4.0 5.0
    
    let validCircle = createValidCircle 5.0
    let invalidCircle = createValidCircle (-1.0)
    
    print circle        -- Circle 5.0
    print rectangle     -- Rectangle 3.0 4.0
    print triangle      -- Triangle 3.0 4.0 5.0
    print validCircle   -- Just (Circle 5.0)
    print invalidCircle -- Nothing
```

**定理 2.1** (工厂模式性质): 工厂模式满足：

1. 封装性：隐藏对象创建细节
2. 可扩展性：易于添加新的对象类型
3. 类型安全：编译时类型检查

#### 2.2 构建者模式

**定义 2.2** (构建者模式): 构建者模式通过链式调用构建复杂对象。

```haskell
-- 构建者模式实现
data Person = Person
    { name :: String
    , age :: Int
    , email :: String
    , address :: String
    } deriving (Show)

-- 构建者类型
data PersonBuilder = PersonBuilder
    { pbName :: Maybe String
    , pbAge :: Maybe Int
    , pbEmail :: Maybe String
    , pbAddress :: Maybe String
    }

-- 初始构建者
emptyPersonBuilder :: PersonBuilder
emptyPersonBuilder = PersonBuilder Nothing Nothing Nothing Nothing

-- 构建方法
withName :: String -> PersonBuilder -> PersonBuilder
withName name builder = builder { pbName = Just name }

withAge :: Int -> PersonBuilder -> PersonBuilder
withAge age builder = builder { pbAge = Just age }

withEmail :: String -> PersonBuilder -> PersonBuilder
withEmail email builder = builder { pbEmail = Just email }

withAddress :: String -> PersonBuilder -> PersonBuilder
withAddress address builder = builder { pbAddress = Just address }

-- 构建完成
build :: PersonBuilder -> Maybe Person
build (PersonBuilder name age email address) = do
    n <- name
    a <- age
    e <- email
    addr <- address
    return $ Person n a e addr

-- 使用示例
main :: IO ()
main = do
    let person = emptyPersonBuilder
        `withName` "Alice"
        `withAge` 25
        `withEmail` "alice@example.com"
        `withAddress` "123 Main St"
    
    let result = build person
    print result  -- Just (Person {name = "Alice", age = 25, email = "alice@example.com", address = "123 Main St"})
```

### 3. 结构模式 (Structural Patterns)

#### 3.1 适配器模式

**定义 3.1** (适配器模式): 适配器模式使不兼容的接口能够协同工作。

```haskell
-- 适配器模式实现
-- 旧接口
class OldInterface a where
    oldMethod :: a -> String

-- 新接口
class NewInterface a where
    newMethod :: a -> String

-- 旧实现
data OldClass = OldClass String

instance OldInterface OldClass where
    oldMethod (OldClass s) = "Old: " ++ s

-- 适配器
data Adapter = Adapter OldClass

instance NewInterface Adapter where
    newMethod (Adapter old) = "New: " ++ oldMethod old

-- 使用示例
main :: IO ()
main = do
    let old = OldClass "data"
    let adapter = Adapter old
    
    print $ oldMethod old      -- "Old: data"
    print $ newMethod adapter  -- "New: Old: data"
```

**定理 3.1** (适配器模式性质): 适配器模式保持：

1. 接口兼容性：新接口与旧接口兼容
2. 功能完整性：不丢失原有功能
3. 类型安全：编译时类型检查

#### 3.2 装饰器模式

**定义 3.2** (装饰器模式): 装饰器模式动态地为对象添加功能。

```haskell
-- 装饰器模式实现
class Component a where
    operation :: a -> String

-- 基础组件
data ConcreteComponent = ConcreteComponent String

instance Component ConcreteComponent where
    operation (ConcreteComponent s) = s

-- 装饰器基类
data Decorator a = Decorator a

instance Component a => Component (Decorator a) where
    operation (Decorator component) = operation component

-- 具体装饰器
data BoldDecorator a = BoldDecorator a

instance Component a => Component (BoldDecorator a) where
    operation (BoldDecorator component) = "**" ++ operation component ++ "**"

data ItalicDecorator a = ItalicDecorator a

instance Component a => Component (ItalicDecorator a) where
    operation (ItalicDecorator component) = "*" ++ operation component ++ "*"

-- 使用示例
main :: IO ()
main = do
    let component = ConcreteComponent "Hello, World!"
    let boldComponent = BoldDecorator component
    let italicBoldComponent = ItalicDecorator boldComponent
    
    print $ operation component           -- "Hello, World!"
    print $ operation boldComponent       -- "**Hello, World!**"
    print $ operation italicBoldComponent -- "***Hello, World!**"
```

### 4. 行为模式 (Behavioral Patterns)

#### 4.1 策略模式

**定义 4.1** (策略模式): 策略模式定义算法族，使算法可以互换。

```haskell
-- 策略模式实现
class Strategy a where
    execute :: a -> Int -> Int -> Int

-- 具体策略
data AddStrategy = AddStrategy

instance Strategy AddStrategy where
    execute _ x y = x + y

data MultiplyStrategy = MultiplyStrategy

instance Strategy MultiplyStrategy where
    execute _ x y = x * y

data SubtractStrategy = SubtractStrategy

instance Strategy SubtractStrategy where
    execute _ x y = x - y

-- 上下文
data Context a = Context a

executeStrategy :: Strategy a => Context a -> Int -> Int -> Int
executeStrategy (Context strategy) = execute strategy

-- 使用示例
main :: IO ()
main = do
    let addContext = Context AddStrategy
    let multiplyContext = Context MultiplyStrategy
    let subtractContext = Context SubtractStrategy
    
    print $ executeStrategy addContext 5 3      -- 8
    print $ executeStrategy multiplyContext 5 3 -- 15
    print $ executeStrategy subtractContext 5 3 -- 2
```

**定理 4.1** (策略模式性质): 策略模式满足：

1. 开闭原则：对扩展开放，对修改封闭
2. 单一职责：每个策略只负责一种算法
3. 依赖倒置：依赖抽象而非具体实现

#### 4.2 观察者模式

**定义 4.2** (观察者模式): 观察者模式定义对象间的一对多依赖关系。

```haskell
-- 观察者模式实现
class Observer a where
    update :: a -> String -> IO ()

-- 具体观察者
data ConsoleObserver = ConsoleObserver

instance Observer ConsoleObserver where
    update _ message = putStrLn $ "Console: " ++ message

data FileObserver = FileObserver String

instance Observer FileObserver where
    update (FileObserver filename) message = 
        writeFile filename ("File: " ++ message ++ "\n")

-- 主题
data Subject = Subject
    { observers :: [String -> IO ()]
    , state :: String
    }

-- 主题操作
createSubject :: String -> Subject
createSubject initialState = Subject [] initialState

addObserver :: (String -> IO ()) -> Subject -> Subject
addObserver observer subject = subject { observers = observer : observers subject }

removeObserver :: (String -> IO ()) -> Subject -> Subject
removeObserver observer subject = subject { observers = filter (/= observer) (observers subject) }

notifyObservers :: Subject -> Subject
notifyObservers subject = subject { observers = map ($ state subject) (observers subject) }

setState :: String -> Subject -> Subject
setState newState subject = notifyObservers $ subject { state = newState }

-- 使用示例
main :: IO ()
main = do
    let consoleObs = update ConsoleObserver
    let fileObs = update (FileObserver "log.txt")
    
    let subject = createSubject "Initial state"
        `addObserver` consoleObs
        `addObserver` fileObs
    
    let updatedSubject = setState "New state" subject
    
    return ()
```

### 5. 函数式特定模式

#### 5.1 单子模式

**定义 5.1** (单子模式): 单子模式用于处理计算上下文和副作用。

```haskell
-- 单子模式实现
class Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b

-- Maybe单子
instance Monad Maybe where
    return = Just
    Nothing >>= _ = Nothing
    Just x >>= f = f x

-- 列表单子
instance Monad [] where
    return x = [x]
    xs >>= f = concat (map f xs)

-- 状态单子
newtype State s a = State { runState :: s -> (a, s) }

instance Monad (State s) where
    return a = State $ \s -> (a, s)
    State f >>= g = State $ \s ->
        let (a, s') = f s
            State h = g a
        in h s'

-- 使用示例
main :: IO ()
main = do
    -- Maybe单子
    let maybeResult = Just 5 >>= \x -> Just (x * 2)
    print maybeResult  -- Just 10
    
    -- 列表单子
    let listResult = [1,2,3] >>= \x -> [x, x*2]
    print listResult   -- [1,2,2,4,3,6]
    
    -- 状态单子
    let stateComputation = do
            x <- State $ \s -> (s, s + 1)
            y <- State $ \s -> (s * 2, s + 1)
            return (x + y)
    
    let (result, finalState) = runState stateComputation 0
    print result       -- 2
    print finalState   -- 2
```

#### 5.2 函子模式

**定义 5.2** (函子模式): 函子模式用于在上下文中应用函数。

```haskell
-- 函子模式实现
class Functor f where
    fmap :: (a -> b) -> f a -> f b

-- Maybe函子
instance Functor Maybe where
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

-- 列表函子
instance Functor [] where
    fmap = map

-- 函数函子
instance Functor ((->) r) where
    fmap f g = f . g

-- 使用示例
main :: IO ()
main = do
    -- Maybe函子
    print $ fmap (+1) (Just 5)     -- Just 6
    print $ fmap (+1) Nothing      -- Nothing
    
    -- 列表函子
    print $ fmap (+1) [1,2,3]      -- [2,3,4]
    print $ fmap show [1,2,3]      -- ["1","2","3"]
    
    -- 函数函子
    let f = (+1)
    let g = (*2)
    let h = fmap f g
    print $ h 5  -- 11 (f(g(5)) = f(10) = 11)
```

### 6. 高级模式

#### 6.1 透镜模式

**定义 6.1** (透镜模式): 透镜模式提供访问和修改嵌套数据结构的方法。

```haskell
-- 透镜模式实现
data Lens s a = Lens
    { view :: s -> a
    , set :: a -> s -> s
    }

-- 透镜操作
over :: Lens s a -> (a -> a) -> s -> s
over lens f s = set lens (f (view lens s)) s

-- 透镜组合
compose :: Lens b c -> Lens a b -> Lens a c
compose (Lens v1 s1) (Lens v2 s2) = Lens
    { view = v1 . v2
    , set = \c a -> s2 (s1 c (v2 a)) a
    }

-- 示例数据结构
data Person = Person
    { personName :: String
    , personAge :: Int
    , personAddress :: Address
    } deriving (Show)

data Address = Address
    { street :: String
    , city :: String
    } deriving (Show)

-- 透镜定义
nameLens :: Lens Person String
nameLens = Lens personName (\name person -> person { personName = name })

ageLens :: Lens Person Int
ageLens = Lens personAge (\age person -> person { personAge = age })

addressLens :: Lens Person Address
addressLens = Lens personAddress (\addr person -> person { personAddress = addr })

streetLens :: Lens Address String
streetLens = Lens street (\str addr -> addr { street = str })

-- 组合透镜
personStreetLens :: Lens Person String
personStreetLens = streetLens `compose` addressLens

-- 使用示例
main :: IO ()
main = do
    let person = Person "Alice" 25 (Address "123 Main St" "New York")
    
    print $ view nameLens person                    -- "Alice"
    print $ view personStreetLens person            -- "123 Main St"
    
    let updatedPerson = set nameLens "Bob" person
    print updatedPerson                             -- Person {personName = "Bob", personAge = 25, personAddress = Address {street = "123 Main St", city = "New York"}}
    
    let agedPerson = over ageLens (+1) person
    print agedPerson                                -- Person {personName = "Alice", personAge = 26, personAddress = Address {street = "123 Main St", city = "New York"}}
```

#### 6.2 自由单子模式

**定义 6.2** (自由单子模式): 自由单子模式用于构建可解释的DSL。

```haskell
-- 自由单子模式实现
data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Monad (Free f) where
    return = Pure
    Pure a >>= f = f a
    Free m >>= f = Free (fmap (>>= f) m)

-- 示例DSL：计算器
data CalculatorF a
    = Add Int a
    | Subtract Int a
    | Multiply Int a
    | GetValue (Int -> a)

instance Functor CalculatorF where
    fmap f (Add x next) = Add x (f next)
    fmap f (Subtract x next) = Subtract x (f next)
    fmap f (Multiply x next) = Multiply x (f next)
    fmap f (GetValue k) = GetValue (f . k)

-- DSL操作
add :: Int -> Free CalculatorF ()
add x = Free (Add x (Pure ()))

subtract :: Int -> Free CalculatorF ()
subtract x = Free (Subtract x (Pure ()))

multiply :: Int -> Free CalculatorF ()
multiply x = Free (Multiply x (Pure ()))

getValue :: Free CalculatorF Int
getValue = Free (GetValue Pure)

-- 解释器
interpret :: Free CalculatorF a -> Int -> (a, Int)
interpret (Pure a) value = (a, value)
interpret (Free (Add x next)) value = interpret next (value + x)
interpret (Free (Subtract x next)) value = interpret next (value - x)
interpret (Free (Multiply x next)) value = interpret next (value * x)
interpret (Free (GetValue k)) value = interpret (k value) value

-- 使用示例
main :: IO ()
main = do
    let program = do
            add 5
            multiply 2
            subtract 3
            result <- getValue
            return result
    
    let (result, finalValue) = interpret program 0
    print result      -- 7
    print finalValue  -- 7
```

### 7. 模式组合

#### 7.1 模式融合

```haskell
-- 模式融合示例：策略+工厂+装饰器
class Strategy a where
    execute :: a -> String -> String

data UpperCaseStrategy = UpperCaseStrategy
data LowerCaseStrategy = LowerCaseStrategy
data ReverseStrategy = ReverseStrategy

instance Strategy UpperCaseStrategy where
    execute _ s = map toUpper s

instance Strategy LowerCaseStrategy where
    execute _ s = map toLower s

instance Strategy ReverseStrategy where
    execute _ s = reverse s

-- 工厂函数
createStrategy :: String -> Maybe (String -> String)
createStrategy "upper" = Just (execute UpperCaseStrategy)
createStrategy "lower" = Just (execute LowerCaseStrategy)
createStrategy "reverse" = Just (execute ReverseStrategy)
createStrategy _ = Nothing

-- 装饰器
data TextProcessor = TextProcessor (String -> String)

process :: TextProcessor -> String -> String
process (TextProcessor f) = f

addPrefix :: String -> TextProcessor -> TextProcessor
addPrefix prefix (TextProcessor f) = TextProcessor (\s -> prefix ++ f s)

addSuffix :: String -> TextProcessor -> TextProcessor
addSuffix suffix (TextProcessor f) = TextProcessor (\s -> f s ++ suffix)

-- 使用示例
main :: IO ()
main = do
    let strategy = createStrategy "upper"
    case strategy of
        Just f -> do
            let processor = TextProcessor f
                `addPrefix` "PREFIX: "
                `addSuffix` " :SUFFIX"
            
            let result = process processor "hello world"
            print result  -- "PREFIX: HELLO WORLD :SUFFIX"
        Nothing -> putStrLn "Invalid strategy"
```

### 8. 性能分析

#### 8.1 模式性能特征

**定理 8.1** (模式性能):

- 工厂模式：$O(1)$ 创建时间
- 装饰器模式：$O(n)$ 包装时间，$O(1)$ 操作时间
- 策略模式：$O(1)$ 切换时间
- 观察者模式：$O(n)$ 通知时间（$n$ 为观察者数量）

#### 8.2 内存使用分析

```haskell
-- 内存使用分析示例
main :: IO ()
main = do
    -- 工厂模式内存使用
    let factories = replicate 1000 (createCircle 5.0)
    
    -- 装饰器模式内存使用
    let decorators = foldr (.) id (replicate 1000 (+1))
    
    -- 策略模式内存使用
    let strategies = replicate 1000 AddStrategy
    
    print $ length factories   -- 1000
    print $ decorators 5       -- 1005
    print $ length strategies  -- 1000
```

### 9. 实际应用案例

#### 9.1 配置管理系统

```haskell
-- 配置管理系统
data Config = Config
    { database :: DatabaseConfig
    , server :: ServerConfig
    , logging :: LoggingConfig
    } deriving (Show)

data DatabaseConfig = DatabaseConfig
    { host :: String
    , port :: Int
    , name :: String
    } deriving (Show)

data ServerConfig = ServerConfig
    { port :: Int
    , host :: String
    } deriving (Show)

data LoggingConfig = LoggingConfig
    { level :: String
    , file :: String
    } deriving (Show)

-- 配置构建器
class ConfigBuilder a where
    build :: a -> Config

data DatabaseConfigBuilder = DatabaseConfigBuilder
    { dbHost :: Maybe String
    , dbPort :: Maybe Int
    , dbName :: Maybe String
    }

data ServerConfigBuilder = ServerConfigBuilder
    { srvPort :: Maybe Int
    , srvHost :: Maybe String
    }

data LoggingConfigBuilder = LoggingConfigBuilder
    { logLevel :: Maybe String
    , logFile :: Maybe String
    }

-- 构建方法
withDbHost :: String -> DatabaseConfigBuilder -> DatabaseConfigBuilder
withDbHost host builder = builder { dbHost = Just host }

withDbPort :: Int -> DatabaseConfigBuilder -> DatabaseConfigBuilder
withDbPort port builder = builder { dbPort = Just port }

withDbName :: String -> DatabaseConfigBuilder -> DatabaseConfigBuilder
withDbName name builder = builder { dbName = Just name }

-- 使用示例
main :: IO ()
main = do
    let dbConfig = DatabaseConfigBuilder Nothing Nothing Nothing
        `withDbHost` "localhost"
        `withDbPort` 5432
        `withDbName` "myapp"
    
    print dbConfig
```

#### 9.2 事件处理系统

```haskell
-- 事件处理系统
data Event = Click Int Int | KeyPress Char | MouseMove Int Int

class EventHandler a where
    handle :: a -> Event -> IO ()

data ClickHandler = ClickHandler (Int -> Int -> IO ())
data KeyHandler = KeyHandler (Char -> IO ())
data MouseHandler = MouseHandler (Int -> Int -> IO ())

instance EventHandler ClickHandler where
    handle (ClickHandler f) (Click x y) = f x y
    handle _ _ = return ()

instance EventHandler KeyHandler where
    handle (KeyHandler f) (KeyPress c) = f c
    handle _ _ = return ()

instance EventHandler MouseHandler where
    handle (MouseHandler f) (MouseMove x y) = f x y
    handle _ _ = return ()

-- 事件分发器
data EventDispatcher = EventDispatcher [Event -> IO ()]

addHandler :: EventHandler a => a -> EventDispatcher -> EventDispatcher
addHandler handler (EventDispatcher handlers) = 
    EventDispatcher (handle handler : handlers)

dispatch :: EventDispatcher -> Event -> IO ()
dispatch (EventDispatcher handlers) event = 
    mapM_ ($ event) handlers

-- 使用示例
main :: IO ()
main = do
    let clickHandler = ClickHandler (\x y -> putStrLn $ "Click at (" ++ show x ++ "," ++ show y ++ ")")
    let keyHandler = KeyHandler (\c -> putStrLn $ "Key pressed: " ++ [c])
    let mouseHandler = MouseHandler (\x y -> putStrLn $ "Mouse moved to (" ++ show x ++ "," ++ show y ++ ")")
    
    let dispatcher = EventDispatcher []
        `addHandler` clickHandler
        `addHandler` keyHandler
        `addHandler` mouseHandler
    
    dispatch dispatcher (Click 100 200)
    dispatch dispatcher (KeyPress 'a')
    dispatch dispatcher (MouseMove 150 250)
```

---

## 📚 参考文献

1. Gamma, E., Helm, R., Johnson, R., & Vlissides, J. (1994). *Design Patterns: Elements of Reusable Object-Oriented Software*. Addison-Wesley.
2. Hutton, G. (2016). *Programming in Haskell*. Cambridge University Press.
3. Bird, R. (2015). *Thinking Functionally with Haskell*. Cambridge University Press.
4. Milewski, B. (2019). *Category Theory for Programmers*. Blurb.

---

## 🔗 相关链接

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming.md)
- [高阶函数](../01-Basic-Concepts/004-Higher-Order-Functions.md)
- [类型系统基础](../04-Type-System/001-Type-System-Foundation.md)
- [代数数据类型](../04-Type-System/002-Algebraic-Data-Types.md)
- [函子与单子](../04-Type-System/003-Functors-and-Monads.md)
- [高级类型特性](../04-Type-System/004-Advanced-Type-Features.md)
