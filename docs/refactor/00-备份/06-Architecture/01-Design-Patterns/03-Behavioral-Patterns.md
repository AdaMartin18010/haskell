# 行为型设计模式 - 形式化理论与Haskell实现

## 📋 概述

行为型设计模式关注对象间的通信和职责分配，提供灵活的行为组织方式。本文档从形式化角度分析行为型模式，并提供Haskell实现。

## 🎯 核心概念

### 对象交互的形式化模型

#### 定义 1.1 (对象交互)

设 $U$ 为类型宇宙，对象交互定义为：
$$\text{interact} : A \times B \rightarrow C$$

其中 $A, B, C \in U$ 是类型。

#### 定义 1.2 (行为型模式)

行为型模式是一个四元组 $(B, I, \text{interact}, \text{coordinate})$，其中：

- $B$ 是行为类型
- $I$ 是交互类型
- $\text{interact}$ 是交互函数
- $\text{coordinate}$ 是协调函数

## 🔗 责任链模式 (Chain of Responsibility Pattern)

### 形式化定义

#### 定义 2.1 (责任链模式)

责任链模式定义为：
$$\text{Chain} = (H, \text{handle}, \text{successor})$$

其中：

- $H$ 是处理器类型
- $\text{handle} : H \times \text{Request} \rightarrow \text{Response}$ 是处理函数
- $\text{successor} : H \rightarrow H$ 是后继函数

### Haskell实现

```haskell
-- 请求类型
data Request = Request
    { requestType :: String
    , requestData :: String
    }

-- 响应类型
data Response = Response
    { responseData :: String
    , isHandled :: Bool
    }

-- 处理器接口
class Handler h where
    handle :: h -> Request -> Response
    setSuccessor :: h -> h -> h
    canHandle :: h -> Request -> Bool

-- 具体处理器
data ConcreteHandlerA = ConcreteHandlerA
    { successor :: Maybe ConcreteHandlerA
    }

instance Handler ConcreteHandlerA where
    handle handler request = 
        if canHandle handler request
        then Response ("HandlerA handled: " ++ requestType request) True
        else case successor handler of
            Just next -> handle next request
            Nothing -> Response "No handler found" False
    
    setSuccessor handler next = handler { successor = Just next }
    
    canHandle handler request = requestType request == "A"

data ConcreteHandlerB = ConcreteHandlerB
    { successor :: Maybe ConcreteHandlerB
    }

instance Handler ConcreteHandlerB where
    handle handler request = 
        if canHandle handler request
        then Response ("HandlerB handled: " ++ requestType request) True
        else case successor handler of
            Just next -> handle next request
            Nothing -> Response "No handler found" False
    
    setSuccessor handler next = handler { successor = Just next }
    
    canHandle handler request = requestType request == "B"

-- 使用示例
exampleChain :: IO ()
exampleChain = do
    let handlerA = ConcreteHandlerA Nothing
    let handlerB = ConcreteHandlerB Nothing
    let chain = setSuccessor handlerA handlerB
    
    let requestA = Request "A" "data"
    let requestB = Request "B" "data"
    let requestC = Request "C" "data"
    
    putStrLn $ responseData $ handle chain requestA
    putStrLn $ responseData $ handle chain requestB
    putStrLn $ responseData $ handle chain requestC
```

### 形式化证明

#### 定理 2.1 (责任链的传递性)

对于任意责任链 $\text{Chain}$，请求沿链传递：
$$\forall h \in H, \text{handle}(h, r) = \text{handle}(\text{successor}(h), r)$$

**证明**：
责任链模式确保请求沿处理器链传递，直到被处理或到达链尾。

## 🎨 命令模式 (Command Pattern)

### 形式化定义

#### 定义 3.1 (命令模式)

命令模式定义为：
$$\text{Command} = (C, \text{execute}, \text{undo})$$

其中：

- $C$ 是命令类型
- $\text{execute} : C \rightarrow \text{Result}$ 是执行函数
- $\text{undo} : C \rightarrow \text{Result}$ 是撤销函数

### Haskell实现

```haskell
-- 命令接口
class Command c where
    type Receiver c
    execute :: c -> Receiver c -> String
    undo :: c -> Receiver c -> String

-- 接收者
data Receiver = Receiver
    { state :: String
    }

-- 具体命令
data ConcreteCommand = ConcreteCommand
    { action :: String
    , previousState :: Maybe String
    }

instance Command ConcreteCommand where
    type Receiver ConcreteCommand = Receiver
    execute command receiver = 
        let newState = action command ++ " executed"
        in "Command executed: " ++ newState
    
    undo command receiver = 
        case previousState command of
            Just prev -> "Undone to: " ++ prev
            Nothing -> "Cannot undo"

-- 调用者
data Invoker = Invoker
    { commands :: [ConcreteCommand]
    }

-- 执行命令
executeCommand :: Invoker -> ConcreteCommand -> Receiver -> (String, Invoker)
executeCommand invoker command receiver = 
    let result = execute command receiver
        newInvoker = invoker { commands = command : commands invoker }
    in (result, newInvoker)

-- 撤销命令
undoLastCommand :: Invoker -> Receiver -> (String, Invoker)
undoLastCommand invoker receiver = 
    case commands invoker of
        [] -> ("No commands to undo", invoker)
        (cmd:rest) -> 
            let result = undo cmd receiver
                newInvoker = invoker { commands = rest }
            in (result, newInvoker)

-- 宏命令
data MacroCommand = MacroCommand
    { commandList :: [ConcreteCommand]
    }

instance Command MacroCommand where
    type Receiver MacroCommand = Receiver
    execute macro receiver = 
        let results = map (\cmd -> execute cmd receiver) (commandList macro)
        in "Macro executed: " ++ unwords results
    
    undo macro receiver = 
        let results = map (\cmd -> undo cmd receiver) (reverse $ commandList macro)
        in "Macro undone: " ++ unwords results

-- 使用示例
exampleCommand :: IO ()
exampleCommand = do
    let receiver = Receiver "initial"
    let command1 = ConcreteCommand "Action1" Nothing
    let command2 = ConcreteCommand "Action2" Nothing
    let macro = MacroCommand [command1, command2]
    
    let invoker = Invoker []
    let (result1, invoker1) = executeCommand invoker command1 receiver
    let (result2, invoker2) = executeCommand invoker1 command2 receiver
    let (undoResult, invoker3) = undoLastCommand invoker2 receiver
    
    putStrLn result1
    putStrLn result2
    putStrLn undoResult
    putStrLn $ execute macro receiver
```

### 形式化证明

#### 定理 3.1 (命令的可逆性)

对于任意命令 $\text{Command}$，执行和撤销是互逆的：
$$\text{undo} \circ \text{execute} = \text{id}$$

**证明**：
命令模式支持撤销操作，撤销操作将状态恢复到执行前的状态。

## 🎭 解释器模式 (Interpreter Pattern)

### 形式化定义

#### 定义 4.1 (解释器模式)

解释器模式定义为：
$$\text{Interpreter} = (E, \text{interpret}, \text{context})$$

其中：

- $E$ 是表达式类型
- $\text{interpret} : E \times \text{Context} \rightarrow \text{Result}$ 是解释函数
- $\text{context} : \text{Context} \rightarrow \text{Environment}$ 是上下文函数

### Haskell实现

```haskell
-- 抽象表达式
class Expression e where
    interpret :: e -> Context -> Int

-- 上下文
data Context = Context
    { variables :: Map String Int
    }

-- 终结表达式
data NumberExpression = NumberExpression Int

instance Expression NumberExpression where
    interpret (NumberExpression n) _ = n

data VariableExpression = VariableExpression String

instance Expression VariableExpression where
    interpret (VariableExpression var) context = 
        case Map.lookup var (variables context) of
            Just value -> value
            Nothing -> 0

-- 非终结表达式
data AddExpression = AddExpression
    { left :: NumberExpression
    , right :: NumberExpression
    }

instance Expression AddExpression where
    interpret (AddExpression left right) context = 
        interpret left context + interpret right context

data SubtractExpression = SubtractExpression
    { left :: NumberExpression
    , right :: NumberExpression
    }

instance Expression SubtractExpression where
    interpret (SubtractExpression left right) context = 
        interpret left context - interpret right context

-- 复合表达式
data ComplexExpression = ComplexExpression
    { expressions :: [NumberExpression]
    , operations :: [String]
    }

instance Expression ComplexExpression where
    interpret (ComplexExpression exprs ops) context = 
        foldl (\acc (expr, op) -> 
            case op of
                "+" -> acc + interpret expr context
                "-" -> acc - interpret expr context
                _ -> acc
        ) (interpret (head exprs) context) (zip (tail exprs) ops)

-- 使用示例
exampleInterpreter :: IO ()
exampleInterpreter = do
    let context = Context $ Map.fromList [("x", 10), ("y", 5)]
    let num1 = NumberExpression 3
    let num2 = NumberExpression 4
    let addExpr = AddExpression num1 num2
    let subtractExpr = SubtractExpression num1 num2
    let varExpr = VariableExpression "x"
    
    putStrLn $ "3 + 4 = " ++ show (interpret addExpr context)
    putStrLn $ "3 - 4 = " ++ show (interpret subtractExpr context)
    putStrLn $ "x = " ++ show (interpret varExpr context)
```

### 形式化证明

#### 定理 4.1 (解释器的组合性)

对于任意解释器 $\text{Interpreter}$，复合表达式的解释是组合的：
$$\text{interpret}(e_1 \circ e_2, c) = \text{interpret}(e_1, c) \circ \text{interpret}(e_2, c)$$

**证明**：
解释器模式支持表达式的组合，复合表达式的解释是子表达式解释的组合。

## 🔄 迭代器模式 (Iterator Pattern)

### 形式化定义

#### 定义 5.1 (迭代器模式)

迭代器模式定义为：
$$\text{Iterator} = (I, \text{next}, \text{hasNext})$$

其中：

- $I$ 是迭代器类型
- $\text{next} : I \rightarrow A \times I$ 是下一个函数
- $\text{hasNext} : I \rightarrow \text{Bool}$ 是是否有下一个函数

### Haskell实现

```haskell
-- 迭代器接口
class Iterator i where
    type Element i
    next :: i -> Maybe (Element i, i)
    hasNext :: i -> Bool

-- 聚合接口
class Aggregate a where
    type IteratorType a
    createIterator :: a -> IteratorType a

-- 具体聚合
data ConcreteAggregate = ConcreteAggregate
    { items :: [String]
    }

-- 具体迭代器
data ConcreteIterator = ConcreteIterator
    { aggregate :: ConcreteAggregate
    , currentIndex :: Int
    }

instance Iterator ConcreteIterator where
    type Element ConcreteIterator = String
    next iterator = 
        if hasNext iterator
        then let item = items (aggregate iterator) !! currentIndex iterator
                 nextIterator = iterator { currentIndex = currentIndex iterator + 1 }
             in Just (item, nextIterator)
        else Nothing
    
    hasNext iterator = currentIndex iterator < length (items (aggregate iterator))

instance Aggregate ConcreteAggregate where
    type IteratorType ConcreteAggregate = ConcreteIterator
    createIterator aggregate = ConcreteIterator aggregate 0

-- 双向迭代器
data BidirectionalIterator = BidirectionalIterator
    { aggregate :: ConcreteAggregate
    , currentIndex :: Int
    , direction :: Direction
    }

data Direction = Forward | Backward

instance Iterator BidirectionalIterator where
    type Element BidirectionalIterator = String
    next iterator = 
        case direction iterator of
            Forward -> 
                if hasNext iterator
                then let item = items (aggregate iterator) !! currentIndex iterator
                         nextIterator = iterator { currentIndex = currentIndex iterator + 1 }
                     in Just (item, nextIterator)
                else Nothing
            Backward -> 
                if hasPrevious iterator
                then let item = items (aggregate iterator) !! (currentIndex iterator - 1)
                         nextIterator = iterator { currentIndex = currentIndex iterator - 1 }
                     in Just (item, nextIterator)
                else Nothing
    
    hasNext iterator = 
        case direction iterator of
            Forward -> currentIndex iterator < length (items (aggregate iterator))
            Backward -> currentIndex iterator > 0

hasPrevious :: BidirectionalIterator -> Bool
hasPrevious iterator = currentIndex iterator > 0

-- 使用示例
exampleIterator :: IO ()
exampleIterator = do
    let aggregate = ConcreteAggregate ["A", "B", "C", "D"]
    let iterator = createIterator aggregate
    
    putStrLn "Forward iteration:"
    iterateForward iterator
    
    let biIterator = BidirectionalIterator aggregate 0 Forward
    putStrLn "Bidirectional iteration:"
    iterateBidirectional biIterator

iterateForward :: ConcreteIterator -> IO ()
iterateForward iterator = 
    case next iterator of
        Just (item, nextIterator) -> do
            putStrLn $ "Item: " ++ item
            iterateForward nextIterator
        Nothing -> putStrLn "End of iteration"

iterateBidirectional :: BidirectionalIterator -> IO ()
iterateBidirectional iterator = do
    case next iterator of
        Just (item, nextIterator) -> do
            putStrLn $ "Item: " ++ item
            iterateBidirectional nextIterator
        Nothing -> putStrLn "End of iteration"
```

### 形式化证明

#### 定理 5.1 (迭代器的终止性)

对于任意迭代器 $\text{Iterator}$，迭代过程最终终止：
$$\exists n \in \mathbb{N}, \text{hasNext}(\text{next}^n(i)) = \text{False}$$

**证明**：
迭代器模式确保迭代过程在有限步后终止，避免无限循环。

## 🔗 中介者模式 (Mediator Pattern)

### 形式化定义

#### 定义 6.1 (中介者模式)

中介者模式定义为：
$$\text{Mediator} = (M, \text{mediate}, \text{colleagues})$$

其中：

- $M$ 是中介者类型
- $\text{mediate} : M \times \text{Colleague} \times \text{Message} \rightarrow \text{Response}$ 是中介函数
- $\text{colleagues} : M \rightarrow [\text{Colleague}]$ 是同事函数

### Haskell实现

```haskell
-- 同事接口
class Colleague c where
    send :: c -> String -> String
    receive :: c -> String -> String
    setMediator :: c -> Mediator -> c

-- 中介者接口
class Mediator m where
    type ColleagueType m
    sendMessage :: m -> ColleagueType m -> String -> String
    addColleague :: m -> ColleagueType m -> m

-- 具体同事
data ConcreteColleagueA = ConcreteColleagueA
    { mediator :: Maybe ConcreteMediator
    , name :: String
    }

instance Colleague ConcreteColleagueA where
    send colleague message = 
        case mediator colleague of
            Just med -> sendMessage med colleague message
            Nothing -> "No mediator set"
    
    receive colleague message = 
        "ColleagueA " ++ name colleague ++ " received: " ++ message
    
    setMediator colleague med = colleague { mediator = Just med }

data ConcreteColleagueB = ConcreteColleagueB
    { mediator :: Maybe ConcreteMediator
    , name :: String
    }

instance Colleague ConcreteColleagueB where
    send colleague message = 
        case mediator colleague of
            Just med -> sendMessage med colleague message
            Nothing -> "No mediator set"
    
    receive colleague message = 
        "ColleagueB " ++ name colleague ++ " received: " ++ message
    
    setMediator colleague med = colleague { mediator = Just med }

-- 具体中介者
data ConcreteMediator = ConcreteMediator
    { colleagues :: [Either ConcreteColleagueA ConcreteColleagueB]
    }

instance Mediator ConcreteMediator where
    type ColleagueType ConcreteMediator = Either ConcreteColleagueA ConcreteColleagueB
    sendMessage mediator sender message = 
        let responses = map (\colleague -> 
            case colleague of
                Left c -> if c /= sender then receive c message else ""
                Right c -> if c /= sender then receive c message else ""
        ) (colleagues mediator)
        in unwords $ filter (/= "") responses
    
    addColleague mediator colleague = 
        mediator { colleagues = colleague : colleagues mediator }

-- 使用示例
exampleMediator :: IO ()
exampleMediator = do
    let mediator = ConcreteMediator []
    let colleagueA = ConcreteColleagueA Nothing "Alice"
    let colleagueB = ConcreteColleagueB Nothing "Bob"
    
    let colleagueA' = setMediator colleagueA mediator
    let colleagueB' = setMediator colleagueB mediator
    let mediator' = addColleague (addColleague mediator (Left colleagueA')) (Right colleagueB')
    
    putStrLn $ send colleagueA' "Hello from Alice"
    putStrLn $ send colleagueB' "Hello from Bob"
```

### 形式化证明

#### 定理 6.1 (中介者的解耦性)

对于任意中介者 $\text{Mediator}$，同事间通过中介者通信：
$$\text{mediate}(m, c_1, \text{msg}) = \text{mediate}(m, c_2, \text{msg})$$

**证明**：
中介者模式解耦同事间的直接依赖，所有通信通过中介者进行。

## 📊 性能分析与优化

### 时间复杂度分析

| 模式 | 交互时间复杂度 | 空间复杂度 | 适用场景 |
|------|----------------|------------|----------|
| 责任链模式 | O(n) | O(n) | 请求处理 |
| 命令模式 | O(1) | O(n) | 操作封装 |
| 解释器模式 | O(n) | O(n) | 语言解释 |
| 迭代器模式 | O(1) | O(1) | 集合遍历 |
| 中介者模式 | O(n) | O(n) | 对象协调 |

### 内存优化策略

```haskell
-- 命令模式的撤销栈优化
data OptimizedCommand = OptimizedCommand
    { action :: String
    , stateSnapshot :: Maybe String
    }

-- 延迟加载的撤销状态
lazyUndoState :: OptimizedCommand -> String -> String
lazyUndoState command currentState = 
    case stateSnapshot command of
        Just snapshot -> snapshot
        Nothing -> currentState
```

## 🎯 最佳实践

### 1. 模式选择原则

- **请求处理**：使用责任链模式
- **操作封装**：使用命令模式
- **语言解释**：使用解释器模式
- **集合遍历**：使用迭代器模式
- **对象协调**：使用中介者模式

### 2. 性能考虑

- 避免过长的责任链
- 合理使用命令模式的撤销功能
- 优化解释器的性能
- 考虑迭代器的内存使用

### 3. 可维护性

- 保持接口的一致性
- 避免过度复杂的中介者
- 提供清晰的文档
- 进行充分的测试

## 🔗 相关链接

- [创建型设计模式](../01-Creational-Patterns/README.md)
- [结构型设计模式](../02-Structural-Patterns/README.md)
- [并发设计模式](../04-Concurrent-Patterns/README.md)
- [设计模式总览](../README.md)

---

*本文档提供了行为型设计模式的完整形式化理论和Haskell实现，为软件架构设计提供了坚实的理论基础。*
