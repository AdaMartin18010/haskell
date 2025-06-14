# 有色Petri网 (Colored Petri Nets)

## 概述

有色Petri网是Petri网的重要扩展，通过引入颜色集和颜色函数，使得Petri网能够建模更复杂的系统，同时保持模型的简洁性。

## 形式化定义

### 基本概念

```haskell
-- 颜色集
type ColorSet = Set Color
type Color = String

-- 颜色函数
type ColorFunction = Marking -> Marking

-- 有色Petri网
data ColoredPetriNet = ColoredPetriNet
  { places :: Set Place
  , transitions :: Set Transition
  , colorSets :: Map Place ColorSet
  , colorFunctions :: Map Transition ColorFunction
  , initialMarking :: Marking
  , arcs :: Set Arc
  }

-- 弧
data Arc = Arc
  { source :: Either Place Transition
  , target :: Either Place Transition
  , colorExpression :: ColorExpression
  }

-- 颜色表达式
data ColorExpression = ColorExpression
  { variables :: Set Variable
  , expression :: Expression
  }
```

### 数学定义

有色Petri网是一个六元组 $CPN = (P, T, C, W, I, M_0)$，其中：

- $P$ 是库所的有限集
- $T$ 是变迁的有限集
- $C$ 是颜色集函数，$C: P \cup T \rightarrow \Sigma$
- $W$ 是弧权函数，$W: (P \times T) \cup (T \times P) \rightarrow \text{Expr}$
- $I$ 是初始标记，$I: P \rightarrow \text{Expr}$
- $M_0$ 是初始标记函数

### 执行语义

```haskell
-- 标记
type Marking = Map Place (Map Color Integer)

-- 变迁使能条件
isEnabled :: ColoredPetriNet -> Transition -> Marking -> Bool
isEnabled cpn t marking = all (\p -> 
  let required = getRequiredTokens cpn p t
      available = getAvailableTokens marking p
  in all (\c -> Map.lookup c available >= Map.lookup c required) 
         (Map.keys required)
  ) (preSet cpn t)

-- 变迁执行
fireTransition :: ColoredPetriNet -> Transition -> Marking -> Marking
fireTransition cpn t marking = 
  let newMarking = removeTokens cpn t marking
      finalMarking = addTokens cpn t newMarking
  in finalMarking
```

## 类型系统

### 颜色类型

```haskell
-- 基本颜色类型
data BasicColor = 
    IntColor
  | StringColor
  | BoolColor
  | ProductColor [BasicColor]
  | SumColor [BasicColor]

-- 类型检查
typeCheck :: ColoredPetriNet -> Bool
typeCheck cpn = 
  let placeTypes = Map.elems (colorSets cpn)
      transitionTypes = Map.elems (colorFunctions cpn)
  in all isValidType (placeTypes ++ transitionTypes)
```

### 类型安全

```haskell
-- 类型安全检查
isTypeSafe :: ColoredPetriNet -> Bool
isTypeSafe cpn = 
  let arcs = getArcs cpn
      arcTypes = map getArcType arcs
  in all isValidArcType arcTypes

-- 弧类型检查
isValidArcType :: ArcType -> Bool
isValidArcType arcType = 
  case arcType of
    PlaceToTransition p t -> 
      getPlaceType p == getTransitionInputType t
    TransitionToPlace t p -> 
      getTransitionOutputType t == getPlaceType p
```

## 应用示例

### 生产者-消费者系统

```haskell
-- 生产者-消费者有色Petri网
producerConsumerCPN :: ColoredPetriNet
producerConsumerCPN = ColoredPetriNet
  { places = Set.fromList ["buffer", "producer", "consumer"]
  , transitions = Set.fromList ["produce", "consume"]
  , colorSets = Map.fromList 
    [ ("buffer", Set.fromList ["Item"])
    , ("producer", Set.fromList ["Producer"])
    , ("consumer", Set.fromList ["Consumer"])
    ]
  , colorFunctions = Map.fromList
    [ ("produce", \m -> addToken m "buffer" "Item" 1)
    , ("consume", \m -> removeToken m "buffer" "Item" 1)
    ]
  , initialMarking = Map.fromList
    [ ("buffer", Map.fromList [("Item", 0)])
    , ("producer", Map.fromList [("Producer", 1)])
    , ("consumer", Map.fromList [("Consumer", 1)])
    ]
  }
```

### 通信协议建模

```haskell
-- 通信协议有色Petri网
communicationProtocolCPN :: ColoredPetriNet
communicationProtocolCPN = ColoredPetriNet
  { places = Set.fromList ["sender", "channel", "receiver", "ack"]
  , transitions = Set.fromList ["send", "receive", "acknowledge"]
  , colorSets = Map.fromList
    [ ("sender", Set.fromList ["Message"])
    , ("channel", Set.fromList ["Message"])
    , ("receiver", Set.fromList ["Message"])
    , ("ack", Set.fromList ["Acknowledgment"])
    ]
  , colorFunctions = Map.fromList
    [ ("send", \m -> transferToken m "sender" "channel" "Message")
    , ("receive", \m -> transferToken m "channel" "receiver" "Message")
    , ("acknowledge", \m -> addToken m "ack" "Acknowledgment" 1)
    ]
  , initialMarking = Map.fromList
    [ ("sender", Map.fromList [("Message", 1)])
    , ("channel", Map.fromList [("Message", 0)])
    , ("receiver", Map.fromList [("Message", 0)])
    , ("ack", Map.fromList [("Acknowledgment", 0)])
    ]
  }
```

## 分析技术

### 可达性分析

```haskell
-- 可达性图
type ReachabilityGraph = Graph Marking Transition

-- 构建可达性图
buildReachabilityGraph :: ColoredPetriNet -> ReachabilityGraph
buildReachabilityGraph cpn = 
  let initial = initialMarking cpn
      states = exploreStates cpn [initial] Set.empty
      edges = buildEdges cpn states
  in Graph states edges

-- 状态探索
exploreStates :: ColoredPetriNet -> [Marking] -> Set Marking -> Set Marking
exploreStates cpn [] visited = visited
exploreStates cpn (current:rest) visited =
  if Set.member current visited
  then exploreStates cpn rest visited
  else 
    let enabledTransitions = getEnabledTransitions cpn current
        newStates = map (\t -> fireTransition cpn t current) enabledTransitions
        newVisited = Set.insert current visited
    in exploreStates cpn (rest ++ newStates) newVisited
```

### 不变性分析

```haskell
-- 不变性检查
checkInvariants :: ColoredPetriNet -> [Invariant] -> Bool
checkInvariants cpn invariants = 
  let reachableStates = getReachableStates cpn
  in all (\inv -> checkInvariant inv reachableStates) invariants

-- 标记不变性
checkMarkingInvariant :: MarkingInvariant -> Set Marking -> Bool
checkMarkingInvariant inv states = 
  all (\state -> evaluateInvariant inv state) states
```

## 形式化验证

### 模型检测

```haskell
-- 时态逻辑公式
data TemporalFormula = 
    Atomic String
  | Not TemporalFormula
  | And TemporalFormula TemporalFormula
  | Or TemporalFormula TemporalFormula
  | Implies TemporalFormula TemporalFormula
  | Always TemporalFormula
  | Eventually TemporalFormula
  | Next TemporalFormula
  | Until TemporalFormula TemporalFormula

-- 模型检测
modelCheck :: ColoredPetriNet -> TemporalFormula -> Bool
modelCheck cpn formula = 
  let reachabilityGraph = buildReachabilityGraph cpn
      initialStates = getInitialStates reachabilityGraph
  in all (\state -> checkFormula formula state reachabilityGraph) initialStates
```

### 死锁检测

```haskell
-- 死锁检测
detectDeadlocks :: ColoredPetriNet -> [Marking]
detectDeadlocks cpn = 
  let reachableStates = getReachableStates cpn
  in filter (\state -> not (hasEnabledTransitions cpn state)) reachableStates

-- 检查是否有使能变迁
hasEnabledTransitions :: ColoredPetriNet -> Marking -> Bool
hasEnabledTransitions cpn marking = 
  not (null (getEnabledTransitions cpn marking))
```

## 性能分析

### 吞吐量分析

```haskell
-- 吞吐量计算
calculateThroughput :: ColoredPetriNet -> Transition -> Double
calculateThroughput cpn transition = 
  let reachabilityGraph = buildReachabilityGraph cpn
      steadyState = calculateSteadyState reachabilityGraph
  in sum [getTransitionRate transition state * getStateProbability state steadyState 
         | state <- getStates reachabilityGraph]

-- 稳态概率
calculateSteadyState :: ReachabilityGraph -> Map Marking Double
calculateSteadyState graph = 
  let transitionMatrix = buildTransitionMatrix graph
      eigenvalues = getEigenvalues transitionMatrix
      steadyStateVector = getSteadyStateVector eigenvalues
  in Map.fromList (zip (getStates graph) steadyStateVector)
```

## 工具支持

### 分析工具

```haskell
-- CPN Tools接口
class CPNToolsInterface where
  loadModel :: FilePath -> IO ColoredPetriNet
  saveModel :: ColoredPetriNet -> FilePath -> IO ()
  simulate :: ColoredPetriNet -> Int -> IO [Marking]
  analyze :: ColoredPetriNet -> AnalysisResult

-- 分析结果
data AnalysisResult = AnalysisResult
  { reachableStates :: Int
  , deadlocks :: [Marking]
  , invariants :: [Invariant]
  , performance :: PerformanceMetrics
  }
```

## 相关理论

- [基础Petri网](../01-基础Petri网/01-Basic-Concepts.md)
- [时间Petri网](./02-时间Petri网.md)
- [随机Petri网](./03-随机Petri网.md)
- [层次Petri网](./04-层次Petri网.md)

## 导航

- [返回高级Petri网主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md)
