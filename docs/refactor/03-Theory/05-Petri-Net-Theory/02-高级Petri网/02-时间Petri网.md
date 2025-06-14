# 时间Petri网 (Timed Petri Nets)

## 概述

时间Petri网是Petri网的重要扩展，通过引入时间约束，使得Petri网能够建模和分析实时系统的时间行为。

## 形式化定义

### 基本概念

```haskell
-- 时间约束
data TimeConstraint = TimeConstraint
  { minDelay :: Time
  , maxDelay :: Time
  }

-- 时间Petri网
data TimedPetriNet = TimedPetriNet
  { places :: Set Place
  , transitions :: Set Transition
  , timeConstraints :: Map Transition TimeConstraint
  , initialMarking :: Marking
  , arcs :: Set Arc
  }

-- 时间标记
data TimedMarking = TimedMarking
  { marking :: Marking
  , clockValues :: Map Transition Time
  }

-- 时间
type Time = Double
```

### 数学定义

时间Petri网是一个五元组 $TPN = (P, T, W, I, M_0)$，其中：

- $P$ 是库所的有限集
- $T$ 是变迁的有限集
- $W$ 是时间约束函数，$W: T \rightarrow [\alpha, \beta]$
- $I$ 是初始标记，$I: P \rightarrow \mathbb{N}$
- $M_0$ 是初始时间标记

### 执行语义

```haskell
-- 时间变迁使能条件
isTimedEnabled :: TimedPetriNet -> Transition -> TimedMarking -> Bool
isTimedEnabled tpn t timedMarking = 
  let basicEnabled = isEnabled tpn t (marking timedMarking)
      timeEnabled = isTimeEnabled tpn t timedMarking
  in basicEnabled && timeEnabled

-- 时间使能检查
isTimeEnabled :: TimedPetriNet -> Transition -> TimedMarking -> Bool
isTimeEnabled tpn t timedMarking = 
  let constraint = getTimeConstraint tpn t
      clockValue = getClockValue timedMarking t
  in clockValue >= minDelay constraint && clockValue <= maxDelay constraint

-- 时间变迁执行
fireTimedTransition :: TimedPetriNet -> Transition -> TimedMarking -> TimedMarking
fireTimedTransition tpn t timedMarking = 
  let newMarking = fireTransition tpn t (marking timedMarking)
      newClockValues = resetClocks tpn t (clockValues timedMarking)
  in TimedMarking newMarking newClockValues
```

## 时间语义

### 时钟语义

```haskell
-- 时钟更新
updateClocks :: TimedPetriNet -> TimedMarking -> Time -> TimedMarking
updateClocks tpn timedMarking delta = 
  let newClockValues = Map.map (+ delta) (clockValues timedMarking)
  in TimedMarking (marking timedMarking) newClockValues

-- 时钟重置
resetClocks :: TimedPetriNet -> Transition -> Map Transition Time -> Map Transition Time
resetClocks tpn t clockValues = 
  let enabledTransitions = getEnabledTransitions tpn (marking timedMarking)
  in Map.mapWithKey (\t' v -> 
       if t' `elem` enabledTransitions then 0 else v
     ) clockValues
```

### 时间约束类型

```haskell
-- 时间约束类型
data TimeConstraintType = 
    Immediate      -- 立即执行
  | Delayed Time   -- 延迟执行
  | Interval Time Time  -- 时间区间
  | Urgent         -- 紧急执行

-- 约束检查
checkTimeConstraint :: TimeConstraint -> Time -> Bool
checkTimeConstraint constraint time = 
  case constraint of
    Immediate -> time == 0
    Delayed delay -> time >= delay
    Interval min max -> time >= min && time <= max
    Urgent -> True
```

## 分析技术

### 时间可达性分析

```haskell
-- 时间可达性图
type TimedReachabilityGraph = Graph TimedMarking (Transition, Time)

-- 构建时间可达性图
buildTimedReachabilityGraph :: TimedPetriNet -> TimedReachabilityGraph
buildTimedReachabilityGraph tpn = 
  let initial = TimedMarking (initialMarking tpn) Map.empty
      states = exploreTimedStates tpn [initial] Set.empty
      edges = buildTimedEdges tpn states
  in Graph states edges

-- 时间状态探索
exploreTimedStates :: TimedPetriNet -> [TimedMarking] -> Set TimedMarking -> Set TimedMarking
exploreTimedStates tpn [] visited = visited
exploreTimedStates tpn (current:rest) visited =
  if Set.member current visited
  then exploreTimedStates tpn rest visited
  else 
    let enabledTransitions = getTimedEnabledTransitions tpn current
        newStates = map (\t -> fireTimedTransition tpn t current) enabledTransitions
        newVisited = Set.insert current visited
    in exploreTimedStates tpn (rest ++ newStates) newVisited
```

### 时间不变性分析

```haskell
-- 时间不变性
data TimedInvariant = TimedInvariant
  { condition :: Marking -> Bool
  , timeBound :: Time
  }

-- 时间不变性检查
checkTimedInvariant :: TimedPetriNet -> TimedInvariant -> Bool
checkTimedInvariant tpn inv = 
  let reachableStates = getTimedReachableStates tpn
  in all (\state -> 
    let marking = marking state
        time = getMaxTime state
    in condition inv marking && time <= timeBound inv
  ) reachableStates
```

## 实时验证

### 时间属性验证

```haskell
-- 时间时态逻辑
data TimedTemporalFormula = 
    TimedAtomic String
  | TimedNot TimedTemporalFormula
  | TimedAnd TimedTemporalFormula TimedTemporalFormula
  | TimedAlways TimedTemporalFormula
  | TimedEventually TimedTemporalFormula
  | TimedUntil TimedTemporalFormula TimedTemporalFormula
  | TimedWithin Time TimedTemporalFormula

-- 时间模型检测
timedModelCheck :: TimedPetriNet -> TimedTemporalFormula -> Bool
timedModelCheck tpn formula = 
  let reachabilityGraph = buildTimedReachabilityGraph tpn
      initialStates = getInitialStates reachabilityGraph
  in all (\state -> checkTimedFormula formula state reachabilityGraph) initialStates
```

### 死锁时间分析

```haskell
-- 时间死锁检测
detectTimedDeadlocks :: TimedPetriNet -> [TimedMarking]
detectTimedDeadlocks tpn = 
  let reachableStates = getTimedReachableStates tpn
  in filter (\state -> not (hasTimedEnabledTransitions tpn state)) reachableStates

-- 检查时间死锁
isTimedDeadlock :: TimedPetriNet -> TimedMarking -> Bool
isTimedDeadlock tpn state = 
  let enabledTransitions = getTimedEnabledTransitions tpn state
  in null enabledTransitions
```

## 应用示例

### 实时控制系统

```haskell
-- 实时控制系统时间Petri网
realTimeControlTPN :: TimedPetriNet
realTimeControlTPN = TimedPetriNet
  { places = Set.fromList ["sensor", "controller", "actuator", "monitor"]
  , transitions = Set.fromList ["read", "compute", "act", "check"]
  , timeConstraints = Map.fromList
    [ ("read", TimeConstraint 0.1 0.5)
    , ("compute", TimeConstraint 0.2 1.0)
    , ("act", TimeConstraint 0.1 0.3)
    , ("check", TimeConstraint 0.5 2.0)
    ]
  , initialMarking = Map.fromList
    [ ("sensor", 1)
    , ("controller", 0)
    , ("actuator", 0)
    , ("monitor", 1)
    ]
  }
```

### 通信协议时间建模

```haskell
-- 通信协议时间Petri网
communicationTimedTPN :: TimedPetriNet
communicationTimedTPN = TimedPetriNet
  { places = Set.fromList ["sender", "channel", "receiver", "timeout"]
  , transitions = Set.fromList ["send", "transmit", "receive", "retransmit"]
  , timeConstraints = Map.fromList
    [ ("send", TimeConstraint 0.1 0.5)
    , ("transmit", TimeConstraint 1.0 5.0)
    , ("receive", TimeConstraint 0.1 0.3)
    , ("retransmit", TimeConstraint 10.0 30.0)
    ]
  , initialMarking = Map.fromList
    [ ("sender", 1)
    , ("channel", 0)
    , ("receiver", 0)
    , ("timeout", 0)
    ]
  }
```

## 性能分析

### 时间性能指标

```haskell
-- 响应时间分析
analyzeResponseTime :: TimedPetriNet -> Transition -> Transition -> Time
analyzeResponseTime tpn start end = 
  let reachabilityGraph = buildTimedReachabilityGraph tpn
      paths = findPaths start end reachabilityGraph
      pathTimes = map calculatePathTime paths
  in minimum pathTimes

-- 吞吐量分析
analyzeThroughput :: TimedPetriNet -> Transition -> Double
analyzeThroughput tpn transition = 
  let reachabilityGraph = buildTimedReachabilityGraph tpn
      steadyState = calculateTimedSteadyState reachabilityGraph
  in sum [getTransitionRate transition state * getStateProbability state steadyState 
         | state <- getStates reachabilityGraph]
```

### 时间约束优化

```haskell
-- 时间约束优化
optimizeTimeConstraints :: TimedPetriNet -> OptimizationGoal -> TimedPetriNet
optimizeTimeConstraints tpn goal = 
  let currentPerformance = evaluatePerformance tpn
      optimizedConstraints = optimizeConstraints tpn goal
  in tpn { timeConstraints = optimizedConstraints }

-- 优化目标
data OptimizationGoal = 
    MinimizeResponseTime
  | MaximizeThroughput
  | MinimizeResourceUsage
  | BalancePerformance
```

## 工具支持

### 分析工具

```haskell
-- 时间Petri网分析工具
class TimedPetriNetTools where
  loadTimedModel :: FilePath -> IO TimedPetriNet
  saveTimedModel :: TimedPetriNet -> FilePath -> IO ()
  simulateTimed :: TimedPetriNet -> Int -> IO [TimedMarking]
  analyzeTimed :: TimedPetriNet -> TimedAnalysisResult

-- 时间分析结果
data TimedAnalysisResult = TimedAnalysisResult
  { reachableStates :: Int
  , timedDeadlocks :: [TimedMarking]
  , timeInvariants :: [TimedInvariant]
  , performance :: TimedPerformanceMetrics
  }
```

## 相关理论

- [基础Petri网](../01-基础Petri网/01-Basic-Concepts.md)
- [有色Petri网](./01-有色Petri网.md)
- [随机Petri网](./03-随机Petri网.md)
- [层次Petri网](./04-层次Petri网.md)

## 导航

- [返回高级Petri网主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md) 