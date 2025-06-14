# 随机Petri网 (Stochastic Petri Nets)

## 概述

随机Petri网是Petri网的重要扩展，通过引入随机延迟，使得Petri网能够进行性能分析和可靠性评估。

## 形式化定义

### 基本概念

```haskell
-- 随机延迟
data StochasticDelay = StochasticDelay
  { distribution :: ProbabilityDistribution
  , rate :: Double
  }

-- 概率分布
data ProbabilityDistribution = 
    Exponential Double
  | Uniform Double Double
  | Normal Double Double
  | Gamma Double Double
  | Weibull Double Double

-- 随机Petri网
data StochasticPetriNet = StochasticPetriNet
  { places :: Set Place
  , transitions :: Set Transition
  , stochasticDelays :: Map Transition StochasticDelay
  , initialMarking :: Marking
  , arcs :: Set Arc
  }

-- 随机标记
data StochasticMarking = StochasticMarking
  { marking :: Marking
  , transitionTimes :: Map Transition Time
  }
```

### 数学定义

随机Petri网是一个五元组 $SPN = (P, T, W, I, M_0)$，其中：

- $P$ 是库所的有限集
- $T$ 是变迁的有限集
- $W$ 是随机延迟函数，$W: T \rightarrow \mathcal{D}$
- $I$ 是初始标记，$I: P \rightarrow \mathbb{N}$
- $M_0$ 是初始随机标记

### 执行语义

```haskell
-- 随机变迁使能条件
isStochasticEnabled :: StochasticPetriNet -> Transition -> StochasticMarking -> Bool
isStochasticEnabled spn t stochasticMarking = 
  let basicEnabled = isEnabled spn t (marking stochasticMarking)
      timeEnabled = isTimeEnabled spn t stochasticMarking
  in basicEnabled && timeEnabled

-- 随机变迁执行
fireStochasticTransition :: StochasticPetriNet -> Transition -> StochasticMarking -> StochasticMarking
fireStochasticTransition spn t stochasticMarking = 
  let newMarking = fireTransition spn t (marking stochasticMarking)
      newTransitionTimes = updateTransitionTimes spn t (transitionTimes stochasticMarking)
  in StochasticMarking newMarking newTransitionTimes
```

## 概率语义

### 马尔可夫链

```haskell
-- 马尔可夫链状态
type MarkovState = Marking

-- 马尔可夫链
data MarkovChain = MarkovChain
  { states :: Set MarkovState
  , transitionMatrix :: Matrix Double
  , initialDistribution :: Vector Double
  }

-- 构建马尔可夫链
buildMarkovChain :: StochasticPetriNet -> MarkovChain
buildMarkovChain spn = 
  let reachableStates = getReachableStates spn
      transitionMatrix = buildTransitionMatrix spn reachableStates
      initialDistribution = getInitialDistribution spn reachableStates
  in MarkovChain reachableStates transitionMatrix initialDistribution

-- 转移矩阵
buildTransitionMatrix :: StochasticPetriNet -> Set Marking -> Matrix Double
buildTransitionMatrix spn states = 
  let stateList = Set.toList states
      n = length stateList
      matrix = replicate n (replicate n 0.0)
  in foldl (\m (i, state) -> 
       foldl (\m' (j, nextState) -> 
         let rate = getTransitionRate spn state nextState
         in updateMatrix m' i j rate
       ) m (zip [0..] stateList)
     ) matrix (zip [0..] stateList)
```

### 稳态分析

```haskell
-- 稳态概率
calculateSteadyState :: StochasticPetriNet -> Map Marking Double
calculateSteadyState spn = 
  let markovChain = buildMarkovChain spn
      steadyStateVector = solveSteadyState (transitionMatrix markovChain)
      states = Set.toList (states markovChain)
  in Map.fromList (zip states steadyStateVector)

-- 求解稳态方程
solveSteadyState :: Matrix Double -> Vector Double
solveSteadyState matrix = 
  let n = length matrix
      augmentedMatrix = addConstraintRow matrix
      solution = solveLinearSystem augmentedMatrix
  in normalize solution
```

## 性能分析

### 吞吐量分析

```haskell
-- 吞吐量计算
calculateThroughput :: StochasticPetriNet -> Transition -> Double
calculateThroughput spn transition = 
  let steadyState = calculateSteadyState spn
      transitionRate = getTransitionRate spn transition
  in sum [transitionRate * getStateProbability state steadyState 
         | state <- Map.keys steadyState]

-- 状态概率
getStateProbability :: Marking -> Map Marking Double -> Double
getStateProbability state steadyState = 
  Map.findWithDefault 0.0 state steadyState
```

### 响应时间分析

```haskell
-- 响应时间
calculateResponseTime :: StochasticPetriNet -> Transition -> Transition -> Double
calculateResponseTime spn start end = 
  let reachabilityGraph = buildReachabilityGraph spn
      paths = findPaths start end reachabilityGraph
      pathTimes = map calculatePathTime paths
  in weightedAverage pathTimes

-- 路径时间计算
calculatePathTime :: Path -> Double
calculatePathTime path = 
  let transitionRates = map getTransitionRate path
  in sum (map (1.0 /) transitionRates)
```

### 可靠性分析

```haskell
-- 可靠性指标
data ReliabilityMetrics = ReliabilityMetrics
  { availability :: Double
  , meanTimeToFailure :: Double
  , meanTimeToRepair :: Double
  , failureRate :: Double
  }

-- 可靠性分析
analyzeReliability :: StochasticPetriNet -> ReliabilityMetrics
analyzeReliability spn = 
  let steadyState = calculateSteadyState spn
      availability = calculateAvailability spn steadyState
      mttf = calculateMTTF spn
      mttr = calculateMTTR spn
      failureRate = 1.0 / mttf
  in ReliabilityMetrics availability mttf mttr failureRate
```

## 应用示例

### 排队系统建模

```haskell
-- M/M/1排队系统随机Petri网
mm1QueueSPN :: StochasticPetriNet
mm1QueueSPN = StochasticPetriNet
  { places = Set.fromList ["queue", "server", "completed"]
  , transitions = Set.fromList ["arrive", "serve"]
  , stochasticDelays = Map.fromList
    [ ("arrive", StochasticDelay (Exponential 2.0) 2.0)
    , ("serve", StochasticDelay (Exponential 3.0) 3.0)
    ]
  , initialMarking = Map.fromList
    [ ("queue", 0)
    , ("server", 1)
    , ("completed", 0)
    ]
  }
```

### 制造系统建模

```haskell
-- 制造系统随机Petri网
manufacturingSPN :: StochasticPetriNet
manufacturingSPN = StochasticPetriNet
  { places = Set.fromList ["raw_material", "machine1", "machine2", "finished"]
  , transitions = Set.fromList ["process1", "process2", "fail", "repair"]
  , stochasticDelays = Map.fromList
    [ ("process1", StochasticDelay (Exponential 1.0) 1.0)
    , ("process2", StochasticDelay (Exponential 1.5) 1.5)
    , ("fail", StochasticDelay (Exponential 0.1) 0.1)
    , ("repair", StochasticDelay (Exponential 0.05) 0.05)
    ]
  , initialMarking = Map.fromList
    [ ("raw_material", 10)
    , ("machine1", 1)
    , ("machine2", 1)
    , ("finished", 0)
    ]
  }
```

## 高级分析技术

### 敏感性分析

```haskell
-- 敏感性分析
sensitivityAnalysis :: StochasticPetriNet -> Transition -> Double -> SensitivityResult
sensitivityAnalysis spn transition delta = 
  let basePerformance = calculatePerformance spn
      perturbedSPN = perturbTransition spn transition delta
      perturbedPerformance = calculatePerformance perturbedSPN
      sensitivity = (perturbedPerformance - basePerformance) / delta
  in SensitivityResult basePerformance perturbedPerformance sensitivity

-- 敏感性结果
data SensitivityResult = SensitivityResult
  { baseValue :: Double
  , perturbedValue :: Double
  , sensitivity :: Double
  }
```

### 优化分析

```haskell
-- 性能优化
optimizePerformance :: StochasticPetriNet -> OptimizationGoal -> StochasticPetriNet
optimizePerformance spn goal = 
  let currentPerformance = evaluatePerformance spn
      optimizedRates = optimizeRates spn goal
  in spn { stochasticDelays = optimizedRates }

-- 优化目标
data OptimizationGoal = 
    MaximizeThroughput
  | MinimizeResponseTime
  | MaximizeReliability
  | MinimizeCost
```

## 工具支持

### 分析工具

```haskell
-- 随机Petri网分析工具
class StochasticPetriNetTools where
  loadStochasticModel :: FilePath -> IO StochasticPetriNet
  saveStochasticModel :: StochasticPetriNet -> FilePath -> IO ()
  simulateStochastic :: StochasticPetriNet -> Int -> IO [StochasticMarking]
  analyzeStochastic :: StochasticPetriNet -> StochasticAnalysisResult

-- 随机分析结果
data StochasticAnalysisResult = StochasticAnalysisResult
  { reachableStates :: Int
  , steadyState :: Map Marking Double
  , performance :: PerformanceMetrics
  , reliability :: ReliabilityMetrics
  }
```

## 相关理论

- [基础Petri网](../01-基础Petri网/01-Basic-Concepts.md)
- [有色Petri网](./01-有色Petri网.md)
- [时间Petri网](./02-时间Petri网.md)
- [层次Petri网](./04-层次Petri网.md)

## 导航

- [返回高级Petri网主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md) 