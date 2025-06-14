# 可达性分析 (Reachability Analysis)

## 概述

可达性分析是Petri网分析的基础，通过构建可达性图来完整地描述系统的行为空间，是验证系统性质的核心技术。

## 形式化定义

### 基本概念

```haskell
-- 可达性图
type ReachabilityGraph = Graph Marking Transition

-- 可达性关系
type ReachabilityRelation = Set (Marking, Transition, Marking)

-- 可达性分析结果
data ReachabilityResult = ReachabilityResult
  { reachableStates :: Set Marking
  , reachabilityRelation :: ReachabilityRelation
  , stateCount :: Int
  , isFinite :: Bool
  }
```

### 数学定义

对于Petri网 $PN = (P, T, W, M_0)$，可达性关系定义为：

- $M_0 \in R(PN)$ （初始标记可达）
- 如果 $M \in R(PN)$ 且 $M[t\rangle M'$，则 $M' \in R(PN)$
- 可达集 $R(PN)$ 是满足上述条件的最小集合

### 可达性算法

```haskell
-- 基本可达性分析
reachabilityAnalysis :: PetriNet -> ReachabilityResult
reachabilityAnalysis pn = 
  let initial = initialMarking pn
      states = exploreStates pn [initial] Set.empty
      relation = buildReachabilityRelation pn states
      isFinite = Set.size states < maxStates
  in ReachabilityResult states relation (Set.size states) isFinite

-- 状态探索
exploreStates :: PetriNet -> [Marking] -> Set Marking -> Set Marking
exploreStates pn [] visited = visited
exploreStates pn (current:rest) visited =
  if Set.member current visited
  then exploreStates pn rest visited
  else 
    let enabledTransitions = getEnabledTransitions pn current
        newStates = map (\t -> fireTransition pn t current) enabledTransitions
        newVisited = Set.insert current visited
    in exploreStates pn (rest ++ newStates) newVisited
```

## 算法优化

### 符号可达性分析

```haskell
-- 符号状态
data SymbolicState = SymbolicState
  { marking :: Marking
  , constraints :: [Constraint]
  }

-- 符号可达性分析
symbolicReachabilityAnalysis :: PetriNet -> SymbolicReachabilityResult
symbolicReachabilityAnalysis pn = 
  let initial = SymbolicState (initialMarking pn) []
      symbolicStates = exploreSymbolicStates pn [initial] Set.empty
  in SymbolicReachabilityResult symbolicStates

-- 符号状态探索
exploreSymbolicStates :: PetriNet -> [SymbolicState] -> Set SymbolicState -> Set SymbolicState
exploreSymbolicStates pn [] visited = visited
exploreSymbolicStates pn (current:rest) visited =
  if Set.member current visited
  then exploreSymbolicStates pn rest visited
  else 
    let enabledTransitions = getSymbolicEnabledTransitions pn current
        newStates = map (\t -> fireSymbolicTransition pn t current) enabledTransitions
        newVisited = Set.insert current visited
    in exploreSymbolicStates pn (rest ++ newStates) newVisited
```

### 覆盖性分析

```haskell
-- 覆盖性分析
coverabilityAnalysis :: PetriNet -> CoverabilityResult
coverabilityAnalysis pn = 
  let initial = initialMarking pn
      coverabilityTree = buildCoverabilityTree pn initial
      coverabilitySet = extractCoverabilitySet coverabilityTree
  in CoverabilityResult coverabilityTree coverabilitySet

-- 覆盖性树
data CoverabilityTree = CoverabilityTree
  { node :: Marking
  , children :: [CoverabilityTree]
  , isTerminal :: Bool
  }

-- 构建覆盖性树
buildCoverabilityTree :: PetriNet -> Marking -> CoverabilityTree
buildCoverabilityTree pn marking = 
  let enabledTransitions = getEnabledTransitions pn marking
      children = map (\t -> 
        let newMarking = fireTransition pn t marking
            childTree = buildCoverabilityTree pn newMarking
        in childTree
      ) enabledTransitions
      isTerminal = null enabledTransitions
  in CoverabilityTree marking children isTerminal
```

## 应用技术

### 状态空间压缩

```haskell
-- 状态压缩
compressStateSpace :: ReachabilityGraph -> CompressedGraph
compressStateSpace graph = 
  let equivalenceClasses = findEquivalenceClasses graph
      compressedStates = map compressClass equivalenceClasses
      compressedEdges = compressEdges graph equivalenceClasses
  in CompressedGraph compressedStates compressedEdges

-- 等价类
data EquivalenceClass = EquivalenceClass
  { representative :: Marking
  , members :: Set Marking
  , properties :: Set Property
  }
```

### 并行可达性分析

```haskell
-- 并行可达性分析
parallelReachabilityAnalysis :: PetriNet -> Int -> ReachabilityResult
parallelReachabilityAnalysis pn numThreads = 
  let initialStates = partitionInitialStates pn numThreads
      workerResults = parMap numThreads (exploreStates pn) initialStates
      combinedStates = foldl Set.union Set.empty (map fst workerResults)
      combinedRelations = foldl Set.union Set.empty (map snd workerResults)
  in ReachabilityResult combinedStates combinedRelations (Set.size combinedStates) True
```

## 验证应用

### 安全性验证

```haskell
-- 安全性验证
safetyVerification :: PetriNet -> SafetyProperty -> Bool
safetyVerification pn property = 
  let reachabilityResult = reachabilityAnalysis pn
      reachableStates = reachableStates reachabilityResult
  in all (\state -> checkSafetyProperty property state) reachableStates

-- 安全性属性
data SafetyProperty = SafetyProperty
  { condition :: Marking -> Bool
  , description :: String
  }
```

### 活性验证

```haskell
-- 活性验证
livenessVerification :: PetriNet -> LivenessProperty -> Bool
livenessVerification pn property = 
  let reachabilityResult = reachabilityAnalysis pn
      reachabilityGraph = buildReachabilityGraph reachabilityResult
  in checkLivenessProperty property reachabilityGraph

-- 活性属性
data LivenessProperty = LivenessProperty
  { transition :: Transition
  , condition :: Marking -> Bool
  }
```

## 性能分析

### 复杂度分析

```haskell
-- 复杂度分析
complexityAnalysis :: PetriNet -> ComplexityMetrics
complexityAnalysis pn = 
  let stateCount = estimateStateCount pn
      transitionCount = Set.size (transitions pn)
      placeCount = Set.size (places pn)
      theoreticalComplexity = calculateTheoreticalComplexity pn
  in ComplexityMetrics stateCount transitionCount placeCount theoreticalComplexity

-- 复杂度指标
data ComplexityMetrics = ComplexityMetrics
  { stateCount :: Int
  , transitionCount :: Int
  , placeCount :: Int
  , theoreticalComplexity :: ComplexityClass
  }
```

### 内存优化

```haskell
-- 内存优化
memoryOptimizedReachability :: PetriNet -> MemoryLimit -> ReachabilityResult
memoryOptimizedReachability pn limit = 
  let initialState = initialMarking pn
      result = exploreWithMemoryLimit pn initialState limit
  in result

-- 内存限制探索
exploreWithMemoryLimit :: PetriNet -> Marking -> MemoryLimit -> ReachabilityResult
exploreWithMemoryLimit pn initial limit = 
  let states = exploreStatesWithLimit pn [initial] Set.empty limit
      relation = buildLimitedRelation pn states
  in ReachabilityResult states relation (Set.size states) False
```

## 工具支持

### 分析工具

```haskell
-- 可达性分析工具
class ReachabilityAnalysisTools where
  analyzeReachability :: PetriNet -> IO ReachabilityResult
  visualizeReachabilityGraph :: ReachabilityGraph -> IO ()
  exportReachabilityResult :: ReachabilityResult -> FilePath -> IO ()
  compareReachabilityResults :: ReachabilityResult -> ReachabilityResult -> ComparisonResult

-- 比较结果
data ComparisonResult = ComparisonResult
  { stateDifference :: Int
  , relationDifference :: Int
  , commonStates :: Set Marking
  , uniqueStates :: Set Marking
  }
```

## 相关理论

- [不变性分析](./02-不变性分析.md)
- [死锁分析](./03-死锁分析.md)
- [活性分析](./04-活性分析.md)

## 导航

- [返回Petri网分析主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md)
