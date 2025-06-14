# 不变性分析 (Invariant Analysis)

## 概述

不变性分析是Petri网分析的重要技术，通过计算P-不变性和T-不变性来验证系统的结构性质和行为特性。

## 形式化定义

### 基本概念

```haskell
-- P-不变性
data PInvariant = PInvariant
  { places :: Vector Integer
  , constant :: Integer
  , description :: String
  }

-- T-不变性
data TInvariant = TInvariant
  { transitions :: Vector Integer
  , cycle :: Bool
  , description :: String
  }

-- 不变性分析结果
data InvariantAnalysisResult = InvariantAnalysisResult
  { pInvariants :: Set PInvariant
  , tInvariants :: Set TInvariant
  , minimalPInvariants :: Set PInvariant
  , minimalTInvariants :: Set TInvariant
  }
```

### 数学定义

对于Petri网 $PN = (P, T, W, M_0)$：

**P-不变性**：向量 $x \in \mathbb{Z}^{|P|}$ 是P-不变性，当且仅当：

- $x^T \cdot C = 0$，其中 $C$ 是关联矩阵
- $x^T \cdot M = x^T \cdot M_0$ 对所有可达标记 $M$ 成立

**T-不变性**：向量 $y \in \mathbb{Z}^{|T|}$ 是T-不变性，当且仅当：

- $C \cdot y = 0$，其中 $C$ 是关联矩阵
- $y$ 表示一个变迁序列，使得系统回到初始状态

### 不变性计算

```haskell
-- 不变性计算
calculateInvariants :: PetriNet -> InvariantAnalysisResult
calculateInvariants pn = 
  let incidenceMatrix = buildIncidenceMatrix pn
      pInvariants = calculatePInvariants incidenceMatrix
      tInvariants = calculateTInvariants incidenceMatrix
      minimalPInvariants = findMinimalPInvariants pInvariants
      minimalTInvariants = findMinimalTInvariants tInvariants
  in InvariantAnalysisResult pInvariants tInvariants minimalPInvariants minimalTInvariants

-- 关联矩阵
buildIncidenceMatrix :: PetriNet -> Matrix Integer
buildIncidenceMatrix pn = 
  let places = Set.toList (places pn)
      transitions = Set.toList (transitions pn)
      matrix = replicate (length places) (replicate (length transitions) 0)
  in foldl (\m (i, p) -> 
       foldl (\m' (j, t) -> 
         let weight = getArcWeight pn p t
         in updateMatrix m' i j weight
       ) m' (zip [0..] transitions)
     ) matrix (zip [0..] places)
```

## P-不变性分析

### P-不变性计算

```haskell
-- P-不变性计算
calculatePInvariants :: Matrix Integer -> Set PInvariant
calculatePInvariants matrix = 
  let nullSpace = calculateNullSpace matrix
      pInvariants = map vectorToPInvariant nullSpace
  in Set.fromList pInvariants

-- 零空间计算
calculateNullSpace :: Matrix Integer -> [Vector Integer]
calculateNullSpace matrix = 
  let reducedMatrix = gaussianElimination matrix
      freeVariables = findFreeVariables reducedMatrix
      nullSpaceVectors = generateNullSpaceVectors reducedMatrix freeVariables
  in nullSpaceVectors

-- 向量转P-不变性
vectorToPInvariant :: Vector Integer -> PInvariant
vectorToPInvariant vector = 
  let places = vector
      constant = calculateConstant vector
      description = generateDescription vector
  in PInvariant places constant description
```

### P-不变性验证

```haskell
-- P-不变性验证
verifyPInvariant :: PetriNet -> PInvariant -> Bool
verifyPInvariant pn invariant = 
  let reachableStates = getReachableStates pn
      initialValue = calculateInvariantValue invariant (initialMarking pn)
  in all (\state -> 
    let currentValue = calculateInvariantValue invariant state
    in currentValue == initialValue
  ) reachableStates

-- 不变性值计算
calculateInvariantValue :: PInvariant -> Marking -> Integer
calculateInvariantValue invariant marking = 
  let placeValues = map (\p -> getMarkingValue marking p) (places invariant)
  in sum (zipWith (*) (Vector.toList (places invariant)) placeValues)
```

## T-不变性分析

### T-不变性计算

```haskell
-- T-不变性计算
calculateTInvariants :: Matrix Integer -> Set TInvariant
calculateTInvariants matrix = 
  let transposedMatrix = transpose matrix
      nullSpace = calculateNullSpace transposedMatrix
      tInvariants = map vectorToTInvariant nullSpace
  in Set.fromList tInvariants

-- 向量转T-不变性
vectorToTInvariant :: Vector Integer -> TInvariant
vectorToTInvariant vector = 
  let transitions = vector
      cycle = isCycle vector
      description = generateDescription vector
  in TInvariant transitions cycle description

-- 循环检测
isCycle :: Vector Integer -> Bool
isCycle vector = 
  let transitionCounts = Vector.toList vector
      totalFirings = sum transitionCounts
  in totalFirings > 0 && all (>= 0) transitionCounts
```

### T-不变性验证

```haskell
-- T-不变性验证
verifyTInvariant :: PetriNet -> TInvariant -> Bool
verifyTInvariant pn invariant = 
  let initialMarking = initialMarking pn
      finalMarking = simulateTInvariant pn invariant initialMarking
  in finalMarking == initialMarking

-- T-不变性模拟
simulateTInvariant :: PetriNet -> TInvariant -> Marking -> Marking
simulateTInvariant pn invariant marking = 
  let transitionSequence = generateTransitionSequence invariant
  in foldl (\m t -> fireTransition pn t m) marking transitionSequence

-- 变迁序列生成
generateTransitionSequence :: TInvariant -> [Transition]
generateTransitionSequence invariant = 
  let transitionCounts = Vector.toList (transitions invariant)
      transitions = getTransitions invariant
  in concatMap (\(t, count) -> replicate count t) (zip transitions transitionCounts)
```

## 最小不变性

### 最小P-不变性

```haskell
-- 最小P-不变性
findMinimalPInvariants :: Set PInvariant -> Set PInvariant
findMinimalPInvariants invariants = 
  let allInvariants = Set.toList invariants
      minimalInvariants = filter (\inv -> isMinimalPInvariant inv allInvariants) allInvariants
  in Set.fromList minimalInvariants

-- 最小性检查
isMinimalPInvariant :: PInvariant -> [PInvariant] -> Bool
isMinimalPInvariant invariant allInvariants = 
  let otherInvariants = filter (/= invariant) allInvariants
  in not (any (\other -> isSubInvariant other invariant) otherInvariants)

-- 子不变性检查
isSubInvariant :: PInvariant -> PInvariant -> Bool
isSubInvariant subInvariant superInvariant = 
  let subVector = places subInvariant
      superVector = places superInvariant
      ratio = findRatio subVector superVector
  in isPositiveIntegerRatio ratio
```

### 最小T-不变性

```haskell
-- 最小T-不变性
findMinimalTInvariants :: Set TInvariant -> Set TInvariant
findMinimalTInvariants invariants = 
  let allInvariants = Set.toList invariants
      minimalInvariants = filter (\inv -> isMinimalTInvariant inv allInvariants) allInvariants
  in Set.fromList minimalInvariants

-- 最小性检查
isMinimalTInvariant :: TInvariant -> [TInvariant] -> Bool
isMinimalTInvariant invariant allInvariants = 
  let otherInvariants = filter (/= invariant) allInvariants
  in not (any (\other -> isSubTInvariant other invariant) otherInvariants)
```

## 应用分析

### 死锁检测

```haskell
-- 基于不变性的死锁检测
deadlockDetectionByInvariants :: PetriNet -> [DeadlockState]
deadlockDetectionByInvariants pn = 
  let invariantResult = calculateInvariants pn
      pInvariants = pInvariants invariantResult
      potentialDeadlocks = findPotentialDeadlocks pn pInvariants
  in filter (\state -> isDeadlockState pn state) potentialDeadlocks

-- 潜在死锁检测
findPotentialDeadlocks :: PetriNet -> Set PInvariant -> [Marking]
findPotentialDeadlocks pn invariants = 
  let boundaryMarkings = calculateBoundaryMarkings pn invariants
  in filter (\marking -> not (hasEnabledTransitions pn marking)) boundaryMarkings
```

### 活性分析

```haskell
-- 基于不变性的活性分析
livenessAnalysisByInvariants :: PetriNet -> [LivenessResult]
livenessAnalysisByInvariants pn = 
  let invariantResult = calculateInvariants pn
      tInvariants = tInvariants invariantResult
      transitions = Set.toList (transitions pn)
  in map (\t -> analyzeTransitionLiveness pn t tInvariants) transitions

-- 变迁活性分析
analyzeTransitionLiveness :: PetriNet -> Transition -> Set TInvariant -> LivenessResult
analyzeTransitionLiveness pn transition invariants = 
  let relevantInvariants = filter (\inv -> involvesTransition inv transition) invariants
      livenessLevel = calculateLivenessLevel relevantInvariants
  in LivenessResult transition livenessLevel relevantInvariants
```

## 性能优化

### 符号计算

```haskell
-- 符号不变性计算
symbolicInvariantCalculation :: PetriNet -> SymbolicInvariantResult
symbolicInvariantCalculation pn = 
  let symbolicMatrix = buildSymbolicIncidenceMatrix pn
      symbolicPInvariants = calculateSymbolicPInvariants symbolicMatrix
      symbolicTInvariants = calculateSymbolicTInvariants symbolicMatrix
  in SymbolicInvariantResult symbolicPInvariants symbolicTInvariants

-- 符号关联矩阵
buildSymbolicIncidenceMatrix :: PetriNet -> SymbolicMatrix
buildSymbolicIncidenceMatrix pn = 
  let places = Set.toList (places pn)
      transitions = Set.toList (transitions pn)
      symbolicEntries = map (\p -> map (\t -> getSymbolicWeight pn p t) transitions) places
  in SymbolicMatrix symbolicEntries
```

### 并行计算

```haskell
-- 并行不变性计算
parallelInvariantCalculation :: PetriNet -> Int -> InvariantAnalysisResult
parallelInvariantCalculation pn numThreads = 
  let incidenceMatrix = buildIncidenceMatrix pn
      pInvariants = parallelPInvariantCalculation incidenceMatrix numThreads
      tInvariants = parallelTInvariantCalculation incidenceMatrix numThreads
  in InvariantAnalysisResult pInvariants tInvariants Set.empty Set.empty
```

## 工具支持

### 分析工具

```haskell
-- 不变性分析工具
class InvariantAnalysisTools where
  calculateInvariants :: PetriNet -> IO InvariantAnalysisResult
  visualizeInvariants :: InvariantAnalysisResult -> IO ()
  exportInvariants :: InvariantAnalysisResult -> FilePath -> IO ()
  compareInvariants :: InvariantAnalysisResult -> InvariantAnalysisResult -> ComparisonResult

-- 不变性比较
data InvariantComparison = InvariantComparison
  { pInvariantDifference :: Int
  , tInvariantDifference :: Int
  , commonPInvariants :: Set PInvariant
  , commonTInvariants :: Set TInvariant
  }
```

## 相关理论

- [可达性分析](./01-可达性分析.md)
- [死锁分析](./03-死锁分析.md)
- [活性分析](./04-活性分析.md)

## 导航

- [返回Petri网分析主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md)
