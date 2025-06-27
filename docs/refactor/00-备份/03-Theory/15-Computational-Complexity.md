# 计算复杂性理论

## 概述

计算复杂性理论研究算法和问题的计算资源需求，包括时间复杂度和空间复杂度。它为理解问题的固有难度和算法的效率提供了理论基础。

## 基本概念

### 计算模型

计算复杂性理论基于抽象的计算模型，如图灵机。

```haskell
-- 计算模型
data ComputationalModel = 
    DeterministicTuringMachine
  | NondeterministicTuringMachine
  | RandomAccessMachine
  | QuantumComputer
  deriving (Show, Eq)

-- 图灵机
data TuringMachine = TuringMachine {
    states :: [State],
    alphabet :: [Symbol],
    transitionFunction :: TransitionFunction,
    startState :: State,
    acceptStates :: [State],
    rejectStates :: [State]
} deriving (Show, Eq)

-- 状态
data State = State {
    stateId :: String,
    stateType :: StateType
} deriving (Show, Eq)

data StateType = 
    StartState
  | AcceptState
  | RejectState
  | NormalState
  deriving (Show, Eq)

-- 转移函数
type TransitionFunction = State -> Symbol -> (State, Symbol, Direction)

-- 方向
data Direction = 
    Left
  | Right
  | Stay
  deriving (Show, Eq)

-- 图灵机配置
data TMConfiguration = TMConfiguration {
    currentState :: State,
    tape :: Tape,
    headPosition :: Int
} deriving (Show, Eq)

-- 磁带
data Tape = Tape {
    leftTape :: [Symbol],
    currentSymbol :: Symbol,
    rightTape :: [Symbol]
} deriving (Show, Eq)
```

### 复杂度度量

```haskell
-- 复杂度度量
data ComplexityMeasure = 
    TimeComplexity
  | SpaceComplexity
  | CommunicationComplexity
  | QueryComplexity
  deriving (Show, Eq)

-- 时间复杂度
data TimeComplexity = TimeComplexity {
    worstCase :: ComplexityFunction,
    averageCase :: ComplexityFunction,
    bestCase :: ComplexityFunction
} deriving (Show, Eq)

-- 空间复杂度
data SpaceComplexity = SpaceComplexity {
    worstCase :: ComplexityFunction,
    averageCase :: ComplexityFunction,
    bestCase :: ComplexityFunction
} deriving (Show, Eq)

-- 复杂度函数
type ComplexityFunction = Int -> Int

-- 大O记号
data BigONotation = BigONotation {
    function :: ComplexityFunction,
    bound :: ComplexityFunction,
    constant :: Double
} deriving (Show, Eq)

-- 复杂度类
data ComplexityClass = ComplexityClass {
    className :: String,
    model :: ComputationalModel,
    resource :: ComplexityMeasure,
    bound :: ComplexityFunction
} deriving (Show, Eq)
```

## 复杂度类

### 1. 基本复杂度类

```haskell
-- P类（多项式时间）
pClass :: ComplexityClass
pClass = ComplexityClass {
    className = "P",
    model = DeterministicTuringMachine,
    resource = TimeComplexity,
    bound = \n -> n^k  -- 对于某个常数k
}

-- NP类（非确定性多项式时间）
npClass :: ComplexityClass
npClass = ComplexityClass {
    className = "NP",
    model = NondeterministicTuringMachine,
    resource = TimeComplexity,
    bound = \n -> n^k  -- 对于某个常数k
}

-- PSPACE类（多项式空间）
pspaceClass :: ComplexityClass
pspaceClass = ComplexityClass {
    className = "PSPACE",
    model = DeterministicTuringMachine,
    resource = SpaceComplexity,
    bound = \n -> n^k  -- 对于某个常数k
}

-- EXPTIME类（指数时间）
exptimeClass :: ComplexityClass
exptimeClass = ComplexityClass {
    className = "EXPTIME",
    model = DeterministicTuringMachine,
    resource = TimeComplexity,
    bound = \n -> 2^(n^k)  -- 对于某个常数k
}

-- 复杂度类关系
complexityHierarchy :: [ComplexityClass]
complexityHierarchy = [
    pClass,      -- P ⊆ NP ⊆ PSPACE ⊆ EXPTIME
    npClass,
    pspaceClass,
    exptimeClass
]
```

### 2. 高级复杂度类

```haskell
-- 多项式层次结构
data PolynomialHierarchy = PolynomialHierarchy {
    sigma0 :: ComplexityClass,  -- P
    sigma1 :: ComplexityClass,  -- NP
    sigma2 :: ComplexityClass,  -- Σ₂P
    pi1 :: ComplexityClass,     -- co-NP
    pi2 :: ComplexityClass,     -- Π₂P
    delta1 :: ComplexityClass,  -- P^NP
    delta2 :: ComplexityClass   -- P^Σ₂P
} deriving (Show, Eq)

-- 计数类
data CountingClass = CountingClass {
    fpClass :: ComplexityClass,    -- #P
    gapClass :: ComplexityClass,   -- GapP
    totpClass :: ComplexityClass   -- TotP
} deriving (Show, Eq)

-- 随机化类
data RandomizedClass = RandomizedClass {
    rpClass :: ComplexityClass,    -- RP
    coRPClass :: ComplexityClass,  -- co-RP
    bppClass :: ComplexityClass,   -- BPP
    ppClass :: ComplexityClass     -- PP
} deriving (Show, Eq)

-- 量子复杂度类
data QuantumClass = QuantumClass {
    bqpClass :: ComplexityClass,   -- BQP
    qmaClass :: ComplexityClass,   -- QMA
    qipClass :: ComplexityClass    -- QIP
} deriving (Show, Eq)
```

## 问题归约

### 1. 归约类型

```haskell
-- 归约
data Reduction = Reduction {
    reductionType :: ReductionType,
    sourceProblem :: Problem,
    targetProblem :: Problem,
    reductionFunction :: ReductionFunction
} deriving (Show, Eq)

data ReductionType = 
    ManyOneReduction
  | TuringReduction
  | TruthTableReduction
  | RandomReduction
  deriving (Show, Eq)

-- 问题
data Problem = Problem {
    problemName :: String,
    problemType :: ProblemType,
    complexityClass :: ComplexityClass,
    instances :: [Instance]
} deriving (Show, Eq)

data ProblemType = 
    DecisionProblem
  | SearchProblem
  | OptimizationProblem
  | CountingProblem
  deriving (Show, Eq)

-- 实例
data Instance = Instance {
    instanceId :: String,
    input :: Input,
    size :: Int
} deriving (Show, Eq)

-- 归约函数
type ReductionFunction = Instance -> Instance

-- 多项式时间归约
polynomialTimeReduction :: Problem -> Problem -> Bool
polynomialTimeReduction problemA problemB = 
    let reduction = findReduction problemA problemB
        isPolynomial = checkPolynomialTime (reductionFunction reduction)
    in isPolynomial
```

### 2. 完全性

```haskell
-- 完全性
data Completeness = Completeness {
    problem :: Problem,
    complexityClass :: ComplexityClass,
    completenessType :: CompletenessType,
    proof :: Proof
} deriving (Show, Eq)

data CompletenessType = 
    NPComplete
  | PSPACEComplete
  | EXPTIMEComplete
  | PComplete
  deriving (Show, Eq)

-- NP完全性
npCompleteness :: Problem -> Bool
npCompleteness problem = 
    let inNP = problemInClass problem npClass
        npHard = isNPHard problem
    in inNP && npHard

-- NP困难性
isNPHard :: Problem -> Bool
isNPHard problem = 
    let allNPProblems = getAllNPProblems
        allReducible = all (\p -> polynomialTimeReduction p problem) allNPProblems
    in allReducible

-- 经典NP完全问题
classicNPCompleteProblems :: [Problem]
classicNPCompleteProblems = [
    satProblem,           -- 布尔可满足性问题
    threeSatProblem,      -- 3-SAT问题
    cliqueProblem,        -- 团问题
    vertexCoverProblem,   -- 顶点覆盖问题
    hamiltonianPathProblem, -- 哈密顿路径问题
    travelingSalesmanProblem -- 旅行商问题
]

-- SAT问题
satProblem :: Problem
satProblem = Problem {
    problemName = "SAT",
    problemType = DecisionProblem,
    complexityClass = npClass,
    instances = []
}

-- 3-SAT问题
threeSatProblem :: Problem
threeSatProblem = Problem {
    problemName = "3-SAT",
    problemType = DecisionProblem,
    complexityClass = npClass,
    instances = []
}
```

## 算法分析

### 1. 时间复杂度分析

```haskell
-- 算法
data Algorithm = Algorithm {
    algorithmId :: String,
    algorithmType :: AlgorithmType,
    timeComplexity :: TimeComplexity,
    spaceComplexity :: SpaceComplexity
} deriving (Show, Eq)

data AlgorithmType = 
    SortingAlgorithm
  | SearchAlgorithm
  | GraphAlgorithm
  | DynamicProgramming
  | GreedyAlgorithm
  deriving (Show, Eq)

-- 排序算法复杂度
sortingAlgorithms :: [Algorithm]
sortingAlgorithms = [
    Algorithm "BubbleSort" SortingAlgorithm 
        (TimeComplexity (\n -> n^2) (\n -> n^2) (\n -> n)) 
        (SpaceComplexity (\n -> 1) (\n -> 1) (\n -> 1)),
    
    Algorithm "QuickSort" SortingAlgorithm 
        (TimeComplexity (\n -> n^2) (\n -> n * log n) (\n -> n * log n)) 
        (SpaceComplexity (\n -> n) (\n -> log n) (\n -> log n)),
    
    Algorithm "MergeSort" SortingAlgorithm 
        (TimeComplexity (\n -> n * log n) (\n -> n * log n) (\n -> n * log n)) 
        (SpaceComplexity (\n -> n) (\n -> n) (\n -> n)),
    
    Algorithm "HeapSort" SortingAlgorithm 
        (TimeComplexity (\n -> n * log n) (\n -> n * log n) (\n -> n * log n)) 
        (SpaceComplexity (\n -> 1) (\n -> 1) (\n -> 1))
]

-- 搜索算法复杂度
searchAlgorithms :: [Algorithm]
searchAlgorithms = [
    Algorithm "LinearSearch" SearchAlgorithm 
        (TimeComplexity (\n -> n) (\n -> n/2) (\n -> 1)) 
        (SpaceComplexity (\n -> 1) (\n -> 1) (\n -> 1)),
    
    Algorithm "BinarySearch" SearchAlgorithm 
        (TimeComplexity (\n -> log n) (\n -> log n) (\n -> 1)) 
        (SpaceComplexity (\n -> 1) (\n -> 1) (\n -> 1))
]
```

### 2. 空间复杂度分析

```haskell
-- 空间复杂度分析
class SpaceComplexityAnalysis a where
    worstCaseSpace :: a -> Int -> Int
    averageCaseSpace :: a -> Int -> Int
    bestCaseSpace :: a -> Int -> Int
    spaceEfficiency :: a -> Double

instance SpaceComplexityAnalysis Algorithm where
    worstCaseSpace algorithm n = 
        worstCase (spaceComplexity algorithm) n
    
    averageCaseSpace algorithm n = 
        averageCase (spaceComplexity algorithm) n
    
    bestCaseSpace algorithm n = 
        bestCase (spaceComplexity algorithm) n
    
    spaceEfficiency algorithm = 
        let worst = worstCaseSpace algorithm 1000
            best = bestCaseSpace algorithm 1000
        in fromIntegral best / fromIntegral worst
```

## 下界理论

### 1. 信息论下界

```haskell
-- 信息论下界
data InformationTheoreticLowerBound = InformationTheoreticLowerBound {
    problem :: Problem,
    lowerBound :: ComplexityFunction,
    proof :: Proof
} deriving (Show, Eq)

-- 比较排序下界
comparisonSortLowerBound :: InformationTheoreticLowerBound
comparisonSortLowerBound = InformationTheoreticLowerBound {
    problem = sortingProblem,
    lowerBound = \n -> ceiling (logBase 2 (fromIntegral (factorial n))),
    proof = comparisonSortProof
}

-- 搜索下界
searchLowerBound :: InformationTheoreticLowerBound
searchLowerBound = InformationTheoreticLowerBound {
    problem = searchProblem,
    lowerBound = \n -> ceiling (logBase 2 (fromIntegral n)),
    proof = searchProof
}

-- 阶乘函数
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)
```

### 2. 对抗性下界

```haskell
-- 对抗性下界
data AdversarialLowerBound = AdversarialLowerBound {
    problem :: Problem,
    adversary :: Adversary,
    lowerBound :: ComplexityFunction,
    proof :: Proof
} deriving (Show, Eq)

-- 对抗者
data Adversary = Adversary {
    adversaryType :: AdversaryType,
    strategy :: AdversaryStrategy,
    power :: AdversaryPower
} deriving (Show, Eq)

data AdversaryType = 
    DeterministicAdversary
  | RandomizedAdversary
  | AdaptiveAdversary
  deriving (Show, Eq)

-- 对抗性策略
type AdversaryStrategy = Algorithm -> Input -> Input

-- 对抗性下界证明
adversarialLowerBound :: Problem -> Adversary -> ComplexityFunction
adversarialLowerBound problem adversary = 
    let worstCaseInput = findWorstCaseInput adversary problem
        lowerBound = calculateLowerBound worstCaseInput
    in lowerBound
```

## 随机化算法

### 1. 随机化复杂度类

```haskell
-- 随机化算法
data RandomizedAlgorithm = RandomizedAlgorithm {
    algorithmId :: String,
    randomizationType :: RandomizationType,
    successProbability :: Double,
    complexity :: ComplexityFunction
} deriving (Show, Eq)

data RandomizationType = 
    MonteCarlo
  | LasVegas
  | AtlanticCity
  deriving (Show, Eq)

-- 蒙特卡洛算法
monteCarloAlgorithm :: Algorithm -> Double -> RandomizedAlgorithm
monteCarloAlgorithm algorithm successProb = 
    RandomizedAlgorithm {
        algorithmId = algorithmId algorithm ++ "_MC",
        randomizationType = MonteCarlo,
        successProbability = successProb,
        complexity = worstCase (timeComplexity algorithm)
    }

-- 拉斯维加斯算法
lasVegasAlgorithm :: Algorithm -> RandomizedAlgorithm
lasVegasAlgorithm algorithm = 
    RandomizedAlgorithm {
        algorithmId = algorithmId algorithm ++ "_LV",
        randomizationType = LasVegas,
        successProbability = 1.0,
        complexity = worstCase (timeComplexity algorithm)
    }
```

### 2. 概率分析

```haskell
-- 概率分析
class ProbabilisticAnalysis a where
    expectedComplexity :: a -> Int -> Double
    variance :: a -> Int -> Double
    concentrationBounds :: a -> Int -> ConcentrationBound

instance ProbabilisticAnalysis RandomizedAlgorithm where
    expectedComplexity algorithm n = 
        calculateExpectedComplexity algorithm n
    
    variance algorithm n = 
        calculateVariance algorithm n
    
    concentrationBounds algorithm n = 
        calculateConcentrationBounds algorithm n

-- 集中不等式
data ConcentrationBound = ConcentrationBound {
    boundType :: BoundType,
    upperBound :: Double,
    lowerBound :: Double,
    confidence :: Double
} deriving (Show, Eq)

data BoundType = 
    ChernoffBound
  | HoeffdingBound
  | AzumaBound
  deriving (Show, Eq)
```

## 形式化证明

### 时间层次定理

**定理 1**: 对于任何时间可构造函数$f(n)$，存在一个语言$L$，使得$L \in \text{TIME}(f(n)^2)$但$L \notin \text{TIME}(f(n))$。

**证明**:

```haskell
-- 时间层次定理
timeHierarchyTheorem :: ComplexityFunction -> Bool
timeHierarchyTheorem f = 
    let timeConstructible = isTimeConstructible f
        diagonalLanguage = constructDiagonalLanguage f
        inLargerClass = diagonalLanguage `inClass` timeClass (f .^ 2)
        notInSmallerClass = not (diagonalLanguage `inClass` timeClass f)
    in timeConstructible && inLargerClass && notInSmallerClass

-- 时间可构造性
isTimeConstructible :: ComplexityFunction -> Bool
isTimeConstructible f = 
    let turingMachine = constructTimeConstructibleTM f
        runsInTime = verifyTimeBound turingMachine f
    in runsInTime

-- 对角化语言
constructDiagonalLanguage :: ComplexityFunction -> Language
constructDiagonalLanguage f = 
    let diagonalTM = constructDiagonalTM f
    in Language diagonalTM
```

### 空间层次定理

**定理 2**: 对于任何空间可构造函数$f(n)$，存在一个语言$L$，使得$L \in \text{SPACE}(f(n)^2)$但$L \notin \text{SPACE}(f(n))$。

**证明**:

```haskell
-- 空间层次定理
spaceHierarchyTheorem :: ComplexityFunction -> Bool
spaceHierarchyTheorem f = 
    let spaceConstructible = isSpaceConstructible f
        diagonalLanguage = constructDiagonalLanguage f
        inLargerClass = diagonalLanguage `inClass` spaceClass (f .^ 2)
        notInSmallerClass = not (diagonalLanguage `inClass` spaceClass f)
    in spaceConstructible && inLargerClass && notInSmallerClass

-- 空间可构造性
isSpaceConstructible :: ComplexityFunction -> Bool
isSpaceConstructible f = 
    let turingMachine = constructSpaceConstructibleTM f
        usesSpace = verifySpaceBound turingMachine f
    in usesSpace
```

## 总结

计算复杂性理论为理解算法的效率和问题的固有难度提供了深刻的洞察。通过复杂度类、问题归约和下界理论，我们可以精确地分析各种计算问题的复杂性。

在Haskell中，我们可以通过类型系统、代数数据类型和函数式编程等特性，构建严格的计算复杂性分析系统，确保复杂度分析的准确性和证明的正确性。这种形式化的方法为算法设计和问题求解提供了坚实的理论基础。
