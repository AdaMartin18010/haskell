# 概率论基础

## 概述

概率论是研究随机现象数学规律的学科，为统计学、机器学习、信息论等提供理论基础。它通过严格的数学公理化体系，为不确定性建模提供了精确的工具。

## 形式化定义

### 概率空间

#### 概率空间公理

概率空间 $(\Omega, \mathcal{F}, P)$ 由以下三个要素组成：

1. **样本空间** $\Omega$：所有可能结果的集合
2. **事件域** $\mathcal{F}$：$\Omega$ 的子集族，满足 $\sigma$-代数性质
3. **概率测度** $P$：$\mathcal{F} \to [0,1]$ 的函数，满足概率公理

```haskell
-- 概率空间
data ProbabilitySpace a = ProbabilitySpace {
  sampleSpace :: [a],
  eventField :: [[a]],
  probabilityMeasure :: [a] -> Double
} deriving (Show)

-- 概率公理验证
class ProbabilityAxioms a where
  isProbabilitySpace :: ProbabilitySpace a -> Bool
  isEventField :: [[a]] -> Bool
  isProbabilityMeasure :: ([a] -> Double) -> [[a]] -> Bool
  
  isProbabilitySpace space = 
    let events = eventField space
        measure = probabilityMeasure space
    in isEventField events &&
       isProbabilityMeasure measure events &&
       measure (sampleSpace space) == 1.0 &&
       all (\event -> measure event >= 0.0) events
       
  isEventField events = 
    let omega = concat events  -- 假设样本空间是事件的并
    in [] `elem` events &&
       omega `elem` events &&
       isClosedUnderComplement events omega &&
       isClosedUnderCountableUnion events
       
  isProbabilityMeasure measure events = 
    measure [] == 0.0 &&
    all (\event -> measure event >= 0.0 && measure event <= 1.0) events &&
    isCountablyAdditive measure events

-- 辅助函数
isClosedUnderComplement :: Eq a => [[a]] -> [a] -> Bool
isClosedUnderComplement events omega = 
  all (\event -> filter (`notElem` event) omega `elem` events) events

isClosedUnderCountableUnion :: Eq a => [[a]] -> Bool
isClosedUnderCountableUnion events = 
  let allUnions = [concat subset | subset <- subsequences events]
  in all (\union -> union `elem` events) allUnions

isCountablyAdditive :: Eq a => ([a] -> Double) -> [[a]] -> Bool
isCountablyAdditive measure events = 
  let disjointEvents = findDisjointEvents events
      unions = map concat disjointEvents
      sumOfMeasures = map (sum . map measure) disjointEvents
      measuresOfUnions = map measure unions
  in all (\(sum, union) -> abs (sum - union) < 0.001) (zip sumOfMeasures measuresOfUnions)

findDisjointEvents :: Eq a => [[a]] -> [[[a]]]
findDisjointEvents events = 
  let pairs = [(e1, e2) | e1 <- events, e2 <- events, e1 /= e2]
      disjointPairs = filter (\(e1, e2) -> null (intersect e1 e2)) pairs
  in map (\(e1, e2) -> [e1, e2]) disjointPairs
```

#### 常见概率空间

```haskell
-- 离散概率空间
discreteProbabilitySpace :: [(a, Double)] -> ProbabilitySpace a
discreteProbabilitySpace outcomes = 
  let sampleSpace = map fst outcomes
      probabilities = map snd outcomes
      eventField = subsequences sampleSpace
      measure = \event -> 
        let eventOutcomes = filter (\outcome -> fst outcome `elem` event) outcomes
        in sum (map snd eventOutcomes)
  in ProbabilitySpace sampleSpace eventField measure

-- 均匀概率空间
uniformProbabilitySpace :: [a] -> ProbabilitySpace a
uniformProbabilitySpace elements = 
  let n = length elements
      probability = 1.0 / fromIntegral n
      outcomes = zip elements (repeat probability)
  in discreteProbabilitySpace outcomes

-- 伯努利试验
bernoulliTrial :: Double -> ProbabilitySpace Bool
bernoulliTrial p = 
  let outcomes = [(True, p), (False, 1.0 - p)]
  in discreteProbabilitySpace outcomes

-- 二项分布
binomialDistribution :: Int -> Double -> ProbabilitySpace Int
binomialDistribution n p = 
  let outcomes = [(k, binomialProbability n k p) | k <- [0..n]]
  in discreteProbabilitySpace outcomes

binomialProbability :: Int -> Int -> Double -> Double
binomialProbability n k p = 
  let combination = fromIntegral (choose n k)
  in combination * p^k * (1.0 - p)^(n - k)

choose :: Int -> Int -> Int
choose n k = 
  product [n-k+1..n] `div` product [1..k]
```

### 随机变量

#### 随机变量定义

```haskell
-- 随机变量
type RandomVariable a b = a -> b

-- 随机变量类型类
class RandomVariable a b where
  expectation :: RandomVariable a b -> ProbabilitySpace a -> Double
  variance :: RandomVariable a b -> ProbabilitySpace a -> Double
  distribution :: RandomVariable a b -> ProbabilitySpace a -> [(b, Double)]
  
  expectation rv space = 
    let outcomes = sampleSpace space
        measure = probabilityMeasure space
        values = map rv outcomes
        probabilities = map (\outcome -> measure [outcome]) outcomes
    in sum (zipWith (*) values probabilities)
    
  variance rv space = 
    let mu = expectation rv space
        outcomes = sampleSpace space
        measure = probabilityMeasure space
        squaredDeviations = map (\outcome -> (rv outcome - mu)^2) outcomes
        probabilities = map (\outcome -> measure [outcome]) outcomes
    in sum (zipWith (*) squaredDeviations probabilities)
    
  distribution rv space = 
    let outcomes = sampleSpace space
        measure = probabilityMeasure space
        values = map rv outcomes
        probabilities = map (\outcome -> measure [outcome]) outcomes
        grouped = groupByValues values probabilities
    in grouped

-- 辅助函数
groupByValues :: Eq b => [b] -> [Double] -> [(b, Double)]
groupByValues values probabilities = 
  let pairs = zip values probabilities
      grouped = groupBy fst pairs
  in map (\group -> (fst (head group), sum (map snd group))) grouped

-- 常见随机变量
bernoulliRandomVariable :: RandomVariable Bool Int
bernoulliRandomVariable True = 1
bernoulliRandomVariable False = 0

binomialRandomVariable :: Int -> RandomVariable [Bool] Int
binomialRandomVariable n outcomes = 
  length (filter id outcomes)

geometricRandomVariable :: RandomVariable [Bool] Int
geometricRandomVariable outcomes = 
  case findIndex id outcomes of
    Just i -> i + 1
    Nothing -> length outcomes
```

#### 随机变量运算

```haskell
-- 随机变量运算
class RandomVariableOperations a b where
  addRandomVariables :: RandomVariable a b -> RandomVariable a b -> RandomVariable a b
  multiplyRandomVariables :: RandomVariable a b -> RandomVariable a b -> RandomVariable a b
  transformRandomVariable :: (b -> c) -> RandomVariable a b -> RandomVariable a c
  
  addRandomVariables rv1 rv2 = \outcome -> rv1 outcome + rv2 outcome
  
  multiplyRandomVariables rv1 rv2 = \outcome -> rv1 outcome * rv2 outcome
  
  transformRandomVariable f rv = \outcome -> f (rv outcome)

-- 独立随机变量
class IndependentRandomVariables a b where
  areIndependent :: RandomVariable a b -> RandomVariable a b -> ProbabilitySpace a -> Bool
  jointDistribution :: RandomVariable a b -> RandomVariable a b -> ProbabilitySpace a -> [((b, b), Double)]
  
  areIndependent rv1 rv2 space = 
    let joint = jointDistribution rv1 rv2 space
        marginal1 = marginalDistribution rv1 space
        marginal2 = marginalDistribution rv2 space
        independent = all (\((x, y), p) -> 
          let p1 = lookup x marginal1
              p2 = lookup y marginal2
          in case (p1, p2) of
               (Just p1', Just p2') -> abs (p - p1' * p2') < 0.001
               _ -> False) joint
    in independent
    
  jointDistribution rv1 rv2 space = 
    let outcomes = sampleSpace space
        measure = probabilityMeasure space
        values1 = map rv1 outcomes
        values2 = map rv2 outcomes
        probabilities = map (\outcome -> measure [outcome]) outcomes
        pairs = zip values1 values2
        grouped = groupByPairs pairs probabilities
    in grouped

-- 辅助函数
marginalDistribution :: Eq b => RandomVariable a b -> ProbabilitySpace a -> [(b, Double)]
marginalDistribution rv space = 
  distribution rv space

groupByPairs :: Eq b => [(b, b)] -> [Double] -> [((b, b), Double)]
groupByPairs pairs probabilities = 
  let combined = zip pairs probabilities
      grouped = groupBy fst combined
  in map (\group -> (fst (head group), sum (map snd group))) grouped
```

### 条件概率

#### 条件概率定义

```haskell
-- 条件概率
class ConditionalProbability a where
  conditionalProbability :: ProbabilitySpace a -> [a] -> [a] -> Double
  bayesTheorem :: ProbabilitySpace a -> [a] -> [a] -> Double
  totalProbability :: ProbabilitySpace a -> [[a]] -> [a] -> Double
  
  conditionalProbability space eventA eventB = 
    let measure = probabilityMeasure space
        intersection = intersect eventA eventB
        pA = measure eventA
        pB = measure eventB
    in if pB > 0 then measure intersection / pB else 0.0
    
  bayesTheorem space eventA eventB = 
    let measure = probabilityMeasure space
        pA = measure eventA
        pB = measure eventB
        pBGivenA = conditionalProbability space eventB eventA
    in if pA > 0 then pBGivenA * pA / pB else 0.0
    
  totalProbability space partitions event = 
    let measure = probabilityMeasure space
        conditionalProbs = map (\partition -> 
          conditionalProbability space event partition) partitions
        partitionProbs = map measure partitions
    in sum (zipWith (*) conditionalProbs partitionProbs)

-- 贝叶斯网络
data BayesianNetwork a = BayesianNetwork {
  nodes :: [a],
  edges :: [(a, a)],
  conditionalProbabilities :: [(a, [a], Double)]
} deriving (Show)

-- 贝叶斯推理
class BayesianInference a where
  posteriorProbability :: BayesianNetwork a -> a -> [a] -> Double
  priorProbability :: BayesianNetwork a -> a -> Double
  likelihood :: BayesianNetwork a -> a -> [a] -> Double
  
  posteriorProbability network node evidence = 
    let prior = priorProbability network node
        likelihood = likelihood network node evidence
        evidenceProb = evidenceProbability network evidence
    in if evidenceProb > 0 then prior * likelihood / evidenceProb else 0.0
    
  priorProbability network node = 
    let cps = conditionalProbabilities network
        nodeCPs = filter (\(n, _, _) -> n == node) cps
    in case nodeCPs of
         ((_, _, p):_) -> p
         [] -> 0.0
         
  likelihood network node evidence = 
    let cps = conditionalProbabilities network
        relevantCPs = filter (\(n, parents, _) -> n == node && all (`elem` evidence) parents) cps
    in case relevantCPs of
         ((_, _, p):_) -> p
         [] -> 1.0

evidenceProbability :: BayesianNetwork a -> [a] -> Double
evidenceProbability network evidence = 
  let nodes = nodes network
      allProbabilities = [priorProbability network node | node <- evidence]
  in product allProbabilities
```

## 形式化证明

### 概率论基本定理

#### 定理1：全概率公式

对于事件 $A$ 和完备事件组 $\{B_i\}_{i=1}^n$，有：
$P(A) = \sum_{i=1}^n P(A|B_i)P(B_i)$

**证明**：

```haskell
-- 全概率公式的Haskell实现
totalProbabilityTheorem :: ProbabilitySpace a -> [a] -> [[a]] -> Bool
totalProbabilityTheorem space event partitions = 
  let measure = probabilityMeasure space
      leftSide = measure event
      rightSide = totalProbability space partitions event
      isPartition = isCompletePartition space partitions
  in isPartition ==> abs (leftSide - rightSide) < 0.001

-- 形式化证明
totalProbabilityProof :: Proof
totalProbabilityProof = Apply TotalProbability [
  Axiom (PartitionAxiom "Bi"),
  Apply DisjointUnion [Axiom (EventAxiom "A"), Axiom (PartitionAxiom "Bi")]
]
```

#### 定理2：贝叶斯定理

对于事件 $A$ 和 $B$，有：
$P(A|B) = \frac{P(B|A)P(A)}{P(B)}$

**证明**：

```haskell
-- 贝叶斯定理的Haskell实现
bayesTheorem :: ProbabilitySpace a -> [a] -> [a] -> Bool
bayesTheorem space eventA eventB = 
  let measure = probabilityMeasure space
      pAGivenB = conditionalProbability space eventA eventB
      pBGivenA = conditionalProbability space eventB eventA
      pA = measure eventA
      pB = measure eventB
      rightSide = if pB > 0 then pBGivenA * pA / pB else 0.0
  in abs (pAGivenB - rightSide) < 0.001

-- 形式化证明
bayesProof :: Proof
bayesProof = Apply BayesTheorem [
  Axiom (ConditionalProbabilityAxiom "P(A|B)"),
  Apply DefinitionOfConditional [Axiom (EventAxiom "A"), Axiom (EventAxiom "B")]
]
```

#### 定理3：大数定律

对于独立同分布的随机变量序列 $\{X_n\}$，有：
$\lim_{n \to \infty} \frac{1}{n}\sum_{i=1}^n X_i = \mu$ (几乎必然)

**证明**：

```haskell
-- 大数定律的Haskell实现
lawOfLargeNumbers :: [RandomVariable a Double] -> ProbabilitySpace a -> Bool
lawOfLargeNumbers rvs space = 
  let n = length rvs
      mu = expectation (head rvs) space
      sampleMeans = [average (map (\rv -> rv outcome) rvs) | outcome <- sampleSpace space]
      convergence = all (\mean -> abs (mean - mu) < 0.1) sampleMeans
  in n > 100 ==> convergence

-- 形式化证明
lawOfLargeNumbersProof :: Proof
lawOfLargeNumbersProof = Apply LawOfLargeNumbers [
  Axiom (IIDAxiom "Xn"),
  Apply ChebyshevInequality [Axiom (RandomVariableAxiom "Xn")]
]
```

## 应用示例

### 统计推断

```haskell
-- 统计推断
class StatisticalInference a b where
  maximumLikelihoodEstimation :: [a] -> (b -> a -> Double) -> b
  bayesianEstimation :: [a] -> (b -> Double) -> (b -> a -> Double) -> b
  confidenceInterval :: [a] -> Double -> (Double, Double)
  
  maximumLikelihoodEstimation data likelihood = 
    let parameterSpace = generateParameterSpace
        likelihoods = map (\theta -> product (map (likelihood theta) data)) parameterSpace
        maxIndex = maximumIndex likelihoods
    in parameterSpace !! maxIndex
    
  bayesianEstimation data prior likelihood = 
    let parameterSpace = generateParameterSpace
        posteriors = map (\theta -> 
          prior theta * product (map (likelihood theta) data)) parameterSpace
        totalPosterior = sum posteriors
        normalizedPosteriors = map (/ totalPosterior) posteriors
        expectedValue = sum (zipWith (*) parameterSpace normalizedPosteriors)
    in expectedValue
    
  confidenceInterval data confidence = 
    let n = length data
        mean = average data
        stdDev = sqrt (variance data)
        z = inverseNormalCDF ((1 + confidence) / 2)
        margin = z * stdDev / sqrt (fromIntegral n)
    in (mean - margin, mean + margin)

-- 辅助函数
average :: [Double] -> Double
average xs = sum xs / fromIntegral (length xs)

variance :: [Double] -> Double
variance xs = 
  let mu = average xs
      squaredDeviations = map (\x -> (x - mu)^2) xs
  in average squaredDeviations

maximumIndex :: [Double] -> Int
maximumIndex xs = 
  snd (maximum (zip xs [0..]))

generateParameterSpace :: [Double]
generateParameterSpace = 
  [0.1, 0.2..1.0]  -- 简化实现

inverseNormalCDF :: Double -> Double
inverseNormalCDF p = 
  -- 简化实现，实际需要数值方法
  if p > 0.5 then 1.96 else -1.96
```

### 马尔可夫链

```haskell
-- 马尔可夫链
data MarkovChain a = MarkovChain {
  states :: [a],
  transitionMatrix :: [[Double]],
  initialDistribution :: [Double]
} deriving (Show)

-- 马尔可夫链性质
class MarkovChainProperties a where
  isIrreducible :: MarkovChain a -> Bool
  isAperiodic :: MarkovChain a -> Bool
  stationaryDistribution :: MarkovChain a -> [Double]
  
  isIrreducible chain = 
    let matrix = transitionMatrix chain
        n = length matrix
        reachable = iterateMatrixPower matrix n
    in all (\row -> all (> 0) row) reachable
    
  isAperiodic chain = 
    let matrix = transitionMatrix chain
        n = length matrix
        periods = findPeriods matrix
    in all (\period -> period == 1) periods
    
  stationaryDistribution chain = 
    let matrix = transitionMatrix chain
        n = length matrix
        -- 求解线性方程组 πP = π
        equations = map (\i -> 
          [if j == i then matrix !! i !! j - 1 else matrix !! i !! j | j <- [0..n-1]]) [0..n-1]
        solution = solveLinearSystem equations
    in solution

-- 辅助函数
iterateMatrixPower :: [[Double]] -> Int -> [[Double]]
iterateMatrixPower matrix n = 
  iterate (matrixMultiply matrix) matrix !! n

matrixMultiply :: [[Double]] -> [[Double]] -> [[Double]]
matrixMultiply a b = 
  [[sum (zipWith (*) (a !! i) (map (!! j) b)) | j <- [0..length (head b) - 1]] | i <- [0..length a - 1]]

findPeriods :: [[Double]] -> [Int]
findPeriods matrix = 
  let n = length matrix
      periods = [gcd n (length (filter (> 0) row)) | row <- matrix]
  in periods

solveLinearSystem :: [[Double]] -> [Double]
solveLinearSystem equations = 
  -- 简化实现，实际需要高斯消元
  replicate (length equations) (1.0 / fromIntegral (length equations))
```

### 随机过程

```haskell
-- 随机过程
data StochasticProcess a b = StochasticProcess {
  timeIndex :: [a],
  stateSpace :: [b],
  probabilityMeasure :: [a] -> [b] -> Double
} deriving (Show)

-- 布朗运动
data BrownianMotion = BrownianMotion {
  timePoints :: [Double],
  initialValue :: Double,
  volatility :: Double
} deriving (Show)

class BrownianMotionProperties where
  simulateBrownianMotion :: BrownianMotion -> [Double]
  brownianMotionProperties :: BrownianMotion -> Bool
  
  simulateBrownianMotion bm = 
    let dt = 0.01
        times = [0, dt..last (timePoints bm)]
        increments = map (\_ -> normalRandom 0 (volatility bm * sqrt dt)) (tail times)
        path = scanl (+) (initialValue bm) increments
    in path
    
  brownianMotionProperties bm = 
    let path = simulateBrownianMotion bm
        increments = zipWith (-) (tail path) path
        meanIncrement = average increments
        varianceIncrement = variance increments
        expectedVariance = volatility bm^2 * 0.01
    in abs meanIncrement < 0.1 && abs (varianceIncrement - expectedVariance) < 0.1

-- 辅助函数
normalRandom :: Double -> Double -> Double
normalRandom mu sigma = 
  -- 简化实现，实际需要Box-Muller变换
  mu + sigma * (sum (take 12 (randomRs (0, 1) (mkStdGen 42))) - 6)
```

## 形式化验证

### 概率性质验证

```haskell
-- 概率性质验证器
class ProbabilityValidator a where
  validateProbabilitySpace :: ProbabilitySpace a -> ProbabilityValidation
  validateRandomVariable :: RandomVariable a Double -> ProbabilitySpace a -> RandomVariableValidation
  validateIndependence :: [RandomVariable a Double] -> ProbabilitySpace a -> IndependenceValidation

data ProbabilityValidation = ProbabilityValidation {
  isValid :: Bool,
  violations :: [String],
  properties :: [String]
} deriving (Show)

data RandomVariableValidation = RandomVariableValidation {
  hasFiniteExpectation :: Bool,
  hasFiniteVariance :: Bool,
  distributionType :: String
} deriving (Show)

data IndependenceValidation = IndependenceValidation {
  areIndependent :: Bool,
  correlationMatrix :: [[Double]],
  independenceTests :: [Bool]
} deriving (Show)

instance ProbabilityValidator Double where
  validateProbabilitySpace space = ProbabilityValidation {
    isValid = isProbabilitySpace space,
    violations = findProbabilityViolations space,
    properties = identifyProbabilityProperties space
  }
  
  validateRandomVariable rv space = RandomVariableValidation {
    hasFiniteExpectation = isFinite (expectation rv space),
    hasFiniteVariance = isFinite (variance rv space),
    distributionType = classifyDistribution rv space
  }
  
  validateIndependence rvs space = IndependenceValidation {
    areIndependent = allIndependent rvs space,
    correlationMatrix = computeCorrelationMatrix rvs space,
    independenceTests = map (\rv -> isIndependent rv rvs space) rvs
  }

-- 辅助函数
findProbabilityViolations :: ProbabilitySpace a -> [String]
findProbabilityViolations space = 
  let violations = []
      violations' = if not (isProbabilitySpace space)
                   then "Invalid probability space" : violations
                   else violations
      violations'' = if not (isEventField (eventField space))
                    then "Invalid event field" : violations'
                    else violations'
      violations''' = if not (isProbabilityMeasure (probabilityMeasure space) (eventField space))
                     then "Invalid probability measure" : violations''
                     else violations''
  in violations'''

identifyProbabilityProperties :: ProbabilitySpace a -> [String]
identifyProbabilityProperties space = 
  let properties = []
      properties' = if isFinite (sampleSpace space) then "Finite" : properties else properties
      properties'' = if isUniform space then "Uniform" : properties' else properties'
      properties''' = if isSymmetric space then "Symmetric" : properties'' else properties''
  in properties'''

isFinite :: [a] -> Bool
isFinite = not . null

isUniform :: ProbabilitySpace a -> Bool
isUniform space = 
  let outcomes = sampleSpace space
      measure = probabilityMeasure space
      n = length outcomes
      expectedProb = 1.0 / fromIntegral n
      actualProbs = map (\outcome -> measure [outcome]) outcomes
  in all (\p -> abs (p - expectedProb) < 0.001) actualProbs

isSymmetric :: ProbabilitySpace a -> Bool
isSymmetric space = 
  let outcomes = sampleSpace space
      measure = probabilityMeasure space
      pairs = [(outcomes !! i, outcomes !! (length outcomes - 1 - i)) | i <- [0..length outcomes `div` 2]]
  in all (\(a, b) -> measure [a] == measure [b]) pairs

classifyDistribution :: RandomVariable a Double -> ProbabilitySpace a -> String
classifyDistribution rv space = 
  let values = map rv (sampleSpace space)
      mean = expectation rv space
      variance = variance rv space
  in if variance == 0 then "Degenerate"
     else if all (\v -> v == 0 || v == 1) values then "Bernoulli"
     else if all (\v -> v >= 0 && v == fromIntegral (round v)) values then "Discrete"
     else "Continuous"
```

## 总结

概率论为不确定性建模提供了严格的数学基础，通过Haskell的类型系统和函数式编程特性，我们可以实现严格的概率论系统。这些实现不仅具有理论价值，也为统计学、机器学习、金融建模等应用领域提供了重要工具。

## 相关链接

- [概率统计主索引](../README.md)
- [数理统计](../02-Mathematical-Statistics.md)
- [信息论](../03-Information-Theory.md)
- [机器学习数学](../04-Machine-Learning-Mathematics.md)
