# 概率统计

## 概述

概率统计是研究随机现象和数据分析的数学分支，包括概率论、数理统计、信息论等。本文档从形式化角度探讨概率统计的核心概念和理论。

## 1. 概率论

### 1.1 概率空间

概率空间是概率论的基础。

```haskell
-- 概率空间
data ProbabilitySpace = ProbabilitySpace
  { sampleSpace :: [String]
  , sigmaAlgebra :: [[String]]
  , probabilityMeasure :: [String] -> Double
  }

-- 样本空间
data SampleSpace = SampleSpace
  { outcomes :: [String]
  , cardinality :: Int
  }

-- σ-代数
data SigmaAlgebra = SigmaAlgebra
  { algebraSets :: [[String]]
  , isSigmaAlgebra :: Bool
  }

-- σ-代数验证
isValidSigmaAlgebra :: [String] -> [[String]] -> Bool
isValidSigmaAlgebra sampleSpace algebra = 
  -- 空集属于σ-代数
  [] `elem` algebra &&
  -- 样本空间属于σ-代数
  sampleSpace `elem` algebra &&
  -- 补集封闭
  all (\set -> 
        let complement = filter (`notElem` set) sampleSpace
        in complement `elem` algebra) algebra &&
  -- 可数并集封闭
  all (\subfamily -> 
        let union = nub (concat subfamily)
        in union `elem` algebra) 
      (powerSet algebra)

-- 幂集
powerSet :: [a] -> [[a]]
powerSet [] = [[]]
powerSet (x:xs) = 
  let ps = powerSet xs
  in ps ++ map (x:) ps

-- 概率测度
data ProbabilityMeasure = ProbabilityMeasure
  { measureFunction :: [String] -> Double
  , measureProperties :: Bool
  }

-- 概率测度验证
isValidProbabilityMeasure :: ProbabilityMeasure -> [String] -> [[String]] -> Bool
isValidProbabilityMeasure measure sampleSpace algebra = 
  let function = measureFunction measure
  in -- 非负性
     all (\set -> function set >= 0) algebra &&
     -- 规范性
     function sampleSpace == 1.0 &&
     -- 可数可加性
     all (\disjointSets -> 
           let union = nub (concat disjointSets)
               sum = sum (map function disjointSets)
           in function union == sum) 
         (disjointSubfamilies algebra)

-- 不相交子族
disjointSubfamilies :: [[String]] -> [[[String]]]
disjointSubfamilies algebra = 
  let allSubsets = powerSet algebra
  in filter (\subfamily -> 
              all (\pair -> 
                    let (set1, set2) = pair
                    in null (intersect set1 set2)) 
                  (pairs subfamily)) 
            allSubsets

-- 生成所有对
pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = [(x, y) | y <- xs] ++ pairs xs
```

### 1.2 随机变量

随机变量是概率论的核心概念。

```haskell
-- 随机变量
data RandomVariable = RandomVariable
  { variableName :: String
  , variableFunction :: String -> Double
  , variableType :: VariableType
  }

-- 变量类型
data VariableType = 
  Discrete | Continuous | Mixed

-- 离散随机变量
data DiscreteRandomVariable = DiscreteRandomVariable
  { variableName :: String
  , probabilityMassFunction :: [(Double, Double)]
  , support :: [Double]
  }

-- 连续随机变量
data ContinuousRandomVariable = ContinuousRandomVariable
  { variableName :: String
  , probabilityDensityFunction :: Double -> Double
  , support :: (Double, Double)
  }

-- 概率质量函数
probabilityMassFunction :: DiscreteRandomVariable -> Double -> Double
probabilityMassFunction variable value = 
  case lookup value (probabilityMassFunction variable) of
    Just prob -> prob
    Nothing -> 0.0

-- 概率密度函数
probabilityDensityFunction :: ContinuousRandomVariable -> Double -> Double
probabilityDensityFunction variable value = 
  let (a, b) = support variable
  in if value >= a && value <= b
     then probabilityDensityFunction variable value
     else 0.0

-- 累积分布函数
cumulativeDistributionFunction :: RandomVariable -> Double -> Double
cumulativeDistributionFunction variable value = case variableType variable of
  Discrete -> 
    let discreteVar = case variable of
                        DiscreteRandomVariable name pmf support -> 
                          DiscreteRandomVariable name pmf support
                        _ -> error "Not a discrete variable"
        pmf = probabilityMassFunction discreteVar
        probabilities = [pmf x | x <- support discreteVar, x <= value]
    in sum probabilities
  Continuous -> 
    let continuousVar = case variable of
                          ContinuousRandomVariable name pdf support -> 
                            ContinuousRandomVariable name pdf support
                          _ -> error "Not a continuous variable"
        (a, _) = support continuousVar
        pdf = probabilityDensityFunction continuousVar
    in integrate pdf a value
  Mixed -> 0.5  -- 简化处理

-- 数值积分
integrate :: (Double -> Double) -> Double -> Double -> Double
integrate function a b = 
  let n = 1000
      h = (b - a) / fromIntegral n
      points = [a + i * h | i <- [0..n]]
      values = map function points
      sum = foldl (+) 0 values
  in sum * h
```

### 1.3 期望和方差

期望和方差是随机变量的重要特征。

```haskell
-- 期望
expectation :: RandomVariable -> Double
expectation variable = case variableType variable of
  Discrete -> 
    let discreteVar = case variable of
                        DiscreteRandomVariable name pmf support -> 
                          DiscreteRandomVariable name pmf support
                        _ -> error "Not a discrete variable"
        pmf = probabilityMassFunction discreteVar
        values = support discreteVar
    in sum [x * pmf x | x <- values]
  Continuous -> 
    let continuousVar = case variable of
                          ContinuousRandomVariable name pdf support -> 
                            ContinuousRandomVariable name pdf support
                          _ -> error "Not a continuous variable"
        (a, b) = support continuousVar
        pdf = probabilityDensityFunction continuousVar
        integrand x = x * pdf x
    in integrate integrand a b
  Mixed -> 0.0  -- 简化处理

-- 方差
variance :: RandomVariable -> Double
variance variable = 
  let mu = expectation variable
      squaredVariable = transformVariable variable (\x -> x^2)
      secondMoment = expectation squaredVariable
  in secondMoment - mu^2

-- 变量变换
transformVariable :: RandomVariable -> (Double -> Double) -> RandomVariable
transformVariable variable transform = 
  RandomVariable {
    variableName = variableName variable ++ "_transformed",
    variableFunction = \omega -> transform (variableFunction variable omega),
    variableType = variableType variable
  }

-- 标准差
standardDeviation :: RandomVariable -> Double
standardDeviation variable = sqrt (variance variable)

-- 矩
moment :: RandomVariable -> Int -> Double
moment variable k = 
  let transformedVariable = transformVariable variable (\x -> x^k)
  in expectation transformedVariable

-- 中心矩
centralMoment :: RandomVariable -> Int -> Double
centralMoment variable k = 
  let mu = expectation variable
      transformedVariable = transformVariable variable (\x -> (x - mu)^k)
  in expectation transformedVariable
```

### 1.4 常见分布

常见概率分布的实现。

```haskell
-- 伯努利分布
data BernoulliDistribution = BernoulliDistribution
  { successProbability :: Double
  }

-- 伯努利分布PMF
bernoulliPMF :: BernoulliDistribution -> Int -> Double
bernoulliPMF dist x = case x of
  0 -> 1 - successProbability dist
  1 -> successProbability dist
  _ -> 0.0

-- 二项分布
data BinomialDistribution = BinomialDistribution
  { numberOfTrials :: Int
  , successProbability :: Double
  }

-- 二项分布PMF
binomialPMF :: BinomialDistribution -> Int -> Double
binomialPMF dist k = 
  let n = numberOfTrials dist
      p = successProbability dist
      combinations = factorial n `div` (factorial k * factorial (n - k))
  in fromIntegral combinations * p^k * (1 - p)^(n - k)

-- 阶乘
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 泊松分布
data PoissonDistribution = PoissonDistribution
  { lambda :: Double
  }

-- 泊松分布PMF
poissonPMF :: PoissonDistribution -> Int -> Double
poissonPMF dist k = 
  let lambda = lambda dist
  in (lambda^k * exp (-lambda)) / fromIntegral (factorial k)

-- 正态分布
data NormalDistribution = NormalDistribution
  { mean :: Double
  , variance :: Double
  }

-- 正态分布PDF
normalPDF :: NormalDistribution -> Double -> Double
normalPDF dist x = 
  let mu = mean dist
      sigma2 = variance dist
      sigma = sqrt sigma2
  in (1 / (sigma * sqrt (2 * pi))) * exp (-((x - mu)^2) / (2 * sigma2))

-- 指数分布
data ExponentialDistribution = ExponentialDistribution
  { lambda :: Double
  }

-- 指数分布PDF
exponentialPDF :: ExponentialDistribution -> Double -> Double
exponentialPDF dist x = 
  let lambda = lambda dist
  in if x >= 0
     then lambda * exp (-lambda * x)
     else 0.0
```

## 2. 数理统计

### 2.1 统计推断

统计推断是从样本推断总体性质的方法。

```haskell
-- 样本
data Sample = Sample
  { sampleData :: [Double]
  , sampleSize :: Int
  , sampleSource :: String
  }

-- 样本统计量
data SampleStatistic = SampleStatistic
  { statisticName :: String
  , statisticValue :: Double
  , statisticType :: StatisticType
  }

-- 统计量类型
data StatisticType = 
  Location | Scale | Shape | Correlation

-- 样本均值
sampleMean :: Sample -> Double
sampleMean sample = 
  let data = sampleData sample
  in sum data / fromIntegral (length data)

-- 样本方差
sampleVariance :: Sample -> Double
sampleVariance sample = 
  let data = sampleData sample
      n = length data
      mean = sampleMean sample
      squaredDeviations = map (\x -> (x - mean)^2) data
  in sum squaredDeviations / fromIntegral (n - 1)

-- 样本标准差
sampleStandardDeviation :: Sample -> Double
sampleStandardDeviation sample = sqrt (sampleVariance sample)

-- 样本中位数
sampleMedian :: Sample -> Double
sampleMedian sample = 
  let data = sort (sampleData sample)
      n = length data
  in if odd n
     then data !! (n `div` 2)
     else (data !! (n `div` 2 - 1) + data !! (n `div` 2)) / 2

-- 样本分位数
sampleQuantile :: Sample -> Double -> Double
sampleQuantile sample p = 
  let data = sort (sampleData sample)
      n = length data
      index = p * fromIntegral (n - 1)
      lowerIndex = floor index
      upperIndex = ceiling index
      weight = index - fromIntegral lowerIndex
  in if lowerIndex == upperIndex
     then data !! lowerIndex
     else (1 - weight) * data !! lowerIndex + weight * data !! upperIndex
```

### 2.2 假设检验

假设检验是统计推断的重要方法。

```haskell
-- 假设检验
data HypothesisTest = HypothesisTest
  { nullHypothesis :: String
  , alternativeHypothesis :: String
  , testStatistic :: Sample -> Double
  , significanceLevel :: Double
  }

-- 检验结果
data TestResult = TestResult
  { testStatisticValue :: Double
  , pValue :: Double
  , criticalValue :: Double
  , decision :: Decision
  }

-- 决策
data Decision = 
  RejectNull | FailToRejectNull | Inconclusive

-- t检验
tTest :: Sample -> Double -> HypothesisTest
tTest sample hypothesizedMean = 
  HypothesisTest {
    nullHypothesis = "μ = " ++ show hypothesizedMean,
    alternativeHypothesis = "μ ≠ " ++ show hypothesizedMean,
    testStatistic = \s -> 
      let mean = sampleMean s
          std = sampleStandardDeviation s
          n = sampleSize s
      in (mean - hypothesizedMean) / (std / sqrt (fromIntegral n)),
    significanceLevel = 0.05
  }

-- 执行t检验
performTTest :: HypothesisTest -> Sample -> TestResult
performTTest test sample = 
  let statistic = testStatistic test sample
      n = sampleSize sample
      degreesOfFreedom = n - 1
      pValue = computePValue statistic degreesOfFreedom
      criticalValue = computeCriticalValue (significanceLevel test) degreesOfFreedom
      decision = if abs statistic > criticalValue
                 then RejectNull
                 else FailToRejectNull
  in TestResult {
    testStatisticValue = statistic,
    pValue = pValue,
    criticalValue = criticalValue,
    decision = decision
  }

-- 计算p值
computePValue :: Double -> Int -> Double
computePValue statistic df = 
  -- 简化实现，实际需要t分布表或数值方法
  if abs statistic > 2.0
  then 0.05
  else 0.5

-- 计算临界值
computeCriticalValue :: Double -> Int -> Double
computeCriticalValue alpha df = 
  -- 简化实现，实际需要t分布表
  case alpha of
    0.01 -> 2.58
    0.05 -> 1.96
    0.10 -> 1.64
    _ -> 1.96
```

### 2.3 置信区间

置信区间是参数估计的重要方法。

```haskell
-- 置信区间
data ConfidenceInterval = ConfidenceInterval
  { lowerBound :: Double
  , upperBound :: Double
  , confidenceLevel :: Double
  , parameter :: String
  }

-- 均值置信区间
meanConfidenceInterval :: Sample -> Double -> ConfidenceInterval
meanConfidenceInterval sample confidenceLevel = 
  let mean = sampleMean sample
      std = sampleStandardDeviation sample
      n = sampleSize sample
      standardError = std / sqrt (fromIntegral n)
      criticalValue = computeCriticalValue ((1 - confidenceLevel) / 2) (n - 1)
      marginOfError = criticalValue * standardError
  in ConfidenceInterval {
    lowerBound = mean - marginOfError,
    upperBound = mean + marginOfError,
    confidenceLevel = confidenceLevel,
    parameter = "μ"
  }

-- 方差置信区间
varianceConfidenceInterval :: Sample -> Double -> ConfidenceInterval
varianceConfidenceInterval sample confidenceLevel = 
  let variance = sampleVariance sample
      n = sampleSize sample
      df = n - 1
      alpha = (1 - confidenceLevel) / 2
      chi2Lower = computeChi2CriticalValue alpha df
      chi2Upper = computeChi2CriticalValue (1 - alpha) df
  in ConfidenceInterval {
    lowerBound = (fromIntegral df * variance) / chi2Upper,
    upperBound = (fromIntegral df * variance) / chi2Lower,
    confidenceLevel = confidenceLevel,
    parameter = "σ²"
  }

-- 卡方分布临界值
computeChi2CriticalValue :: Double -> Int -> Double
computeChi2CriticalValue alpha df = 
  -- 简化实现，实际需要卡方分布表
  case (alpha, df) of
    (0.025, 9) -> 19.02
    (0.975, 9) -> 2.70
    _ -> 10.0
```

## 3. 信息论

### 3.1 信息熵

信息熵是信息论的核心概念。

```haskell
-- 信息熵
data InformationEntropy = InformationEntropy
  { entropyValue :: Double
  , entropyBase :: Double
  , entropyDistribution :: [(String, Double)]
  }

-- 计算信息熵
computeEntropy :: [(String, Double)] -> Double -> Double
computeEntropy distribution base = 
  let probabilities = map snd distribution
      logProbabilities = map (\p -> if p > 0 then logBase base p else 0) probabilities
      weightedLogs = zipWith (*) probabilities logProbabilities
  in -sum weightedLogs

-- 香农熵
shannonEntropy :: [(String, Double)] -> Double
shannonEntropy distribution = computeEntropy distribution 2

-- 联合熵
jointEntropy :: [(String, Double)] -> [(String, Double)] -> Double
jointEntropy dist1 dist2 = 
  let jointDistribution = [(x ++ "," ++ y, p1 * p2) | 
                           (x, p1) <- dist1, (y, p2) <- dist2]
  in shannonEntropy jointDistribution

-- 条件熵
conditionalEntropy :: [(String, Double)] -> [(String, Double)] -> Double
conditionalEntropy dist1 dist2 = 
  let jointDist = [(x ++ "," ++ y, p1 * p2) | 
                   (x, p1) <- dist1, (y, p2) <- dist2]
      marginalDist2 = [(y, sum [p | (xy, p) <- jointDist, 
                                   let (x', y') = splitAt (length x) xy, 
                                   y' == y]) | 
                       (y, _) <- dist2]
  in jointEntropy dist1 dist2 - shannonEntropy marginalDist2
```

### 3.2 互信息

互信息衡量两个随机变量之间的依赖关系。

```haskell
-- 互信息
data MutualInformation = MutualInformation
  { mutualInformationValue :: Double
  , variable1 :: String
  , variable2 :: String
  }

-- 计算互信息
computeMutualInformation :: [(String, Double)] -> [(String, Double)] -> Double
computeMutualInformation dist1 dist2 = 
  let entropy1 = shannonEntropy dist1
      entropy2 = shannonEntropy dist2
      jointEnt = jointEntropy dist1 dist2
  in entropy1 + entropy2 - jointEnt

-- 信息增益
informationGain :: [(String, Double)] -> [(String, Double)] -> Double
informationGain target feature = 
  let targetEntropy = shannonEntropy target
      conditionalEnt = conditionalEntropy target feature
  in targetEntropy - conditionalEnt

-- 相对熵（KL散度）
relativeEntropy :: [(String, Double)] -> [(String, Double)] -> Double
relativeEntropy p q = 
  let commonOutcomes = nub (map fst p ++ map fst q)
      klTerms = [let pVal = lookup x p ? 0
                     qVal = lookup x q ? 0
                 in if pVal > 0 && qVal > 0
                    then pVal * logBase 2 (pVal / qVal)
                    else 0 | x <- commonOutcomes]
  in sum klTerms

-- 交叉熵
crossEntropy :: [(String, Double)] -> [(String, Double)] -> Double
crossEntropy p q = 
  let commonOutcomes = nub (map fst p ++ map fst q)
      crossTerms = [let pVal = lookup x p ? 0
                        qVal = lookup x q ? 0
                    in if pVal > 0 && qVal > 0
                       then -pVal * logBase 2 qVal
                       else 0 | x <- commonOutcomes]
  in sum crossTerms
```

### 3.3 信道容量

信道容量是通信理论的重要概念。

```haskell
-- 信道
data Channel = Channel
  { channelMatrix :: [[Double]]
  , inputAlphabet :: [String]
  , outputAlphabet :: [String]
  }

-- 信道容量
data ChannelCapacity = ChannelCapacity
  { capacityValue :: Double
  , optimalDistribution :: [(String, Double)]
  }

-- 计算信道容量
computeChannelCapacity :: Channel -> ChannelCapacity
computeChannelCapacity channel = 
  let matrix = channelMatrix channel
      inputs = inputAlphabet channel
      outputs = outputAlphabet channel
      -- 简化实现，实际需要迭代算法
      uniformDistribution = [(x, 1.0 / fromIntegral (length inputs)) | x <- inputs]
      capacity = mutualInformationForChannel channel uniformDistribution
  in ChannelCapacity {
    capacityValue = capacity,
    optimalDistribution = uniformDistribution
  }

-- 信道互信息
mutualInformationForChannel :: Channel -> [(String, Double)] -> Double
mutualInformationForChannel channel inputDist = 
  let matrix = channelMatrix channel
      inputs = inputAlphabet channel
      outputs = outputAlphabet channel
      -- 计算输出分布
      outputDist = [(y, sum [pX * matrix !! i !! j | 
                              (x, pX) <- zip inputs inputDist, 
                              let i = fromJust (elemIndex x inputs),
                              let j = fromJust (elemIndex y outputs)]) | 
                    y <- outputs]
      -- 计算联合分布
      jointDist = [(x ++ "," ++ y, pX * matrix !! i !! j) | 
                   (x, pX) <- zip inputs inputDist,
                   (y, _) <- zip outputs [0..],
                   let i = fromJust (elemIndex x inputs),
                   let j = fromJust (elemIndex y outputs)]
  in computeMutualInformation inputDist outputDist

-- 从Just中提取值
fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "fromJust: Nothing"
```

## 4. 机器学习数学

### 4.1 线性代数基础

线性代数是机器学习的重要数学基础。

```haskell
-- 向量
data Vector = Vector
  { vectorComponents :: [Double]
  , vectorDimension :: Int
  }

-- 向量运算
vectorAdd :: Vector -> Vector -> Vector
vectorAdd v1 v2 = 
  let components1 = vectorComponents v1
      components2 = vectorComponents v2
      sumComponents = zipWith (+) components1 components2
  in Vector {
    vectorComponents = sumComponents,
    vectorDimension = vectorDimension v1
  }

vectorScale :: Double -> Vector -> Vector
vectorScale scalar vector = 
  Vector {
    vectorComponents = map (* scalar) (vectorComponents vector),
    vectorDimension = vectorDimension vector
  }

vectorDot :: Vector -> Vector -> Double
vectorDot v1 v2 = 
  let components1 = vectorComponents v1
      components2 = vectorComponents v2
  in sum (zipWith (*) components1 components2)

vectorNorm :: Vector -> Double
vectorNorm vector = 
  sqrt (vectorDot vector vector)

-- 矩阵
data Matrix = Matrix
  { matrixRows :: Int
  , matrixColumns :: Int
  , matrixElements :: [[Double]]
  }

-- 矩阵运算
matrixAdd :: Matrix -> Matrix -> Matrix
matrixAdd m1 m2 = 
  let elements1 = matrixElements m1
      elements2 = matrixElements m2
      sumElements = zipWith (zipWith (+)) elements1 elements2
  in Matrix {
    matrixRows = matrixRows m1,
    matrixColumns = matrixColumns m1,
    matrixElements = sumElements
  }

matrixMultiply :: Matrix -> Matrix -> Matrix
matrixMultiply m1 m2 = 
  let elements1 = matrixElements m1
      elements2 = matrixElements m2
      productElements = [[sum (zipWith (*) row col) | 
                          col <- transpose elements2] | 
                         row <- elements1]
  in Matrix {
    matrixRows = matrixRows m1,
    matrixColumns = matrixColumns m2,
    matrixElements = productElements
  }

-- 转置
transpose :: [[a]] -> [[a]]
transpose [] = []
transpose ([]:_) = []
transpose matrix = 
  (map head matrix) : transpose (map tail matrix)
```

### 4.2 优化理论

优化理论是机器学习算法的基础。

```haskell
-- 优化问题
data OptimizationProblem = OptimizationProblem
  { objectiveFunction :: [Double] -> Double
  , constraintFunctions :: [[Double] -> Double]
  , variableBounds :: [(Double, Double)]
  }

-- 梯度
gradient :: ([Double] -> Double) -> [Double] -> [Double]
gradient function point = 
  let h = 0.001
      n = length point
  in [partialDerivative function point i h | i <- [0..n-1]]

-- 偏导数
partialDerivative :: ([Double] -> Double) -> [Double] -> Int -> Double -> Double
partialDerivative function point index h = 
  let pointPlusH = take index point ++ 
                   [point !! index + h] ++ 
                   drop (index + 1) point
      pointMinusH = take index point ++ 
                    [point !! index - h] ++ 
                    drop (index + 1) point
  in (function pointPlusH - function pointMinusH) / (2 * h)

-- 梯度下降
gradientDescent :: ([Double] -> Double) -> [Double] -> Double -> Int -> [Double]
gradientDescent function initialPoint learningRate maxIterations = 
  let iterations = iterate (\point -> 
                             let grad = gradient function point
                                 step = map (* learningRate) grad
                             in zipWith (-) point step) 
                          initialPoint
  in iterations !! maxIterations

-- 牛顿法
newtonMethod :: ([Double] -> Double) -> [Double] -> Int -> [Double]
newtonMethod function initialPoint maxIterations = 
  let iterations = iterate (\point -> 
                             let grad = gradient function point
                                 hessian = hessianMatrix function point
                                 direction = solveLinearSystem hessian (map negate grad)
                             in zipWith (+) point direction) 
                          initialPoint
  in iterations !! maxIterations

-- 海森矩阵
hessianMatrix :: ([Double] -> Double) -> [Double] -> [[Double]]
hessianMatrix function point = 
  let n = length point
  in [[secondPartialDerivative function point i j | j <- [0..n-1]] | i <- [0..n-1]]

-- 二阶偏导数
secondPartialDerivative :: ([Double] -> Double) -> [Double] -> Int -> Int -> Double
secondPartialDerivative function point i j = 
  let h = 0.001
      pointPlusHi = take i point ++ [point !! i + h] ++ drop (i + 1) point
      pointPlusHj = take j point ++ [point !! j + h] ++ drop (j + 1) point
      pointPlusHiHj = take i pointPlusHj ++ [pointPlusHj !! i + h] ++ drop (i + 1) pointPlusHj
      pointMinusHi = take i point ++ [point !! i - h] ++ drop (i + 1) point
      pointMinusHj = take j point ++ [point !! j - h] ++ drop (j + 1) point
      pointMinusHiMinusHj = take i pointMinusHj ++ [pointMinusHj !! i - h] ++ drop (i + 1) pointMinusHj
  in (function pointPlusHiHj - function pointPlusHi - function pointPlusHj + function point) / (h^2)

-- 解线性方程组
solveLinearSystem :: [[Double]] -> [Double] -> [Double]
solveLinearSystem matrix vector = 
  -- 简化实现，实际需要高斯消元法
  replicate (length vector) 0.0
```

## 总结

概率统计为理解随机现象和数据分析提供了强大的数学工具。通过形式化方法，我们可以：

1. **精确建模**：用数学结构精确描述随机现象
2. **统计推断**：从样本推断总体性质
3. **信息分析**：量化信息量和不确定性
4. **算法优化**：为机器学习提供数学基础

概率统计的研究将继续推动我们对随机现象的理解，并为科学和工程应用提供理论基础。 