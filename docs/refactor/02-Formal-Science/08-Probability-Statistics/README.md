# 08-概率统计 (Probability and Statistics)

## 概述

概率统计是研究随机现象和数据分析的数学分支，为机器学习、数据科学、信息论等提供基础数学工具。在形式化知识体系中，概率统计为人工智能、数据挖掘、风险评估等提供理论框架。

## 目录结构

### 01-概率论 (Probability Theory)

- **01-概率空间** (Probability Spaces)
- **02-随机变量** (Random Variables)
- **03-概率分布** (Probability Distributions)
- **04-随机过程** (Stochastic Processes)

### 02-数理统计 (Mathematical Statistics)

- **01-统计推断** (Statistical Inference)
- **02-假设检验** (Hypothesis Testing)
- **03-回归分析** (Regression Analysis)
- **04-贝叶斯统计** (Bayesian Statistics)

### 03-信息论 (Information Theory)

- **01-信息度量** (Information Measures)
- **02-熵理论** (Entropy Theory)
- **03-编码理论** (Coding Theory)
- **04-信道理论** (Channel Theory)

### 04-机器学习数学 (Machine Learning Mathematics)

- **01-统计学习理论** (Statistical Learning Theory)
- **02-优化理论** (Optimization Theory)
- **03-矩阵分解** (Matrix Factorization)
- **04-核方法** (Kernel Methods)

## 核心概念

### 概率空间 (Probability Spaces)

```haskell
-- 概率空间
data ProbabilitySpace = ProbabilitySpace
  { sampleSpace :: Set
  , sigmaAlgebra :: SigmaAlgebra
  , probabilityMeasure :: ProbabilityMeasure
  }

-- σ-代数
data SigmaAlgebra = SigmaAlgebra
  { sets :: [Set]
  , properties :: [SigmaAlgebraProperty]
  }

-- 概率测度
data ProbabilityMeasure = ProbabilityMeasure
  { function :: Set -> Double
  , properties :: [ProbabilityAxiom]
  }

-- 概率公理
data ProbabilityAxiom = NonNegative
                      | Normalized
                      | CountableAdditivity
                      deriving (Show, Eq)

-- 概率空间验证
isProbabilitySpace :: ProbabilitySpace -> Bool
isProbabilitySpace (ProbabilitySpace sampleSpace sigmaAlgebra probabilityMeasure) =
  isSigmaAlgebra sigmaAlgebra sampleSpace &&
  satisfiesProbabilityAxioms probabilityMeasure

-- 概率公理检查
satisfiesProbabilityAxioms :: ProbabilityMeasure -> Bool
satisfiesProbabilityAxioms (ProbabilityMeasure function axioms) =
  all (\axiom -> checkProbabilityAxiom axiom function) axioms

-- 非负性
checkProbabilityAxiom :: ProbabilityAxiom -> (Set -> Double) -> Bool
checkProbabilityAxiom NonNegative measure =
  all (\set -> measure set >= 0) allSets
checkProbabilityAxiom Normalized measure =
  measure sampleSpace == 1.0
checkProbabilityAxiom CountableAdditivity measure =
  all (\disjointSets -> measure (unionSets disjointSets) == sum (map measure disjointSets)) allDisjointCollections
```

### 随机变量 (Random Variables)

```haskell
-- 随机变量
data RandomVariable = RandomVariable
  { domain :: ProbabilitySpace
  , codomain :: Set
  , function :: Element -> Element
  , measurable :: Bool
  }

-- 随机变量验证
isRandomVariable :: RandomVariable -> Bool
isRandomVariable (RandomVariable domain codomain function measurable) =
  measurable &&
  all (\set -> isMeasurable (preimage function set) domain) (measurableSets codomain)

-- 离散随机变量
data DiscreteRandomVariable = DiscreteRandomVariable
  { variable :: RandomVariable
  , support :: [Element]
  , probabilityMass :: Element -> Double
  }

-- 连续随机变量
data ContinuousRandomVariable = ContinuousRandomVariable
  { variable :: RandomVariable
  , support :: Interval
  , probabilityDensity :: Real -> Double
  }

-- 期望
expectation :: RandomVariable -> Double
expectation (RandomVariable domain codomain function _) =
  case variableType domain of
    Discrete -> sum [function x * probabilityMass domain x | x <- support domain]
    Continuous -> integrate (\x -> function x * probabilityDensity domain x) (support domain)

-- 方差
variance :: RandomVariable -> Double
variance randomVar =
  let mu = expectation randomVar
      squaredDiff = \x -> (function randomVar x - mu)^2
  in expectation (RandomVariable (domain randomVar) (codomain randomVar) squaredDiff True)
```

### 概率分布 (Probability Distributions)

```haskell
-- 概率分布
class ProbabilityDistribution a where
  type Support a
  
  probabilityMass :: a -> Support a -> Double
  cumulativeDistribution :: a -> Support a -> Double
  expectation :: a -> Double
  variance :: a -> Double

-- 离散分布
data DiscreteDistribution = Bernoulli Double
                         | Binomial Int Double
                         | Poisson Double
                         | Geometric Double
                         deriving (Show, Eq)

-- 连续分布
data ContinuousDistribution = Normal Double Double
                           | Exponential Double
                           | Uniform Double Double
                           | Gamma Double Double
                           deriving (Show, Eq)

-- 伯努利分布
instance ProbabilityDistribution DiscreteDistribution where
  type Support DiscreteDistribution = [0, 1]
  
  probabilityMass (Bernoulli p) 0 = 1 - p
  probabilityMass (Bernoulli p) 1 = p
  probabilityMass _ _ = 0
  
  cumulativeDistribution (Bernoulli p) x
    | x < 0 = 0
    | x < 1 = 1 - p
    | otherwise = 1
  
  expectation (Bernoulli p) = p
  variance (Bernoulli p) = p * (1 - p)

-- 正态分布
instance ProbabilityDistribution ContinuousDistribution where
  type Support ContinuousDistribution = Real
  
  probabilityMass (Normal mu sigma) x =
    (1 / (sigma * sqrt (2 * pi))) * exp (-((x - mu)^2) / (2 * sigma^2))
  
  cumulativeDistribution (Normal mu sigma) x =
    (1/2) * (1 + erf ((x - mu) / (sigma * sqrt 2)))
  
  expectation (Normal mu _) = mu
  variance (Normal _ sigma) = sigma^2
```

### 统计推断 (Statistical Inference)

```haskell
-- 统计推断
data StatisticalInference = StatisticalInference
  { data_ :: [Observation]
  , model :: StatisticalModel
  , method :: InferenceMethod
  , result :: InferenceResult
  }

-- 统计模型
data StatisticalModel = StatisticalModel
  { family :: DistributionFamily
  , parameters :: [Parameter]
  , assumptions :: [Assumption]
  }

-- 推断方法
data InferenceMethod = MaximumLikelihood
                     | Bayesian
                     | MethodOfMoments
                     | LeastSquares
                     deriving (Show, Eq)

-- 最大似然估计
maximumLikelihoodEstimate :: StatisticalModel -> [Observation] -> [Parameter]
maximumLikelihoodEstimate model observations =
  let likelihood = computeLikelihood model observations
      logLikelihood = log likelihood
      gradient = computeGradient logLikelihood
      mle = findMaximum gradient
  in mle

-- 似然函数
computeLikelihood :: StatisticalModel -> [Observation] -> Double
computeLikelihood (StatisticalModel family parameters _) observations =
  product [probabilityMass family parameters obs | obs <- observations]

-- 对数似然
logLikelihood :: StatisticalModel -> [Observation] -> Double
logLikelihood model observations =
  sum [log (probabilityMass model obs) | obs <- observations]
```

### 假设检验 (Hypothesis Testing)

```haskell
-- 假设检验
data HypothesisTest = HypothesisTest
  { nullHypothesis :: Hypothesis
  , alternativeHypothesis :: Hypothesis
  , testStatistic :: TestStatistic
  , significanceLevel :: Double
  , decision :: TestDecision
  }

-- 假设
data Hypothesis = Hypothesis
  { statement :: String
  , parameters :: [Parameter]
  , type_ :: HypothesisType
  }

-- 检验统计量
data TestStatistic = TestStatistic
  { function :: [Observation] -> Double
  , distribution :: Distribution
  , criticalValue :: Double
  }

-- 检验决策
data TestDecision = RejectNull
                  | FailToRejectNull
                  | Inconclusive
                  deriving (Show, Eq)

-- t检验
tTest :: [Double] -> Double -> Double -> HypothesisTest
tTest sample hypothesizedMean significanceLevel =
  let sampleMean = mean sample
      sampleStd = standardDeviation sample
      n = length sample
      tStatistic = (sampleMean - hypothesizedMean) / (sampleStd / sqrt n)
      criticalValue = tCriticalValue (n-1) significanceLevel
      decision = if abs tStatistic > criticalValue then RejectNull else FailToRejectNull
  in HypothesisTest
       (Hypothesis "μ = μ₀" [hypothesizedMean] Simple)
       (Hypothesis "μ ≠ μ₀" [hypothesizedMean] Composite)
       (TestStatistic (\_ -> tStatistic) (TDistribution (n-1)) criticalValue)
       significanceLevel
       decision
```

### 信息论 (Information Theory)

```haskell
-- 信息论
class InformationTheory a where
  type Information a
  
  entropy :: a -> Double
  mutualInformation :: a -> a -> Double
  relativeEntropy :: a -> a -> Double

-- 熵
entropy :: [Double] -> Double
entropy probabilities =
  let validProbs = filter (> 0) probabilities
  in -sum [p * log2 p | p <- validProbs]

-- 互信息
mutualInformation :: [Double] -> [Double] -> [Double] -> Double
mutualInformation pX pY pXY =
  let hX = entropy pX
      hY = entropy pY
      hXY = entropy pXY
  in hX + hY - hXY

-- 相对熵（KL散度）
relativeEntropy :: [Double] -> [Double] -> Double
relativeEntropy p q =
  let validPairs = filter (\(pi, qi) -> pi > 0 && qi > 0) (zip p q)
  in sum [pi * log2 (pi / qi) | (pi, qi) <- validPairs]

-- 香农熵
shannonEntropy :: DiscreteRandomVariable -> Double
shannonEntropy (DiscreteRandomVariable _ support pmf) =
  let probabilities = [pmf x | x <- support]
  in entropy probabilities

-- 条件熵
conditionalEntropy :: DiscreteRandomVariable -> DiscreteRandomVariable -> Double
conditionalEntropy x y =
  let jointProb = jointProbabilityMass x y
      marginalProb = marginalProbabilityMass y
      conditionalProb = \x_val y_val -> jointProb x_val y_val / marginalProb y_val
  in sum [jointProb x_val y_val * log2 (1 / conditionalProb x_val y_val) | x_val <- support x, y_val <- support y]
```

### 机器学习数学 (Machine Learning Mathematics)

```haskell
-- 统计学习理论
data StatisticalLearningTheory = StatisticalLearningTheory
  { hypothesisSpace :: HypothesisSpace
  , riskFunction :: RiskFunction
  , generalizationBound :: GeneralizationBound
  }

-- 假设空间
data HypothesisSpace = HypothesisSpace
  { functions :: [Function]
  , complexity :: Complexity
  , capacity :: Capacity
  }

-- 风险函数
data RiskFunction = RiskFunction
  { empiricalRisk :: [Observation] -> Function -> Double
  , trueRisk :: Distribution -> Function -> Double
  , regularization :: Function -> Double
  }

-- 泛化界
data GeneralizationBound = GeneralizationBound
  { bound :: Double
  , confidence :: Double
  , sampleSize :: Int
  }

-- VC维
vcDimension :: HypothesisSpace -> Int
vcDimension (HypothesisSpace functions _ _) =
  maximum [n | n <- [1..], canShatter functions n]

-- 能否打散
canShatter :: [Function] -> Int -> Bool
canShatter functions n =
  let allLabelings = allBinaryLabelings n
  in all (\labeling -> exists (\f -> canRealize f labeling) functions) allLabelings

-- 优化理论
class Optimization a where
  type Objective a
  type Constraint a
  
  objective :: a -> Objective a
  constraints :: a -> [Constraint a]
  gradient :: a -> Objective a -> [Double]
  hessian :: a -> Objective a -> Matrix

-- 梯度下降
gradientDescent :: (Objective a -> [Double]) -> [Double] -> Double -> Int -> [Double]
gradientDescent gradient initial learningRate maxIterations =
  let iterations = iterate (\x -> x - map (* learningRate) (gradient x)) initial
  in iterations !! maxIterations

-- 随机梯度下降
stochasticGradientDescent :: (Observation -> [Double]) -> [Observation] -> [Double] -> Double -> Int -> [Double]
stochasticGradientDescent gradient observations initial learningRate maxIterations =
  let iterations = iterate (\x -> 
        let batch = take 10 observations  -- 小批量
            avgGradient = average [gradient obs | obs <- batch]
        in x - map (* learningRate) avgGradient) initial
  in iterations !! maxIterations
```

## 形式化方法

### 概率证明 (Probabilistic Proofs)

```haskell
-- 概率证明系统
data ProbabilisticProof = ProbabilisticProof
  { theorem :: Theorem
  { steps :: [ProofStep]
  , conclusion :: Conclusion
  , confidence :: Double
  }

-- 概率不等式
data ProbabilisticInequality = MarkovInequality
                             | ChebyshevInequality
                             | ChernoffBound
                             | HoeffdingInequality
                             deriving (Show, Eq)

-- 马尔可夫不等式
markovInequality :: RandomVariable -> Double -> Double
markovInequality randomVar a =
  let mu = expectation randomVar
  in mu / a

-- 切比雪夫不等式
chebyshevInequality :: RandomVariable -> Double -> Double
chebyshevInequality randomVar k =
  let sigma2 = variance randomVar
      mu = expectation randomVar
  in sigma2 / (k^2)
```

### 统计算法 (Statistical Algorithms)

```haskell
-- 统计算法
class StatisticalAlgorithm a where
  type Data a
  type Result a
  
  estimate :: a -> Data a -> Result a
  confidence :: a -> Data a -> ConfidenceInterval
  validate :: a -> Data a -> ValidationResult

-- 贝叶斯推断
data BayesianInference = BayesianInference
  { prior :: Prior
  , likelihood :: Likelihood
  , posterior :: Posterior
  }

-- 先验分布
data Prior = Prior
  { distribution :: Distribution
  , parameters :: [Parameter]
  }

-- 后验分布
data Posterior = Posterior
  { distribution :: Distribution
  , parameters :: [Parameter]
  , evidence :: Double
  }

-- 贝叶斯更新
bayesianUpdate :: Prior -> [Observation] -> Posterior
bayesianUpdate prior observations =
  let likelihood = computeLikelihood observations
      posterior = multiply prior likelihood
      evidence = normalize posterior
  in Posterior (distribution posterior) (parameters posterior) evidence
```

## 应用示例

### 1. 机器学习应用

```haskell
-- 朴素贝叶斯分类器
data NaiveBayesClassifier = NaiveBayesClassifier
  { classes :: [Class]
  , featureDistributions :: [(Feature, Distribution)]
  , classPriors :: [Double]
  }

-- 训练朴素贝叶斯
trainNaiveBayes :: [(Observation, Class)] -> NaiveBayesClassifier
trainNaiveBayes trainingData =
  let classes = nub [c | (_, c) <- trainingData]
      classPriors = [count c trainingData / length trainingData | c <- classes]
      featureDistributions = [(f, estimateDistribution f trainingData) | f <- features]
  in NaiveBayesClassifier classes featureDistributions classPriors

-- 预测
predict :: NaiveBayesClassifier -> Observation -> Class
predict classifier observation =
  let classScores = [computeClassScore classifier observation c | c <- classes classifier]
      maxIndex = maximumIndex classScores
  in classes classifier !! maxIndex

-- 计算类别得分
computeClassScore :: NaiveBayesClassifier -> Observation -> Class -> Double
computeClassScore classifier observation class_ =
  let prior = classPriors classifier !! (classIndex class_)
      likelihood = product [probabilityMass dist (featureValue observation f) | (f, dist) <- featureDistributions classifier]
  in prior * likelihood
```

### 2. 数据挖掘应用

```haskell
-- 聚类分析
data Clustering = Clustering
  { algorithm :: ClusteringAlgorithm
  , clusters :: [Cluster]
  , centroids :: [Centroid]
  }

-- K-means聚类
kMeans :: [Point] -> Int -> [Cluster]
kMeans points k =
  let initialCentroids = randomCentroids points k
      iterations = iterate (updateClusters points) initialCentroids
      converged = findConverged iterations
  in assignToClusters points converged

-- 更新聚类
updateClusters :: [Point] -> [Centroid] -> [Centroid]
updateClusters points centroids =
  let clusters = assignToClusters points centroids
      newCentroids = [computeCentroid cluster | cluster <- clusters]
  in newCentroids

-- 计算质心
computeCentroid :: [Point] -> Centroid
computeCentroid points =
  let n = length points
      sumX = sum [x | Point x _ <- points]
      sumY = sum [y | Point _ y <- points]
  in Centroid (sumX / n) (sumY / n)
```

### 3. 风险评估应用

```haskell
-- 风险模型
data RiskModel = RiskModel
  { riskFactors :: [RiskFactor]
  , probabilityModel :: ProbabilityModel
  , impactModel :: ImpactModel
  }

-- 风险因子
data RiskFactor = RiskFactor
  { name :: String
  , distribution :: Distribution
  , correlation :: [Double]
  }

-- 蒙特卡洛模拟
monteCarloSimulation :: RiskModel -> Int -> [Double]
monteCarloSimulation model n =
  let scenarios = generateScenarios model n
      losses = map (computeLoss model) scenarios
  in losses

-- 生成场景
generateScenarios :: RiskModel -> Int -> [[Double]]
generateScenarios model n =
  let factorSamples = [sample (distribution factor) n | factor <- riskFactors model]
      correlatedSamples = applyCorrelation factorSamples (correlationMatrix model)
  in transpose correlatedSamples

-- 计算损失
computeLoss :: RiskModel -> [Double] -> Double
computeLoss model scenario =
  let probabilities = [probabilityModel model factor value | (factor, value) <- zip (riskFactors model) scenario]
      impacts = [impactModel model factor value | (factor, value) <- zip (riskFactors model) scenario]
  in sum [p * i | (p, i) <- zip probabilities impacts]
```

## 与其他理论的关系

### 与代数学的关系

- 线性代数为多元统计提供工具
- 群论为对称性分析提供框架
- 矩阵论为降维方法提供基础

### 与分析学的关系

- 微积分为连续分布提供工具
- 泛函分析为随机过程提供框架
- 优化理论为参数估计提供方法

### 与计算机科学的关系

- 为机器学习提供理论基础
- 为数据挖掘提供算法
- 为人工智能提供推理方法

---

**相关链接**：

- [形式科学层 - 数学基础](../01-Mathematics/README.md)
- [具体科学层 - 数据科学](../04-Applied-Science/04-Data-Science/README.md)
- [具体科学层 - 人工智能](../04-Applied-Science/03-Artificial-Intelligence/README.md)
