# 统计分析 - 形式化理论与Haskell实现

## 📋 概述

统计分析是数据科学的核心基础，通过数学方法对数据进行收集、整理、分析和解释。本文档从形式化角度建立统计分析的完整理论体系。

## 🎯 核心概念

### 1. 概率空间

#### 形式化定义

**定义 1.1 (概率空间)** 概率空间是一个三元组 $(\Omega, \mathcal{F}, P)$，其中：

- $\Omega$ 是样本空间
- $\mathcal{F}$ 是 $\sigma$-代数
- $P: \mathcal{F} \to [0,1]$ 是概率测度

-**公理 1.1 (概率公理)**

1. $P(\Omega) = 1$
2. $P(A) \geq 0$ 对所有 $A \in \mathcal{F}$
3. 对互斥事件序列 $\{A_i\}_{i=1}^{\infty}$，$P(\bigcup_{i=1}^{\infty} A_i) = \sum_{i=1}^{\infty} P(A_i)$

#### Haskell实现

```haskell
{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Statistics.ProbabilitySpace where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (nub)

-- 样本空间
type SampleSpace a = Set a

-- σ-代数
type SigmaAlgebra a = Set (Set a)

-- 概率测度
type ProbabilityMeasure a = Set a -> Double

-- 概率空间
data ProbabilitySpace a where
  ProbabilitySpace :: 
    { sampleSpace :: SampleSpace a
    , sigmaAlgebra :: SigmaAlgebra a
    , probabilityMeasure :: ProbabilityMeasure a
    } -> ProbabilitySpace a

-- 验证概率公理
validateProbabilityAxioms :: (Ord a, Show a) => ProbabilitySpace a -> Bool
validateProbabilityAxioms (ProbabilitySpace omega f p) =
  let axiom1 = abs (p omega - 1.0) < 1e-10  -- P(Ω) = 1
      axiom2 = all (\a -> p a >= 0) (Set.toList f)  -- P(A) ≥ 0
      axiom3 = validateCountableAdditivity omega f p  -- 可数可加性
  in axiom1 && axiom2 && axiom3

-- 验证可数可加性
validateCountableAdditivity :: (Ord a) => 
  SampleSpace a -> SigmaAlgebra a -> ProbabilityMeasure a -> Bool
validateCountableAdditivity omega f p =
  -- 简化实现：检查有限互斥事件
  let events = Set.toList f
      disjointPairs = [(a, b) | a <- events, b <- events, 
                               a /= b, Set.null (a `Set.intersection` b)]
  in all (\(a, b) -> abs (p (a `Set.union` b) - (p a + p b)) < 1e-10) disjointPairs

-- 示例：掷骰子的概率空间
diceProbabilitySpace :: ProbabilitySpace Int
diceProbabilitySpace = ProbabilitySpace
  { sampleSpace = Set.fromList [1..6]
  , sigmaAlgebra = Set.fromList [Set.empty, Set.fromList [1..6]]
  , probabilityMeasure = \a -> 
      if Set.null a then 0.0
      else fromIntegral (Set.size a) / 6.0
  }
```

### 2. 随机变量

#### 2.1 形式化定义

**定义 1.2 (随机变量)** 设 $(\Omega, \mathcal{F}, P)$ 是概率空间，$(\mathbb{R}, \mathcal{B})$ 是可测空间，则随机变量 $X: \Omega \to \mathbb{R}$ 满足：
$$\forall B \in \mathcal{B}, X^{-1}(B) \in \mathcal{F}$$

**定义 1.3 (分布函数)** 随机变量 $X$ 的分布函数 $F_X: \mathbb{R} \to [0,1]$ 定义为：
$$F_X(x) = P(X \leq x)$$

#### 2.2 Haskell实现

```haskell
module Statistics.RandomVariable where

import Statistics.ProbabilitySpace
import Data.Set (Set)
import qualified Data.Set as Set

-- 随机变量
type RandomVariable a b = a -> b

-- 分布函数
type DistributionFunction = Double -> Double

-- 离散随机变量
data DiscreteRandomVariable a b where
  DiscreteRV :: 
    { rvFunction :: RandomVariable a b
    , support :: Set b
    , probabilityMass :: b -> Double
    } -> DiscreteRandomVariable a b

-- 连续随机变量
data ContinuousRandomVariable a where
  ContinuousRV :: 
    { rvFunction :: RandomVariable a Double
    , densityFunction :: Double -> Double
    } -> ContinuousRandomVariable a

-- 计算期望
expectation :: (Num b, Fractional b) => DiscreteRandomVariable a b -> b
expectation (DiscreteRV _ support pmf) =
  sum [x * pmf x | x <- Set.toList support]

-- 计算方差
variance :: (Num b, Fractional b) => DiscreteRandomVariable a b -> b
variance rv@(DiscreteRV _ support pmf) =
  let mu = expectation rv
  in sum [(x - mu)^2 * pmf x | x <- Set.toList support]

-- 示例：伯努利随机变量
bernoulliRV :: Double -> DiscreteRandomVariable Int Int
bernoulliRV p = DiscreteRV
  { rvFunction = \omega -> if omega == 1 then 1 else 0
  , support = Set.fromList [0, 1]
  , probabilityMass = \x -> case x of
      0 -> 1 - p
      1 -> p
      _ -> 0
  }
```

### 3. 统计推断

#### 3.1 形式化定义

**定义 1.4 (统计模型)** 统计模型是参数化概率分布的集合：
$$\mathcal{P} = \{P_\theta : \theta \in \Theta\}$$

**定义 1.5 (最大似然估计)** 给定观测数据 $x_1, \ldots, x_n$，最大似然估计为：
$$\hat{\theta}_{MLE} = \arg\max_{\theta \in \Theta} L(\theta; x_1, \ldots, x_n)$$
其中似然函数 $L(\theta; x_1, \ldots, x_n) = \prod_{i=1}^n f(x_i; \theta)$

#### 3.2 Haskell实现

```haskell
module Statistics.Inference where

import Statistics.RandomVariable
import Data.List (maximumBy)
import Data.Ord (comparing)

-- 统计模型
type StatisticalModel a b = b -> a -> Double  -- θ -> x -> f(x;θ)

-- 似然函数
likelihood :: StatisticalModel a b -> b -> [a] -> Double
likelihood model theta observations =
  product [model theta x | x <- observations]

-- 对数似然函数
logLikelihood :: StatisticalModel a b -> b -> [a] -> Double
logLikelihood model theta observations =
  sum [log (model theta x) | x <- observations]

-- 最大似然估计
maximumLikelihoodEstimate :: 
  (Ord b, Show b) => 
  StatisticalModel a b -> 
  [b] ->  -- 参数空间
  [a] ->  -- 观测数据
  b
maximumLikelihoodEstimate model parameterSpace observations =
  maximumBy (comparing (\theta -> logLikelihood model theta observations)) 
            parameterSpace

-- 示例：正态分布的最大似然估计
normalMLE :: [Double] -> (Double, Double)
normalMLE observations =
  let n = fromIntegral (length observations)
      mu = sum observations / n
      sigma2 = sum [(x - mu)^2 | x <- observations] / n
  in (mu, sqrt sigma2)

-- 置信区间
confidenceInterval :: 
  Double ->  -- 置信水平
  [Double] ->  -- 样本
  (Double, Double)
confidenceInterval confidenceLevel sample =
  let n = fromIntegral (length sample)
      mean = sum sample / n
      std = sqrt (sum [(x - mean)^2 | x <- sample] / (n - 1))
      z = 1.96  -- 95% 置信水平对应的z值
      margin = z * std / sqrt n
  in (mean - margin, mean + margin)
```

## 🔬 高级统计方法

### 1. 贝叶斯统计

#### 1.1 形式化定义

**定理 1.1 (贝叶斯定理)** 设 $A, B$ 是事件，$P(B) > 0$，则：
$$P(A|B) = \frac{P(B|A)P(A)}{P(B)}$$

**定义 1.6 (后验分布)** 给定先验分布 $p(\theta)$ 和似然函数 $L(\theta; x)$，后验分布为：
$$p(\theta|x) \propto L(\theta; x)p(\theta)$$

#### 1.2 Haskell实现

```haskell
module Statistics.Bayesian where

import Statistics.Inference
import Data.List (mapAccumL)

-- 先验分布
type Prior a = a -> Double

-- 后验分布
type Posterior a = a -> Double

-- 贝叶斯更新
bayesianUpdate :: 
  StatisticalModel a b -> 
  Prior b -> 
  b ->  -- 参数
  a ->  -- 观测
  Double
bayesianUpdate model prior theta observation =
  let likelihood = model theta observation
      priorProb = prior theta
  in likelihood * priorProb

-- 后验分布计算
posteriorDistribution :: 
  StatisticalModel a b -> 
  Prior b -> 
  [b] ->  -- 参数空间
  [a] ->  -- 观测数据
  [(b, Double)]
posteriorDistribution model prior parameterSpace observations =
  let unnormalized = [(theta, bayesianUpdate model prior theta obs) 
                     | theta <- parameterSpace, obs <- observations]
      total = sum [prob | (_, prob) <- unnormalized]
  in [(theta, prob / total) | (theta, prob) <- unnormalized]

-- 最大后验估计
maximumAPosteriori :: 
  (Ord b) => 
  StatisticalModel a b -> 
  Prior b -> 
  [b] -> 
  [a] -> 
  b
maximumAPosteriori model prior parameterSpace observations =
  let posteriors = posteriorDistribution model prior parameterSpace observations
  in fst $ maximumBy (comparing snd) posteriors
```

### 2. 假设检验

#### 2.1 形式化定义1

**定义 1.7 (假设检验)** 假设检验是统计推断的重要方法，包括：

- 零假设 $H_0: \theta \in \Theta_0$
- 备择假设 $H_1: \theta \in \Theta_1$
- 检验统计量 $T(X)$
- 拒绝域 $R$

**定义 1.8 (p值)** p值是观测到比当前样本更极端结果的概率：
$$p\text{-value} = P(T(X) \geq t_{obs} | H_0)$$

#### 2.2 Haskell实现1

```haskell
module Statistics.HypothesisTesting where

import Statistics.Inference
import Statistics.RandomVariable
import Data.List (sort)

-- 假设检验
data HypothesisTest a b where
  HypothesisTest :: 
    { nullHypothesis :: b -> Bool
    , alternativeHypothesis :: b -> Bool
    , testStatistic :: [a] -> Double
    , criticalValue :: Double -> Double
    } -> HypothesisTest a b

-- t检验
tTest :: [Double] -> Double -> (Double, Double)
tTest sample hypothesizedMean =
  let n = fromIntegral (length sample)
      sampleMean = sum sample / n
      sampleVar = sum [(x - sampleMean)^2 | x <- sample] / (n - 1)
      tStat = (sampleMean - hypothesizedMean) / sqrt (sampleVar / n)
      -- 简化：使用正态分布近似
      pValue = 2 * (1 - normalCDF (abs tStat))
  in (tStat, pValue)

-- 正态分布累积分布函数（近似）
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))
  where erf z = 2 / sqrt pi * sum [((-1)^n * z^(2*n+1)) / (factorial n * (2*n+1)) | n <- [0..10]]
        factorial n = product [1..n]
        pi = 3.14159265359

-- 卡方检验
chiSquareTest :: [Int] -> [Double] -> (Double, Double)
chiSquareTest observed expected =
  let chiSquare = sum [(o - e)^2 / e | (o, e) <- zip observed expected]
      df = length observed - 1
      -- 简化：使用卡方分布近似
      pValue = 1 - chiSquareCDF chiSquare df
  in (chiSquare, pValue)

-- 卡方分布累积分布函数（近似）
chiSquareCDF :: Double -> Int -> Double
chiSquareCDF x df = gammaIncomplete (fromIntegral df / 2) (x / 2)
  where gammaIncomplete a x = 1 - exp (-x) * sum [x^k / factorial k | k <- [0..floor a]]
        factorial n = product [1..n]
```

## 📊 数据可视化

### 1. 描述性统计

#### 1.1 Haskell实现

```haskell
module Statistics.Descriptive where

import Data.List (sort, group)
import Data.Map (Map)
import qualified Data.Map as Map

-- 描述性统计
data DescriptiveStats = DescriptiveStats
  { mean :: Double
  , median :: Double
  , mode :: Double
  , variance :: Double
  , standardDeviation :: Double
  , skewness :: Double
  , kurtosis :: Double
  } deriving (Show)

-- 计算描述性统计
descriptiveStatistics :: [Double] -> DescriptiveStats
descriptiveStatistics data_ =
  let n = fromIntegral (length data_)
      sorted = sort data_
      mean_ = sum data_ / n
      median_ = if odd n 
                then sorted !! (n `div` 2)
                else (sorted !! (n `div` 2 - 1) + sorted !! (n `div` 2)) / 2
      mode_ = modeOf data_
      variance_ = sum [(x - mean_)^2 | x <- data_] / (n - 1)
      stdDev = sqrt variance_
      skewness_ = skewnessOf data_ mean_ stdDev
      kurtosis_ = kurtosisOf data_ mean_ stdDev
  in DescriptiveStats mean_ median_ mode_ variance_ stdDev skewness_ kurtosis_

-- 众数
modeOf :: [Double] -> Double
modeOf data_ =
  let grouped = group $ sort data_
      maxFreq = maximum $ map length grouped
      modes = [head group | group <- grouped, length group == maxFreq]
  in head modes

-- 偏度
skewnessOf :: [Double] -> Double -> Double -> Double
skewnessOf data_ mean_ stdDev =
  let n = fromIntegral (length data_)
      thirdMoment = sum [(x - mean_)^3 | x <- data_] / n
  in thirdMoment / (stdDev^3)

-- 峰度
kurtosisOf :: [Double] -> Double -> Double -> Double
kurtosisOf data_ mean_ stdDev =
  let n = fromIntegral (length data_)
      fourthMoment = sum [(x - mean_)^4 | x <- data_] / n
  in fourthMoment / (stdDev^4) - 3
```

## 🎯 应用示例

### 1. 回归分析

```haskell
module Statistics.Regression where

import Statistics.Descriptive
import Data.List (zipWith)

-- 线性回归
data LinearRegression = LinearRegression
  { slope :: Double
  , intercept :: Double
  , rSquared :: Double
  } deriving (Show)

-- 最小二乘法线性回归
linearRegression :: [(Double, Double)] -> LinearRegression
linearRegression data_ =
  let n = fromIntegral (length data_)
      x = map fst data_
      y = map snd data_
      xMean = sum x / n
      yMean = sum y / n
      slope_ = sum [(xi - xMean) * (yi - yMean) | (xi, yi) <- data_] / 
               sum [(xi - xMean)^2 | xi <- x]
      intercept_ = yMean - slope_ * xMean
      rSquared_ = correlationCoefficient x y ^ 2
  in LinearRegression slope_ intercept_ rSquared_

-- 相关系数
correlationCoefficient :: [Double] -> [Double] -> Double
correlationCoefficient x y =
  let n = fromIntegral (length x)
      xMean = sum x / n
      yMean = sum y / n
      numerator = sum [(xi - xMean) * (yi - yMean) | (xi, yi) <- zip x y]
      xVar = sum [(xi - xMean)^2 | xi <- x]
      yVar = sum [(yi - yMean)^2 | yi <- y]
      denominator = sqrt (xVar * yVar)
  in numerator / denominator

-- 预测
predict :: LinearRegression -> Double -> Double
predict (LinearRegression slope intercept _) x = slope * x + intercept
```

## 📚 形式化证明

### 定理 1.1: 线性回归的最小二乘性质

**证明** 设线性回归模型 $y_i = \beta_0 + \beta_1 x_i + \epsilon_i$，最小二乘估计为：
$$\hat{\beta}_1 = \frac{\sum_{i=1}^n (x_i - \bar{x})(y_i - \bar{y})}{\sum_{i=1}^n (x_i - \bar{x})^2}$$
$$\hat{\beta}_0 = \bar{y} - \hat{\beta}_1 \bar{x}$$

**证明步骤**：

1. 定义残差平方和：$SSE = \sum_{i=1}^n (y_i - \hat{y}_i)^2$
2. 对 $\beta_0$ 和 $\beta_1$ 求偏导数并令其为零
3. 求解得到上述估计量
4. 验证二阶导数矩阵为正定，确认为最小值

### 定理 1.2: 中心极限定理

**定理** 设 $X_1, X_2, \ldots$ 是独立同分布的随机变量，期望为 $\mu$，方差为 $\sigma^2$，则：
$$\frac{\bar{X}_n - \mu}{\sigma/\sqrt{n}} \xrightarrow{d} N(0,1)$$

**证明** 使用特征函数方法：

1. 计算 $\bar{X}_n$ 的特征函数
2. 取对数并展开到二阶项
3. 证明极限为 $e^{-t^2/2}$，即标准正态分布的特征函数

## 🔗 相关链接

- [数学基础](../02-Formal-Science/01-Mathematical-Foundations/01-Set-Theory.md)
- [概率论](../02-Formal-Science/01-Mathematical-Foundations/02-Probability-Theory.md)
- [机器学习](../04-Applied-Science/03-Artificial-Intelligence/01-Machine-Learning.md)
- [数据挖掘](./02-Data-Mining.md)

---

*本文档建立了统计分析的完整形式化理论体系，包含严格的数学定义、Haskell实现和形式化证明。*
