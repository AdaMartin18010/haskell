# 数据挖掘 - 形式化理论与Haskell实现

## 📋 概述

数据挖掘是从大量数据中发现有用模式、关联和知识的过程。本文档从形式化角度建立数据挖掘的完整理论体系，包括分类、聚类、关联规则挖掘等核心算法。

## 🎯 核心概念

### 1. 数据挖掘基础

#### 形式化定义

**定义 1.1 (数据集)** 数据集 $D$ 是一个元组 $(X, Y, f)$，其中：

- $X = \{x_1, \ldots, x_n\}$ 是特征空间
- $Y$ 是目标空间（监督学习）或空集（无监督学习）
- $f: X \to Y$ 是目标函数（监督学习）

**定义 1.2 (模式)** 模式 $P$ 是数据集 $D$ 中满足特定条件的数据子集：
$$P = \{x \in D : \phi(x)\}$$
其中 $\phi$ 是模式描述函数。

#### Haskell实现

```haskell
{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module DataMining.Core where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub)

-- 特征向量
type FeatureVector a = [a]

-- 数据集
data Dataset a b where
  SupervisedDataset :: 
    { features :: [FeatureVector a]
    , labels :: [b]
    } -> Dataset a b
  UnsupervisedDataset :: 
    { features :: [FeatureVector a]
    } -> Dataset a b

-- 模式描述函数
type PatternDescription a = FeatureVector a -> Bool

-- 模式
data Pattern a where
  Pattern :: 
    { description :: PatternDescription a
    , support :: Double
    , confidence :: Double
    } -> Pattern a

-- 计算支持度
support :: (Eq a) => PatternDescription a -> [FeatureVector a] -> Double
support pattern data_ =
  let matching = filter pattern data_
      total = length data_
  in fromIntegral (length matching) / fromIntegral total

-- 计算置信度（用于关联规则）
confidence :: (Eq a) => 
  PatternDescription a -> 
  PatternDescription a -> 
  [FeatureVector a] -> 
  Double
confidence antecedent consequent data_ =
  let antecedentSupport = support antecedent data_
      bothSupport = support (\x -> antecedent x && consequent x) data_
  in if antecedentSupport > 0 then bothSupport / antecedentSupport else 0
```

### 2. 分类算法

#### 形式化定义

**定义 1.3 (分类问题)** 给定训练集 $T = \{(x_i, y_i)\}_{i=1}^n$，学习函数 $f: X \to Y$ 使得：
$$\forall (x, y) \in T, f(x) = y$$

**定义 1.4 (决策树)** 决策树是一个递归结构：

- 叶节点：包含类别标签
- 内部节点：包含分裂条件和子节点

#### Haskell实现

```haskell
module DataMining.Classification where

import DataMining.Core
import Data.List (maximumBy, group, sort)
import Data.Ord (comparing)
import Data.Map (Map)
import qualified Data.Map as Map

-- 决策树
data DecisionTree a b where
  Leaf :: b -> DecisionTree a b
  Node :: 
    { splitFeature :: Int
    , splitValue :: a
    , leftChild :: DecisionTree a b
    , rightChild :: DecisionTree a b
    } -> DecisionTree a b

-- 信息熵
entropy :: (Eq b) => [b] -> Double
entropy labels =
  let total = length labels
      counts = Map.fromListWith (+) [(label, 1) | label <- labels]
      probabilities = [fromIntegral count / fromIntegral total | count <- Map.elems counts]
  in -sum [p * logBase 2 p | p <- probabilities, p > 0]

-- 信息增益
informationGain :: (Ord a, Eq b) => 
  Int ->  -- 特征索引
  a ->    -- 分裂值
  [(FeatureVector a, b)] ->  -- 训练数据
  Double
informationGain featureIndex splitValue data_ =
  let parentEntropy = entropy [label | (_, label) <- data_]
      leftData = [(features, label) | (features, label) <- data_, 
                                     features !! featureIndex <= splitValue]
      rightData = [(features, label) | (features, label) <- data_, 
                                      features !! featureIndex > splitValue]
      leftEntropy = entropy [label | (_, label) <- leftData]
      rightEntropy = entropy [label | (_, label) <- rightData]
      leftWeight = fromIntegral (length leftData) / fromIntegral (length data_)
      rightWeight = fromIntegral (length rightData) / fromIntegral (length data_)
  in parentEntropy - (leftWeight * leftEntropy + rightWeight * rightEntropy)

-- 构建决策树
buildDecisionTree :: (Ord a, Eq b) => [(FeatureVector a, b)] -> DecisionTree a b
buildDecisionTree data_
  | allSameLabels = Leaf (snd $ head data_)
  | otherwise = 
      let bestSplit = findBestSplit data_
          leftData = [(features, label) | (features, label) <- data_, 
                                         features !! (fst bestSplit) <= snd bestSplit]
          rightData = [(features, label) | (features, label) <- data_, 
                                          features !! (fst bestSplit) > snd bestSplit]
      in Node (fst bestSplit) (snd bestSplit) 
             (buildDecisionTree leftData) 
             (buildDecisionTree rightData)
  where
    allSameLabels = length (nub [label | (_, label) <- data_]) == 1

-- 找到最佳分裂点
findBestSplit :: (Ord a, Eq b) => [(FeatureVector a, b)] -> (Int, a)
findBestSplit data_ =
  let numFeatures = length (fst $ head data_)
      featureValues = [[features !! i | (features, _) <- data_] | i <- [0..numFeatures-1]]
      splits = [(i, value) | i <- [0..numFeatures-1], 
                            value <- nub (featureValues !! i)]
      gains = [(split, informationGain (fst split) (snd split) data_) | split <- splits]
  in maximumBy (comparing snd) gains

-- 预测
predict :: (Ord a) => DecisionTree a b -> FeatureVector a -> b
predict (Leaf label) _ = label
predict (Node featureIndex splitValue left right) features =
  if features !! featureIndex <= splitValue
  then predict left features
  else predict right features

-- 朴素贝叶斯分类器
data NaiveBayes a b = NaiveBayes
  { classProbabilities :: Map b Double
  , featureProbabilities :: Map (b, Int, a) Double
  } deriving (Show)

-- 训练朴素贝叶斯
trainNaiveBayes :: (Ord a, Eq b) => [(FeatureVector a, b)] -> NaiveBayes a b
trainNaiveBayes data_ =
  let total = length data_
      classCounts = Map.fromListWith (+) [(label, 1) | (_, label) <- data_]
      classProbs = Map.map (\count -> fromIntegral count / fromIntegral total) classCounts
      
      featureProbs = Map.fromListWith (+) 
        [(label, featureIndex, featureValue, 1) | 
         (features, label) <- data_, 
         (featureIndex, featureValue) <- zip [0..] features]
      
      featureProbsNormalized = Map.mapWithKey 
        (\(label, featureIndex, featureValue) count ->
           count / fromIntegral (classCounts Map.! label))
        featureProbs
  in NaiveBayes classProbs featureProbsNormalized

-- 朴素贝叶斯预测
predictNaiveBayes :: (Ord a) => NaiveBayes a b -> FeatureVector a -> b
predictNaiveBayes model features =
  let classScores = Map.mapWithKey (\class_ classProb ->
        let featureScore = product [Map.findWithDefault 0.1 (class_, i, feature) model.featureProbabilities 
                                  | (i, feature) <- zip [0..] features]
        in classProb * featureScore) model.classProbabilities
  in fst $ maximumBy (comparing snd) (Map.toList classScores)
```

### 3. 聚类算法

#### 形式化定义

**定义 1.5 (聚类)** 聚类是将数据集 $D$ 划分为 $k$ 个不相交子集 $C_1, \ldots, C_k$ 的过程：
$$D = \bigcup_{i=1}^k C_i, \quad C_i \cap C_j = \emptyset \text{ for } i \neq j$$

**定义 1.6 (K-means目标函数)** K-means最小化以下目标函数：
$$J = \sum_{i=1}^k \sum_{x \in C_i} \|x - \mu_i\|^2$$
其中 $\mu_i$ 是聚类 $C_i$ 的中心。

#### Haskell实现

```haskell
module DataMining.Clustering where

import DataMining.Core
import Data.List (minimumBy, maximumBy, nub)
import Data.Ord (comparing)
import Data.Map (Map)
import qualified Data.Map as Map

-- 聚类结果
type Cluster a = [FeatureVector a]
type Clustering a = [Cluster a]

-- 欧几里得距离
euclideanDistance :: (Num a) => FeatureVector a -> FeatureVector a -> Double
euclideanDistance x y = sqrt $ sum [(xi - yi)^2 | (xi, yi) <- zip x y]

-- K-means聚类
kMeans :: (Num a, Fractional a) => 
  Int ->  -- 聚类数
  [FeatureVector a] ->  -- 数据
  Clustering a
kMeans k data_ =
  let initialCentroids = take k data_  -- 简化：使用前k个点作为初始中心
      finalCentroids = converge data_ initialCentroids
  in assignToClusters data_ finalCentroids

-- 收敛到最终中心
converge :: (Num a, Fractional a) => 
  [FeatureVector a] -> 
  [FeatureVector a] -> 
  [FeatureVector a]
converge data_ centroids =
  let newCentroids = updateCentroids data_ centroids
  in if centroids == newCentroids
     then centroids
     else converge data_ newCentroids

-- 更新聚类中心
updateCentroids :: (Num a, Fractional a) => 
  [FeatureVector a] -> 
  [FeatureVector a] -> 
  [FeatureVector a]
updateCentroids data_ centroids =
  let assignments = [findClosest centroid data_ | centroid <- centroids]
      newCentroids = [computeCentroid cluster | cluster <- assignments]
  in newCentroids

-- 找到最近的聚类
findClosest :: (Num a) => 
  FeatureVector a -> 
  [FeatureVector a] -> 
  Cluster a
findClosest centroid data_ =
  let distances = [(point, euclideanDistance centroid point) | point <- data_]
      minDistance = minimum [distance | (_, distance) <- distances]
  in [point | (point, distance) <- distances, distance == minDistance]

-- 计算聚类中心
computeCentroid :: (Num a, Fractional a) => Cluster a -> FeatureVector a
computeCentroid cluster =
  let numFeatures = length (head cluster)
      featureSums = [sum [point !! i | point <- cluster] | i <- [0..numFeatures-1]]
      clusterSize = fromIntegral (length cluster)
  in [sum / clusterSize | sum <- featureSums]

-- 分配数据点到聚类
assignToClusters :: (Num a) => 
  [FeatureVector a] -> 
  [FeatureVector a] -> 
  Clustering a
assignToClusters data_ centroids =
  let assignments = [assignToCluster point centroids | point <- data_]
      clusters = Map.fromListWith (++) [(i, [point]) | (point, i) <- zip data_ assignments]
  in [clusters Map.! i | i <- [0..length centroids-1]]

-- 分配单个点到聚类
assignToCluster :: (Num a) => 
  FeatureVector a -> 
  [FeatureVector a] -> 
  Int
assignToCluster point centroids =
  let distances = [euclideanDistance point centroid | centroid <- centroids]
  in fst $ minimumBy (comparing snd) (zip [0..] distances)

-- 层次聚类
data HierarchicalCluster a = 
  Leaf a |
  Node [HierarchicalCluster a] Double
  deriving (Show)

-- 单链接层次聚类
singleLinkClustering :: (Num a) => 
  [FeatureVector a] -> 
  HierarchicalCluster a
singleLinkClustering data_
  | length data_ == 1 = Leaf (head data_)
  | otherwise =
      let (i, j, distance) = findClosestPair data_
          cluster1 = data_ !! i
          cluster2 = data_ !! j
          remaining = [data_ !! k | k <- [0..length data_-1], k /= i, k /= j]
          mergedCluster = [cluster1, cluster2]
      in Node [singleLinkClustering (mergedCluster ++ remaining)] distance

-- 找到最近的点对
findClosestPair :: (Num a) => [FeatureVector a] -> (Int, Int, Double)
findClosestPair data_ =
  let pairs = [(i, j, euclideanDistance (data_ !! i) (data_ !! j)) 
               | i <- [0..length data_-1], j <- [i+1..length data_-1]]
  in minimumBy (comparing (\(_, _, d) -> d)) pairs
```

## 🔬 高级数据挖掘技术

### 1. 关联规则挖掘

#### 形式化定义

**定义 1.7 (关联规则)** 关联规则是形如 $A \Rightarrow B$ 的表达式，其中 $A, B$ 是项集。

**定义 1.8 (支持度和置信度)** 关联规则 $A \Rightarrow B$ 的：

- 支持度：$support(A \Rightarrow B) = P(A \cup B)$
- 置信度：$confidence(A \Rightarrow B) = P(B|A) = \frac{P(A \cup B)}{P(A)}$

#### Haskell实现

```haskell
module DataMining.AssociationRules where

import DataMining.Core
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (subsequences, nub)

-- 项集
type Itemset a = Set a

-- 关联规则
data AssociationRule a = AssociationRule
  { antecedent :: Itemset a
  , consequent :: Itemset a
  , support :: Double
  , confidence :: Double
  } deriving (Show)

-- 事务数据库
type Transaction a = Itemset a
type TransactionDatabase a = [Transaction a]

-- Apriori算法
apriori :: (Ord a) => 
  Double ->  -- 最小支持度
  TransactionDatabase a -> 
  [Itemset a]
apriori minSupport database =
  let allItems = Set.unions database
      frequent1Itemsets = filter (\item -> 
        support (Set.singleton item) database >= minSupport) (Set.toList allItems)
  in aprioriGen frequent1Itemsets database minSupport

-- Apriori生成
aprioriGen :: (Ord a) => 
  [Itemset a] -> 
  TransactionDatabase a -> 
  Double -> 
  [Itemset a]
aprioriGen candidates database minSupport =
  let frequent = filter (\candidate -> 
        support candidate database >= minSupport) candidates
  in if null frequent
     then []
     else frequent ++ aprioriGen (generateCandidates frequent) database minSupport

-- 生成候选集
generateCandidates :: (Ord a) => [Itemset a] -> [Itemset a]
generateCandidates frequent =
  let k = Set.size (head frequent)
      candidates = [Set.union set1 set2 | 
                   set1 <- frequent, set2 <- frequent,
                   Set.size (Set.intersection set1 set2) == k - 1]
  in nub candidates

-- 计算支持度
support :: (Ord a) => Itemset a -> TransactionDatabase a -> Double
support itemset database =
  let count = length [transaction | transaction <- database, 
                                  itemset `Set.isSubsetOf` transaction]
      total = length database
  in fromIntegral count / fromIntegral total

-- 生成关联规则
generateAssociationRules :: (Ord a) => 
  Double ->  -- 最小置信度
  [Itemset a] -> 
  TransactionDatabase a -> 
  [AssociationRule a]
generateAssociationRules minConfidence frequentItemsets database =
  concat [generateRulesFromItemset itemset database minConfidence 
          | itemset <- frequentItemsets, Set.size itemset > 1]

-- 从项集生成规则
generateRulesFromItemset :: (Ord a) => 
  Itemset a -> 
  TransactionDatabase a -> 
  Double -> 
  [AssociationRule a]
generateRulesFromItemset itemset database minConfidence =
  let subsets = [subset | subset <- Set.toList (powerSet itemset), 
                         not (Set.null subset), subset /= itemset]
      rules = [AssociationRule 
                { antecedent = antecedent
                , consequent = itemset `Set.difference` antecedent
                , support = support itemset database
                , confidence = confidence antecedent (itemset `Set.difference` antecedent) database
                } | antecedent <- subsets]
  in filter (\rule -> rule.confidence >= minConfidence) rules

-- 计算置信度
confidence :: (Ord a) => 
  Itemset a -> 
  Itemset a -> 
  TransactionDatabase a -> 
  Double
confidence antecedent consequent database =
  let antecedentSupport = support antecedent database
      unionSupport = support (antecedent `Set.union` consequent) database
  in if antecedentSupport > 0 then unionSupport / antecedentSupport else 0

-- 幂集
powerSet :: (Ord a) => Set a -> Set (Set a)
powerSet set = Set.fromList [Set.fromList subset | subset <- subsequences (Set.toList set)]
```

### 2. 异常检测

#### 形式化定义

**定义 1.9 (异常)** 异常是数据集中与大多数数据点显著不同的数据点。

**定义 1.10 (局部异常因子)** 局部异常因子定义为：
$$LOF(p) = \frac{\sum_{o \in N_k(p)} \frac{lrd_k(o)}{lrd_k(p)}}{|N_k(p)|}$$

#### Haskell实现

```haskell
module DataMining.AnomalyDetection where

import DataMining.Core
import DataMining.Clustering
import Data.List (sort, minimumBy)
import Data.Ord (comparing)

-- 异常检测结果
data AnomalyScore a = AnomalyScore
  { point :: FeatureVector a
  , score :: Double
  , isAnomaly :: Bool
  } deriving (Show)

-- 基于距离的异常检测
distanceBasedAnomaly :: (Num a) => 
  Double ->  -- 异常阈值
  [FeatureVector a] -> 
  [AnomalyScore a]
distanceBasedAnomaly threshold data_ =
  let scores = [AnomalyScore point (averageDistance point data_) False | point <- data_]
      maxScore = maximum [score | AnomalyScore _ score _ <- scores]
      normalizedScores = [score { score = score.score / maxScore, 
                                 isAnomaly = score.score / maxScore > threshold } | score <- scores]
  in normalizedScores

-- 计算平均距离
averageDistance :: (Num a) => FeatureVector a -> [FeatureVector a] -> Double
averageDistance point data_ =
  let distances = [euclideanDistance point other | other <- data_, other /= point]
  in sum distances / fromIntegral (length distances)

-- 局部异常因子
localOutlierFactor :: (Num a) => 
  Int ->  -- k值
  Double ->  -- 异常阈值
  [FeatureVector a] -> 
  [AnomalyScore a]
localOutlierFactor k threshold data_ =
  let lofScores = [computeLOF point k data_ | point <- data_]
      maxLOF = maximum lofScores
      normalizedScores = [AnomalyScore point (score / maxLOF) (score / maxLOF > threshold) 
                         | (point, score) <- zip data_ lofScores]
  in normalizedScores

-- 计算LOF
computeLOF :: (Num a) => FeatureVector a -> Int -> [FeatureVector a] -> Double
computeLOF point k data_ =
  let neighbors = kNearestNeighbors point k data_
      lrdPoint = localReachabilityDensity point k data_
      neighborLRDs = [localReachabilityDensity neighbor k data_ | neighbor <- neighbors]
  in sum neighborLRDs / (lrdPoint * fromIntegral k)

-- k近邻
kNearestNeighbors :: (Num a) => FeatureVector a -> Int -> [FeatureVector a] -> [FeatureVector a]
kNearestNeighbors point k data_ =
  let distances = [(other, euclideanDistance point other) | other <- data_, other /= point]
      sorted = sort [(other, distance) | (other, distance) <- distances]
  in [other | (other, _) <- take k sorted]

-- 局部可达密度
localReachabilityDensity :: (Num a) => FeatureVector a -> Int -> [FeatureVector a] -> Double
localReachabilityDensity point k data_ =
  let neighbors = kNearestNeighbors point k data_
      reachabilityDistances = [reachabilityDistance point neighbor data_ | neighbor <- neighbors]
  in fromIntegral k / sum reachabilityDistances

-- 可达距离
reachabilityDistance :: (Num a) => 
  FeatureVector a -> 
  FeatureVector a -> 
  [FeatureVector a] -> 
  Double
reachabilityDistance point1 point2 data_ =
  let kDistance = kDistance point2 data_
      directDistance = euclideanDistance point1 point2
  in max kDistance directDistance

-- k距离
kDistance :: (Num a) => FeatureVector a -> [FeatureVector a] -> Double
kDistance point data_ =
  let distances = [euclideanDistance point other | other <- data_, other /= point]
      sorted = sort distances
  in sorted !! (min 4 (length sorted - 1))  -- 使用k=5
```

## 📊 评估指标

### 1. 分类评估

```haskell
module DataMining.Evaluation where

import DataMining.Classification
import Data.List (zipWith)

-- 混淆矩阵
data ConfusionMatrix = ConfusionMatrix
  { truePositives :: Int
  , falsePositives :: Int
  , trueNegatives :: Int
  , falseNegatives :: Int
  } deriving (Show)

-- 计算混淆矩阵
confusionMatrix :: (Eq b) => [b] -> [b] -> ConfusionMatrix
confusionMatrix actual predicted =
  let pairs = zip actual predicted
      tp = length [() | (a, p) <- pairs, a == p, a == True]  -- 假设True为正类
      fp = length [() | (a, p) <- pairs, a /= p, p == True]
      tn = length [() | (a, p) <- pairs, a == p, a == False]
      fn = length [() | (a, p) <- pairs, a /= p, p == False]
  in ConfusionMatrix tp fp tn fn

-- 准确率
accuracy :: ConfusionMatrix -> Double
accuracy (ConfusionMatrix tp fp tn fn) =
  fromIntegral (tp + tn) / fromIntegral (tp + fp + tn + fn)

-- 精确率
precision :: ConfusionMatrix -> Double
precision (ConfusionMatrix tp fp _ _) =
  fromIntegral tp / fromIntegral (tp + fp)

-- 召回率
recall :: ConfusionMatrix -> Double
recall (ConfusionMatrix tp _ _ fn) =
  fromIntegral tp / fromIntegral (tp + fn)

-- F1分数
f1Score :: ConfusionMatrix -> Double
f1Score matrix =
  let p = precision matrix
      r = recall matrix
  in 2 * p * r / (p + r)

-- 聚类评估：轮廓系数
silhouetteCoefficient :: (Num a) => 
  [FeatureVector a] -> 
  Clustering a -> 
  Double
silhouetteCoefficient data_ clustering =
  let coefficients = [silhouetteForPoint point clustering | point <- data_]
  in sum coefficients / fromIntegral (length coefficients)

-- 单个点的轮廓系数
silhouetteForPoint :: (Num a) => 
  FeatureVector a -> 
  Clustering a -> 
  Double
silhouetteForPoint point clustering =
  let cluster = findCluster point clustering
      a = averageDistance point cluster
      b = minimum [averageDistance point otherCluster | otherCluster <- clustering, 
                                                       otherCluster /= cluster]
  in (b - a) / max a b

-- 找到点所属的聚类
findCluster :: (Eq a) => FeatureVector a -> Clustering a -> Cluster a
findCluster point clustering =
  head [cluster | cluster <- clustering, point `elem` cluster]

-- 平均距离
averageDistance :: (Num a) => FeatureVector a -> Cluster a -> Double
averageDistance point cluster =
  let distances = [euclideanDistance point other | other <- cluster, other /= point]
  in if null distances then 0 else sum distances / fromIntegral (length distances)
```

## 📚 形式化证明

### 定理 1.1: K-means收敛性

**定理** K-means算法在有限步内收敛到局部最优解。

**证明**：

1. 目标函数 $J$ 在每次迭代后单调递减
2. $J$ 有下界（非负）
3. 由单调收敛定理，算法收敛
4. 收敛点满足局部最优条件

### 定理 1.2: Apriori算法的正确性

**定理** Apriori算法能够找到所有频繁项集。

**证明**：

1. 反单调性：频繁项集的子集也是频繁的
2. 候选生成：所有频繁k项集都包含在候选k项集中
3. 剪枝：非频繁项集被正确剪枝
4. 归纳：通过数学归纳法证明所有频繁项集都被找到

## 🔗 相关链接

- [统计分析](./01-Statistical-Analysis.md)
- [数据可视化](./03-Data-Visualization.md)
- [机器学习](../03-Artificial-Intelligence/01-Machine-Learning.md)
- [大数据技术](./04-Big-Data-Technology.md)

---

*本文档建立了数据挖掘的完整形式化理论体系，包含严格的数学定义、Haskell实现和形式化证明。*
