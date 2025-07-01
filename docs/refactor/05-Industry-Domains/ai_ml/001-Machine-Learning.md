# 机器学习应用

## 概述

本文档介绍函数式编程在机器学习领域的应用，包括算法实现、数据处理和模型训练。

## 函数式机器学习基础

### 1. 纯函数式数据处理

#### 数据管道

```haskell
-- 数据管道类型
newtype DataPipeline a b = DataPipeline 
  { runPipeline :: a -> Either PipelineError b }

-- 管道组合
instance Category DataPipeline where
  id = DataPipeline Right
  DataPipeline f . DataPipeline g = DataPipeline (f <=< g)

-- 数据处理步骤
data ProcessingStep a b = 
  Transform (a -> b)
  | Filter (a -> Bool)
  | Aggregate ([a] -> b)

-- 构建数据管道
buildPipeline :: [ProcessingStep a b] -> DataPipeline a b
buildPipeline steps = DataPipeline $ \input -> 
  foldM processStep input steps
  where
    processStep acc (Transform f) = Right (f acc)
    processStep acc (Filter p) = if p acc then Right acc else Left FilteredOut
    processStep acc (Aggregate f) = Right (f [acc])
```

#### 惰性数据处理

```haskell
-- 惰性数据流
data DataStream a = DataStream
  { head :: a
  , tail :: DataStream a
  }

-- 流处理
mapStream :: (a -> b) -> DataStream a -> DataStream b
mapStream f (DataStream x xs) = DataStream (f x) (mapStream f xs)

filterStream :: (a -> Bool) -> DataStream a -> DataStream a
filterStream p (DataStream x xs) = 
  if p x 
  then DataStream x (filterStream p xs)
  else filterStream p xs

-- 无限数据流
infiniteStream :: a -> DataStream a
infiniteStream x = DataStream x (infiniteStream x)
```

### 2. 类型安全的机器学习

#### 特征向量

```haskell
-- 特征向量类型
newtype FeatureVector = FeatureVector { unFeatureVector :: Vector Double }

-- 特征类型
data FeatureType = 
  Numerical Double
  | Categorical String
  | Binary Bool

-- 特征提取
class FeatureExtractor a where
  extractFeatures :: a -> FeatureVector
  featureNames :: [String]

-- 示例：文本特征提取
instance FeatureExtractor String where
  extractFeatures text = FeatureVector $ 
    V.fromList [wordCount, charCount, avgWordLength]
    where
      wordCount = fromIntegral $ length $ words text
      charCount = fromIntegral $ length text
      avgWordLength = charCount / max 1 wordCount
  
  featureNames = ["word_count", "char_count", "avg_word_length"]
```

#### 标签类型

```haskell
-- 分类标签
newtype ClassificationLabel = ClassificationLabel { unLabel :: Int }

-- 回归标签
newtype RegressionLabel = RegressionLabel { unValue :: Double }

-- 多标签
newtype MultiLabel = MultiLabel { unLabels :: Set Int }

-- 标签编码器
class LabelEncoder a where
  encode :: a -> Int
  decode :: Int -> a
  numClasses :: Int
```

## 机器学习算法

### 1. 线性回归

#### 模型定义

```haskell
-- 线性回归模型
data LinearRegression = LinearRegression
  { weights :: Vector Double
  , bias :: Double
  }

-- 模型参数
data ModelParams = ModelParams
  { learningRate :: Double
  , numIterations :: Int
  , regularization :: Double
  }

-- 训练数据
data TrainingData = TrainingData
  { features :: Matrix Double
  , labels :: Vector Double
  }
```

#### 模型训练

```haskell
-- 损失函数
mseLoss :: Vector Double -> Vector Double -> Double
mseLoss predictions targets = 
  V.sum (V.zipWith (\p t -> (p - t) ^ 2) predictions targets) / 
  fromIntegral (V.length predictions)

-- 梯度计算
computeGradients :: Matrix Double -> Vector Double -> Vector Double -> 
                   (Vector Double, Double)
computeGradients X y predictions = 
  let errors = V.zipWith (-) predictions y
      n = fromIntegral $ V.length y
      gradWeights = (1/n) * (X `multiplyVector` errors)
      gradBias = (1/n) * V.sum errors
  in (gradWeights, gradBias)

-- 模型训练
trainLinearRegression :: ModelParams -> TrainingData -> LinearRegression
trainLinearRegression params data = 
  let initialModel = LinearRegression (V.replicate (numFeatures data) 0) 0
  in foldl' (updateModel params data) initialModel [1..numIterations params]
  where
    numFeatures = V.length . head . toRows . features

updateModel :: ModelParams -> TrainingData -> LinearRegression -> Int -> LinearRegression
updateModel params data model _ = 
  let predictions = predict model (features data)
      (gradWeights, gradBias) = computeGradients (features data) (labels data) predictions
      newWeights = V.zipWith (\w g -> w - learningRate params * g) (weights model) gradWeights
      newBias = bias model - learningRate params * gradBias
  in LinearRegression newWeights newBias
```

#### 模型预测

```haskell
-- 预测函数
predict :: LinearRegression -> Matrix Double -> Vector Double
predict model X = 
  V.map (+ bias model) (X `multiplyVector` weights model)

-- 模型评估
evaluateModel :: LinearRegression -> TrainingData -> Double
evaluateModel model data = 
  let predictions = predict model (features data)
  in mseLoss predictions (labels data)
```

### 2. 逻辑回归

#### 模型定义1

```haskell
-- 逻辑回归模型
data LogisticRegression = LogisticRegression
  { weights :: Vector Double
  , bias :: Double
  }

-- 激活函数
sigmoid :: Double -> Double
sigmoid x = 1 / (1 + exp (-x))

-- 预测概率
predictProb :: LogisticRegression -> Vector Double -> Vector Double
predictProb model features = 
  V.map sigmoid (V.map (+ bias model) (V.zipWith (*) features (weights model)))
```

#### 训练算法

```haskell
-- 交叉熵损失
crossEntropyLoss :: Vector Double -> Vector Double -> Double
crossEntropyLoss predictions targets = 
  -V.sum (V.zipWith (\p t -> t * log p + (1-t) * log (1-p)) predictions targets)

-- 逻辑回归训练
trainLogisticRegression :: ModelParams -> TrainingData -> LogisticRegression
trainLogisticRegression params data = 
  let initialModel = LogisticRegression (V.replicate (numFeatures data) 0) 0
  in foldl' (updateLogisticModel params data) initialModel [1..numIterations params]
```

### 3. 决策树

#### 树结构

```haskell
-- 决策树节点
data DecisionTree a = 
  Leaf a
  | Node 
    { featureIndex :: Int
    , threshold :: Double
    , leftChild :: DecisionTree a
    , rightChild :: DecisionTree a
    }

-- 分裂标准
data SplitCriterion = 
  Gini
  | Entropy
  | Variance

-- 分裂信息
data SplitInfo = SplitInfo
  { featureIndex :: Int
  , threshold :: Double
  , impurity :: Double
  , leftIndices :: [Int]
  , rightIndices :: [Int]
  }
```

#### 树构建

```haskell
-- 计算不纯度
calculateImpurity :: SplitCriterion -> [Double] -> Double
calculateImpurity Gini values = 
  let counts = Map.fromListWith (+) [(v, 1) | v <- values]
      total = fromIntegral $ length values
      probabilities = map (/ total) (Map.elems counts)
  in 1 - sum (map (^2) probabilities)

calculateImpurity Entropy values = 
  let counts = Map.fromListWith (+) [(v, 1) | v <- values]
      total = fromIntegral $ length values
      probabilities = map (/ total) (Map.elems counts)
  in -sum (map (\p -> p * log p) (filter (>0) probabilities))

-- 寻找最佳分裂
findBestSplit :: Matrix Double -> Vector Double -> SplitCriterion -> SplitInfo
findBestSplit X y criterion = 
  let numFeatures = V.length (head (toRows X))
      splits = concatMap (\f -> findSplitsForFeature X y f criterion) [0..numFeatures-1]
  in minimumBy (comparing impurity) splits
```

### 4. 随机森林

#### 集成学习

```haskell
-- 随机森林
data RandomForest = RandomForest
  { trees :: [DecisionTree Double]
  , numTrees :: Int
  , maxDepth :: Int
  }

-- 训练随机森林
trainRandomForest :: ModelParams -> TrainingData -> RandomForest
trainRandomForest params data = 
  let trees = map (\_ -> trainSingleTree params data) [1..numTrees params]
  in RandomForest trees (numTrees params) (maxDepth params)

-- 预测
predictForest :: RandomForest -> Vector Double -> Double
predictForest forest features = 
  let predictions = map (\tree -> predictTree tree features) (trees forest)
  in sum predictions / fromIntegral (length predictions)
```

## 深度学习

### 1. 神经网络

#### 网络结构

```haskell
-- 神经网络层
data NeuralLayer = NeuralLayer
  { weights :: Matrix Double
  , bias :: Vector Double
  , activation :: ActivationFunction
  }

data ActivationFunction = 
  ReLU
  | Sigmoid
  | Tanh
  | Softmax

-- 神经网络
data NeuralNetwork = NeuralNetwork
  { layers :: [NeuralLayer]
  , inputSize :: Int
  , outputSize :: Int
  }
```

#### 前向传播

```haskell
-- 激活函数
applyActivation :: ActivationFunction -> Vector Double -> Vector Double
applyActivation ReLU = V.map (max 0)
applyActivation Sigmoid = V.map sigmoid
applyActivation Tanh = V.map tanh
applyActivation Softmax v = 
  let maxVal = V.maximum v
      expVals = V.map (\x -> exp (x - maxVal)) v
      sumExp = V.sum expVals
  in V.map (/ sumExp) expVals

-- 前向传播
forwardPass :: NeuralNetwork -> Vector Double -> Vector Double
forwardPass network input = 
  foldl' (\acc layer -> 
    let linearOutput = (weights layer) `multiplyVector` acc + bias layer
    in applyActivation (activation layer) linearOutput
  ) input (layers network)
```

### 2. 反向传播

#### 梯度计算

```haskell
-- 损失函数梯度
computeLossGradient :: LossFunction -> Vector Double -> Vector Double -> Vector Double
computeLossGradient MSE predictions targets = 
  V.zipWith (\p t -> 2 * (p - t)) predictions targets

-- 反向传播
backwardPass :: NeuralNetwork -> Vector Double -> Vector Double -> 
                Vector Double -> [NeuralLayer]
backwardPass network input target output = 
  let gradients = reverse $ computeLayerGradients network input target output
  in zipWith updateLayer (layers network) gradients
```

## 数据处理

### 1. 数据预处理

#### 标准化

```haskell
-- 标准化
standardize :: Vector Double -> Vector Double
standardize v = 
  let mean = V.sum v / fromIntegral (V.length v)
      variance = V.sum (V.map (\x -> (x - mean) ^ 2) v) / fromIntegral (V.length v)
      std = sqrt variance
  in V.map (\x -> (x - mean) / std) v

-- 归一化
normalize :: Vector Double -> Vector Double
normalize v = 
  let minVal = V.minimum v
      maxVal = V.maximum v
      range = maxVal - minVal
  in V.map (\x -> (x - minVal) / range) v
```

#### 特征选择

```haskell
-- 特征重要性
data FeatureImportance = FeatureImportance
  { featureIndex :: Int
  , importance :: Double
  }

-- 基于方差的选择
selectByVariance :: Matrix Double -> Double -> [Int]
selectByVariance X threshold = 
  let variances = map (\col -> variance col) (toColumns X)
      importantFeatures = zipWith (\i v -> (i, v)) [0..] variances
  in map fst $ filter (\ (_, v) -> v > threshold) importantFeatures
```

### 2. 数据验证

#### 数据质量检查

```haskell
-- 数据质量报告
data DataQualityReport = DataQualityReport
  { missingValues :: Map Int Int
  , outliers :: Map Int [Int]
  , dataTypes :: Map Int DataType
  , statistics :: Map Int Statistics
  }

-- 数据验证
validateData :: Matrix Double -> DataQualityReport
validateData X = DataQualityReport
  { missingValues = findMissingValues X
  , outliers = findOutliers X
  , dataTypes = inferDataTypes X
  , statistics = computeStatistics X
  }
```

## 模型评估

### 1. 分类指标

#### 评估指标

```haskell
-- 混淆矩阵
data ConfusionMatrix = ConfusionMatrix
  { truePositives :: Int
  , trueNegatives :: Int
  , falsePositives :: Int
  , falseNegatives :: Int
  }

-- 计算指标
accuracy :: ConfusionMatrix -> Double
accuracy cm = 
  fromIntegral (truePositives cm + trueNegatives cm) / 
  fromIntegral (total cm)
  where total cm = truePositives cm + trueNegatives cm + 
                   falsePositives cm + falseNegatives cm

precision :: ConfusionMatrix -> Double
precision cm = 
  fromIntegral (truePositives cm) / 
  fromIntegral (truePositives cm + falsePositives cm)

recall :: ConfusionMatrix -> Double
recall cm = 
  fromIntegral (truePositives cm) / 
  fromIntegral (truePositives cm + falseNegatives cm)

f1Score :: ConfusionMatrix -> Double
f1Score cm = 
  2 * precision cm * recall cm / (precision cm + recall cm)
```

### 2. 回归指标

#### 回归评估

```haskell
-- 回归指标
data RegressionMetrics = RegressionMetrics
  { mse :: Double
  , rmse :: Double
  , mae :: Double
  , r2 :: Double
  }

-- 计算回归指标
computeRegressionMetrics :: Vector Double -> Vector Double -> RegressionMetrics
computeRegressionMetrics predictions targets = 
  let mse = mseLoss predictions targets
      rmse = sqrt mse
      mae = V.sum (V.map abs (V.zipWith (-) predictions targets)) / 
            fromIntegral (V.length predictions)
      r2 = computeR2 predictions targets
  in RegressionMetrics mse rmse mae r2
```

## 实际应用

### 1. 推荐系统

#### 协同过滤

```haskell
-- 用户-物品矩阵
type UserItemMatrix = Matrix Double

-- 相似度计算
cosineSimilarity :: Vector Double -> Vector Double -> Double
cosineSimilarity v1 v2 = 
  let dotProduct = V.sum (V.zipWith (*) v1 v2)
      norm1 = sqrt (V.sum (V.map (^2) v1))
      norm2 = sqrt (V.sum (V.map (^2) v2))
  in dotProduct / (norm1 * norm2)

-- 推荐算法
recommendItems :: UserItemMatrix -> Int -> Int -> [Int]
recommendItems matrix userId numRecommendations = 
  let userRatings = getRow matrix userId
      similarUsers = findSimilarUsers matrix userId
      recommendations = generateRecommendations matrix userRatings similarUsers
  in take numRecommendations recommendations
```

### 2. 自然语言处理

#### 文本分类

```haskell
-- 文本特征
data TextFeatures = TextFeatures
  { tfidf :: Map String Double
  , wordCount :: Int
  , avgWordLength :: Double
  }

-- TF-IDF计算
computeTFIDF :: [String] -> Map String Double
computeTFIDF documents = 
  let termFreq = computeTermFrequency documents
      inverseDocFreq = computeInverseDocumentFrequency documents
  in Map.intersectionWith (*) termFreq inverseDocFreq
```

---

**相关链接**：

- [算法实现](../07-Implementation/004-Algorithms.md)
- [性能优化](../07-Implementation/006-Performance-Optimization.md)
- [系统架构](../06-Architecture/001-System-Architecture.md)
