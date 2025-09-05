# 001-机器学习基础

## 1. 概述

### 1.1 定义与目标

机器学习是人工智能的一个分支，通过算法使计算机能够从数据中学习模式，主要目标：

- **监督学习**: 从标记数据中学习映射关系
- **无监督学习**: 发现数据中的隐藏模式
- **强化学习**: 通过与环境交互学习最优策略

### 1.2 形式化定义

**学习问题**: 给定输入空间 $\mathcal{X}$ 和输出空间 $\mathcal{Y}$，学习一个函数 $f: \mathcal{X} \rightarrow \mathcal{Y}$。

**经验风险最小化**:
$$\hat{f} = \arg\min_{f \in \mathcal{F}} \frac{1}{n} \sum_{i=1}^{n} L(f(x_i), y_i)$$
其中 $L$ 是损失函数，$\mathcal{F}$ 是假设空间。

## 2. 监督学习

### 2.1 线性回归

**模型**: $f(x) = w^T x + b$

**损失函数**: 均方误差
$$L(w, b) = \frac{1}{n} \sum_{i=1}^{n} (y_i - (w^T x_i + b))^2$$

**梯度下降更新**:
$$w_{t+1} = w_t - \alpha \nabla_w L(w_t, b_t)$$
$$b_{t+1} = b_t - \alpha \nabla_b L(w_t, b_t)$$

### 2.2 逻辑回归

**模型**: $f(x) = \sigma(w^T x + b)$，其中 $\sigma(z) = \frac{1}{1 + e^{-z}}$

**损失函数**: 交叉熵损失
$$L(w, b) = -\frac{1}{n} \sum_{i=1}^{n} [y_i \log(f(x_i)) + (1-y_i) \log(1-f(x_i))]$$

### 2.3 支持向量机

**目标函数**:
$$\min_{w,b} \frac{1}{2} \|w\|^2 + C \sum_{i=1}^{n} \xi_i$$
约束条件: $y_i(w^T x_i + b) \geq 1 - \xi_i, \xi_i \geq 0$

## 3. 无监督学习

### 3.1 K-means聚类

**目标**: 最小化簇内平方误差
$$J = \sum_{i=1}^{k} \sum_{x \in C_i} \|x - \mu_i\|^2$$

**算法步骤**:

1. 随机初始化 $k$ 个聚类中心
2. 将每个点分配到最近的聚类中心
3. 更新聚类中心: $\mu_i = \frac{1}{|C_i|} \sum_{x \in C_i} x$
4. 重复步骤2-3直到收敛

### 3.2 主成分分析（PCA）

**目标**: 找到数据的主要方向，最大化方差
$$\max_{w} w^T \Sigma w \quad \text{s.t.} \quad \|w\| = 1$$

其中 $\Sigma = \frac{1}{n} \sum_{i=1}^{n} (x_i - \bar{x})(x_i - \bar{x})^T$ 是协方差矩阵。

## 4. Haskell实现示例

### 4.1 机器学习类型系统

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Matrix (Matrix)
import qualified Data.Matrix as M

-- 机器学习数据类型
class MLData a where
    type FeatureType a :: *
    type LabelType a :: *
    
    -- 获取特征维度
    featureDimension :: a -> Int
    
    -- 获取样本数量
    sampleCount :: a -> Int
    
    -- 获取特征矩阵
    featureMatrix :: a -> Matrix (FeatureType a)
    
    -- 获取标签向量
    labelVector :: a -> Vector (LabelType a)

-- 数据集
data Dataset a b = Dataset {
    features :: Matrix a,
    labels :: Vector b,
    featureNames :: [String]
}

instance (Num a, Show a, Show b) => MLData (Dataset a b) where
    type FeatureType (Dataset a b) = a
    type LabelType (Dataset a b) = b
    
    featureDimension = M.ncols . features
    sampleCount = M.nrows . features
    featureMatrix = features
    labelVector = labels

-- 模型类型类
class MLModel m where
    type ModelInput m :: *
    type ModelOutput m :: *
    
    -- 训练模型
    train :: MLData d => d -> m -> m
    
    -- 预测
    predict :: m -> ModelInput m -> ModelOutput m
    
    -- 评估模型
    evaluate :: MLData d => d -> m -> Double
```

### 4.2 线性回归实现

```haskell
-- 线性回归模型
data LinearRegression = LinearRegression {
    weights :: Vector Double,
    bias :: Double,
    learningRate :: Double,
    maxIterations :: Int
}

instance MLModel LinearRegression where
    type ModelInput LinearRegression = Vector Double
    type ModelOutput LinearRegression = Double
    
    train dataset model = 
        let iterations = take (maxIterations model) $ iterate (updateModel dataset) model
        in last iterations
    
    predict model input = 
        V.sum (V.zipWith (*) (weights model) input) + bias model
    
    evaluate dataset model = 
        let predictions = V.map (predict model) (featureRows dataset)
            actuals = labelVector dataset
            mse = V.sum (V.zipWith (\pred actual -> (pred - actual)^2) predictions actuals) / fromIntegral (V.length actuals)
        in mse

-- 特征行提取
featureRows :: MLData d => d -> Vector (Vector Double)
featureRows dataset = V.fromList $ map (\i -> V.fromList $ M.getRow i (featureMatrix dataset)) [1..sampleCount dataset]

-- 模型更新
updateModel :: MLData d => d -> LinearRegression -> LinearRegression
updateModel dataset model = 
    let gradients = computeGradients dataset model
        newWeights = V.zipWith (\w g -> w - learningRate model * g) (weights model) (fst gradients)
        newBias = bias model - learningRate model * snd gradients
    in model { weights = newWeights, bias = newBias }

-- 梯度计算
computeGradients :: MLData d => d -> LinearRegression -> (Vector Double, Double)
computeGradients dataset model = 
    let samples = featureRows dataset
        labels = labelVector dataset
        predictions = V.map (predict model) samples
        errors = V.zipWith (-) labels predictions
        
        -- 权重梯度
        weightGradients = V.map (\i -> 
            V.sum (V.zipWith (*) errors (V.map (V.! (i-1)) samples)) / fromIntegral (V.length samples)
        ) (V.enumFromTo 1 (featureDimension dataset))
        
        -- 偏置梯度
        biasGradient = V.sum errors / fromIntegral (V.length errors)
    in (weightGradients, biasGradient)
```

### 4.3 K-means聚类实现

```haskell
-- K-means模型
data KMeans = KMeans {
    centroids :: Matrix Double,
    k :: Int,
    maxIterations :: Int,
    tolerance :: Double
}

-- 聚类结果
data ClusteringResult = ClusteringResult {
    clusterAssignments :: Vector Int,
    finalCentroids :: Matrix Double,
    iterations :: Int,
    converged :: Bool
}

-- K-means算法
kmeans :: Dataset Double Double -> KMeans -> ClusteringResult
kmeans dataset model = 
    let initialCentroids = initializeCentroids dataset (k model)
        iterations = take (maxIterations model) $ iterate (kmeansStep dataset) (model { centroids = initialCentroids })
        converged = checkConvergence iterations (tolerance model)
        finalModel = last iterations
        assignments = assignToClusters dataset finalModel
    in ClusteringResult {
        clusterAssignments = assignments,
        finalCentroids = centroids finalModel,
        iterations = length iterations,
        converged = converged
    }

-- 初始化聚类中心
initializeCentroids :: Dataset Double Double -> Int -> Matrix Double
initializeCentroids dataset k = 
    let features = featureMatrix dataset
        n = M.nrows features
        indices = take k $ randomRs (1, n) (mkStdGen 42)
        centroids = M.fromLists $ map (\i -> M.getRow i features) indices
    in centroids

-- K-means单步
kmeansStep :: Dataset Double Double -> KMeans -> KMeans
kmeansStep dataset model = 
    let assignments = assignToClusters dataset model
        newCentroids = updateCentroids dataset assignments (k model)
    in model { centroids = newCentroids }

-- 分配点到聚类
assignToClusters :: Dataset Double Double -> KMeans -> Vector Int
assignToClusters dataset model = 
    let samples = featureRows dataset
        centroids = V.fromList $ map (\i -> V.fromList $ M.getRow i (centroids model)) [1..k model]
    in V.map (\sample -> 
        let distances = V.map (\centroid -> euclideanDistance sample centroid) centroids
            minIndex = V.minIndex distances
        in minIndex + 1
    ) samples

-- 欧几里得距离
euclideanDistance :: Vector Double -> Vector Double -> Double
euclideanDistance v1 v2 = sqrt $ V.sum $ V.map (\i -> (v1 V.! i - v2 V.! i)^2) (V.enumFromTo 0 (V.length v1 - 1))

-- 更新聚类中心
updateCentroids :: Dataset Double Double -> Vector Int -> Int -> Matrix Double
updateCentroids dataset assignments k = 
    let samples = featureRows dataset
        newCentroids = map (\clusterId -> 
            let clusterSamples = V.filter (\i -> assignments V.! (i-1) == clusterId) (V.enumFromTo 1 (V.length samples))
                clusterVectors = V.map (\i -> samples V.! (i-1)) clusterSamples
            in if V.null clusterVectors 
               then V.replicate (featureDimension dataset) 0
               else V.map (\j -> V.sum (V.map (V.! j) clusterVectors) / fromIntegral (V.length clusterVectors)) (V.enumFromTo 0 (featureDimension dataset - 1))
        ) [1..k]
    in M.fromLists newCentroids

-- 检查收敛
checkConvergence :: [KMeans] -> Double -> Bool
checkConvergence [] _ = True
checkConvergence [_] _ = True
checkConvergence (m1:m2:ms) tolerance = 
    let diff = M.norm_Inf (centroids m1 - centroids m2)
    in if diff < tolerance then True else checkConvergence (m2:ms) tolerance
```

### 4.4 主成分分析实现

```haskell
-- PCA模型
data PCA = PCA {
    components :: Matrix Double,
    explainedVariance :: Vector Double,
    nComponents :: Int
}

-- PCA算法
pca :: Dataset Double Double -> Int -> PCA
pca dataset nComponents = 
    let features = featureMatrix dataset
        centered = centerData features
        covariance = computeCovariance centered
        (eigenvalues, eigenvectors) = eigendecomposition covariance
        topComponents = take nComponents $ zip eigenvalues eigenvectors
        components = M.fromLists $ map snd topComponents
        explainedVar = V.fromList $ map fst topComponents
    in PCA {
        components = components,
        explainedVariance = explainedVar,
        nComponents = nComponents
    }

-- 数据标准化
centerData :: Matrix Double -> Matrix Double
centerData data = 
    let means = V.fromList $ map (\j -> V.sum (M.getCol j data) / fromIntegral (M.nrows data)) [1..M.ncols data]
        centered = M.fromLists $ map (\i -> 
            map (\j -> (M.getElem i j data) - (means V.! (j-1))) [1..M.ncols data]
        ) [1..M.nrows data]
    in centered

-- 计算协方差矩阵
computeCovariance :: Matrix Double -> Matrix Double
computeCovariance data = 
    let n = M.nrows data
        covariance = M.multStd (M.transpose data) data
    in M.scale (1.0 / fromIntegral (n-1)) covariance

-- 特征值分解（简化实现）
eigendecomposition :: Matrix Double -> [(Double, [Double])]
eigendecomposition matrix = 
    -- 这里使用简化的幂迭代方法
    let n = M.nrows matrix
        initialVector = V.replicate n 1.0
        iterations = 20
        eigenvalues = take n $ iterate (\v -> normalize $ M.multStd matrix v) initialVector
    in zip (map (\v -> V.sum (V.zipWith (*) v (M.multStd matrix v))) eigenvalues) (map V.toList eigenvalues)

-- 向量归一化
normalize :: Vector Double -> Vector Double
normalize v = 
    let norm = sqrt $ V.sum $ V.map (^2) v
    in V.map (/ norm) v

-- 数据转换
transform :: PCA -> Matrix Double -> Matrix Double
transform pca data = M.multStd data (M.transpose (components pca))
```

### 4.5 模型评估工具

```haskell
-- 评估指标
class EvaluationMetric a where
    -- 计算指标
    computeMetric :: Vector Double -> Vector Double -> a
    
    -- 指标名称
    metricName :: String

-- 均方误差
newtype MSE = MSE Double deriving (Show)

instance EvaluationMetric MSE where
    computeMetric predictions actuals = 
        let errors = V.zipWith (-) actuals predictions
            squaredErrors = V.map (^2) errors
            mse = V.sum squaredErrors / fromIntegral (V.length squaredErrors)
        in MSE mse
    
    metricName = "Mean Squared Error"

-- 准确率
newtype Accuracy = Accuracy Double deriving (Show)

instance EvaluationMetric Accuracy where
    computeMetric predictions actuals = 
        let correct = V.sum $ V.zipWith (\pred actual -> if round pred == round actual then 1 else 0) predictions actuals
            total = V.length predictions
        in Accuracy (fromIntegral correct / fromIntegral total)
    
    metricName = "Accuracy"

-- 交叉验证
crossValidation :: MLData d => d -> (d -> m -> m) -> m -> Int -> [Double]
crossValidation dataset trainFunc model k = 
    let folds = createFolds dataset k
        foldResults = map (\fold -> 
            let trainData = combineFolds (filter (/= fold) folds)
                testData = fold
                trainedModel = trainFunc trainData model
                score = evaluate testData trainedModel
            in score
        ) folds
    in foldResults

-- 创建交叉验证折
createFolds :: MLData d => d -> Int -> [d]
createFolds dataset k = 
    let n = sampleCount dataset
        foldSize = n `div` k
        indices = [1..n]
        foldIndices = chunksOf foldSize indices
    in map (\foldIdx -> createSubset dataset foldIdx) foldIndices

-- 创建数据子集
createSubset :: MLData d => d -> [Int] -> d
createSubset dataset indices = 
    let features = featureMatrix dataset
        labels = labelVector dataset
        subsetFeatures = M.fromLists $ map (\i -> M.getRow i features) indices
        subsetLabels = V.fromList $ map (\i -> labels V.! (i-1)) indices
    in Dataset {
        features = subsetFeatures,
        labels = subsetLabels,
        featureNames = featureNames dataset
    }

-- 合并数据折
combineFolds :: MLData d => [d] -> d
combineFolds [] = error "Empty fold list"
combineFolds [fold] = fold
combineFolds (fold:folds) = 
    let combined = combineFolds folds
        allFeatures = M.vertJoin (featureMatrix fold) (featureMatrix combined)
        allLabels = V.concat [labelVector fold, labelVector combined]
    in Dataset {
        features = allFeatures,
        labels = allLabels,
        featureNames = featureNames fold
    }
```

## 5. 高级机器学习技术

### 5.1 正则化

**L1正则化（Lasso）**:
$$L_{lasso}(w) = L(w) + \lambda \sum_{i=1}^{d} |w_i|$$

**L2正则化（Ridge）**:
$$L_{ridge}(w) = L(w) + \lambda \sum_{i=1}^{d} w_i^2$$

### 5.2 集成学习

**Bagging**: 通过重采样创建多个模型并平均预测结果。

**Boosting**: 顺序训练模型，每个模型关注前一个模型的错误。

**随机森林**: 结合决策树的Bagging方法。

### 5.3 深度学习基础

**前馈神经网络**:
$$h^{(l+1)} = \sigma(W^{(l)} h^{(l)} + b^{(l)})$$

**反向传播**:
$$\frac{\partial L}{\partial W^{(l)}} = \frac{\partial L}{\partial h^{(l+1)}} \cdot \frac{\partial h^{(l+1)}}{\partial W^{(l)}}$$

## 6. 实际应用

### 6.1 特征工程

```haskell
-- 特征工程类型类
class FeatureEngineering a where
    -- 特征缩放
    scaleFeatures :: a -> a
    
    -- 特征选择
    selectFeatures :: a -> [Int] -> a
    
    -- 特征变换
    transformFeatures :: a -> (Vector Double -> Vector Double) -> a

-- 标准化
standardize :: Vector Double -> Vector Double
standardize v = 
    let mean = V.sum v / fromIntegral (V.length v)
        variance = V.sum (V.map (\x -> (x - mean)^2) v) / fromIntegral (V.length v)
        std = sqrt variance
    in V.map (\x -> (x - mean) / std) v

-- 归一化
normalizeFeatures :: Vector Double -> Vector Double
normalizeFeatures v = 
    let minVal = V.minimum v
        maxVal = V.maximum v
        range = maxVal - minVal
    in V.map (\x -> (x - minVal) / range) v
```

### 6.2 模型选择

```haskell
-- 模型选择器
data ModelSelector = ModelSelector {
    models :: [String],
    hyperparameters :: Map String [Double],
    evaluationMetric :: String,
    crossValidationFolds :: Int
}

-- 网格搜索
gridSearch :: MLData d => d -> ModelSelector -> [(String, Double, Double)]
gridSearch dataset selector = 
    let allCombinations = generateHyperparameterCombinations selector
        results = map (\combination -> 
            let (modelName, hyperparams) = combination
                model = createModel modelName hyperparams
                scores = crossValidation dataset train model (crossValidationFolds selector)
                avgScore = sum scores / fromIntegral (length scores)
            in (modelName, hyperparams, avgScore)
        ) allCombinations
    in sortBy (\a b -> compare (snd3 b) (snd3 a)) results
    where
        snd3 (_, _, c) = c

-- 生成超参数组合
generateHyperparameterCombinations :: ModelSelector -> [(String, Double)]
generateHyperparameterCombinations selector = 
    concatMap (\modelName -> 
        let params = Map.findWithDefault [] modelName (hyperparameters selector)
        in map (\param -> (modelName, param)) params
    ) (models selector)
```

## 7. 总结

机器学习基础提供了从数据中学习模式的系统方法：

1. **监督学习**: 线性回归、逻辑回归、支持向量机等
2. **无监督学习**: K-means聚类、主成分分析等
3. **模型评估**: 交叉验证、各种评估指标
4. **实际应用**: 特征工程、模型选择、超参数调优

通过Haskell的实现，我们可以：

- 形式化地表示机器学习算法
- 实现类型安全的模型训练和预测
- 构建可组合的机器学习管道
- 确保算法的正确性和可维护性

---

**相关文档**:

- [算法基础](../01-Computer-Science/001-Algorithms.md)
- [数据结构](../01-Computer-Science/002-Data-Structures.md)
- [计算复杂性理论](../01-Computer-Science/003-Computational-Complexity.md)
- [函数式编程基础](../haskell/01-Basic-Concepts/001-Functional-Programming-Foundation.md)
