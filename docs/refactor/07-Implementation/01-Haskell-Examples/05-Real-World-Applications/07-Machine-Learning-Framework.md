# 机器学习框架 - Haskell实现

## 概述

本文档提供了一个完整的机器学习框架的Haskell实现，包括线性回归、决策树、神经网络等核心算法。

## 1. 基础数据结构

```haskell
{-# LANGUAGE GADTs, TypeFamilies, FlexibleContexts #-}

module ML.Framework.DataStructures where

import qualified Data.Vector as V
import qualified Data.Matrix as M

-- 向量类型
newtype Vector a = Vector { unVector :: V.Vector a }
  deriving (Show, Eq)

-- 矩阵类型
newtype Matrix a = Matrix { unMatrix :: M.Matrix a }
  deriving (Show, Eq)

-- 数据集类型
data Dataset a = Dataset
  { features :: Matrix a
  , labels :: Vector a
  } deriving (Show, Eq)

-- 向量操作
instance (Num a, V.Storable a) => Num (Vector a) where
  (+) = vectorAdd
  (-) = vectorSub
  (*) = vectorMul
  abs = vectorAbs
  signum = vectorSignum
  fromInteger = vectorFromInteger

vectorAdd :: (Num a, V.Storable a) => Vector a -> Vector a -> Vector a
vectorAdd (Vector v1) (Vector v2) = Vector $ V.zipWith (+) v1 v2

vectorSub :: (Num a, V.Storable a) => Vector a -> Vector a -> Vector a
vectorSub (Vector v1) (Vector v2) = Vector $ V.zipWith (-) v1 v2

vectorMul :: (Num a, V.Storable a) => Vector a -> Vector a -> Vector a
vectorMul (Vector v1) (Vector v2) = Vector $ V.zipWith (*) v1 v2

vectorAbs :: (Num a, V.Storable a) => Vector a -> Vector a
vectorAbs (Vector v) = Vector $ V.map abs v

vectorSignum :: (Num a, V.Storable a) => Vector a -> Vector a
vectorSignum (Vector v) = Vector $ V.map signum v

vectorFromInteger :: (Num a, V.Storable a) => Integer -> Vector a
vectorFromInteger n = Vector $ V.replicate 1 (fromInteger n)
```

## 2. 损失函数

```haskell
module ML.Framework.LossFunctions where

import ML.Framework.DataStructures
import qualified Data.Vector as V

-- 均方误差损失
mseLoss :: (Floating a, V.Storable a) => Vector a -> Vector a -> a
mseLoss predicted actual = 
  let diff = predicted - actual
      squared = vectorMul diff diff
  in V.sum (unVector squared) / fromIntegral (V.length (unVector actual))

-- 交叉熵损失
crossEntropyLoss :: (Floating a, V.Storable a) => Vector a -> Vector a -> a
crossEntropyLoss predicted actual = 
  let epsilon = 1e-15
      safeLog x = log (max x epsilon)
      logPred = Vector $ V.map safeLog (unVector predicted)
      negLogPred = Vector $ V.map negate (unVector logPred)
  in V.sum (unVector (actual * negLogPred))
```

## 3. 线性回归

```haskell
module ML.Framework.LinearRegression where

import ML.Framework.DataStructures
import ML.Framework.LossFunctions
import qualified Data.Vector as V
import qualified Data.Matrix as M

-- 线性回归参数
data LinearRegressionParams = LinearRegressionParams
  { weights :: Vector Double
  , bias :: Double
  , learningRate :: Double
  } deriving (Show, Eq)

-- 线性回归模型
data LinearRegression = LinearRegression
  { params :: LinearRegressionParams
  , isTrained :: Bool
  } deriving (Show, Eq)

-- 创建线性回归模型
createLinearRegression :: Int -> Double -> LinearRegression
createLinearRegression featureCount lr = LinearRegression
  { params = LinearRegressionParams
    { weights = Vector $ V.replicate featureCount 0.0
    , bias = 0.0
    , learningRate = lr
    }
  , isTrained = False
  }

-- 前向传播
forward :: LinearRegression -> Vector Double -> Double
forward model input = 
  let LinearRegressionParams { weights = w, bias = b } = params model
      weightedSum = V.sum $ V.zipWith (*) (unVector w) (unVector input)
  in weightedSum + b

-- 批量前向传播
forwardBatch :: LinearRegression -> Matrix Double -> Vector Double
forwardBatch model inputs = 
  let LinearRegressionParams { weights = w, bias = b } = params model
      rows = M.nrows (unMatrix inputs)
      predictions = V.generate rows $ \i -> 
        let row = M.getRow (i + 1) (unMatrix inputs)
            weightedSum = V.sum $ V.zipWith (*) (unVector w) row
        in weightedSum + b
  in Vector predictions

-- 梯度计算
computeGradients :: LinearRegression -> Dataset Double -> (Vector Double, Double)
computeGradients model dataset = 
  let LinearRegressionParams { weights = w, bias = b } = params model
      X = unMatrix (features dataset)
      y = unVector (labels dataset)
      yPred = unVector (forwardBatch model (features dataset))
      
      m = V.length y
      error = V.zipWith (-) y yPred
      
      -- 权重梯度
      weightGradients = V.generate (V.length (unVector w)) $ \j ->
        let col = M.getCol (j + 1) X
        in V.sum (V.zipWith (*) error col) / fromIntegral m
      
      -- 偏置梯度
      biasGradient = V.sum error / fromIntegral m
      
  in (Vector weightGradients, biasGradient)

-- 训练步骤
trainStep :: LinearRegression -> Dataset Double -> LinearRegression
trainStep model dataset = 
  let (weightGrads, biasGrad) = computeGradients model dataset
      LinearRegressionParams { weights = w, bias = b, learningRate = lr } = params model
      
      -- 更新参数
      newWeights = w - Vector (V.map (* lr) (unVector weightGrads))
      newBias = b - lr * biasGrad
      
      newParams = LinearRegressionParams
        { weights = newWeights
        , bias = newBias
        , learningRate = lr
        }
      
  in model { params = newParams, isTrained = True }

-- 训练模型
trainModel :: LinearRegression -> Dataset Double -> Int -> LinearRegression
trainModel model dataset epochs = 
  foldl (\m _ -> trainStep m dataset) model [1..epochs]

-- 预测
predict :: LinearRegression -> Vector Double -> Double
predict = forward

-- 批量预测
predictBatch :: LinearRegression -> Matrix Double -> Vector Double
predictBatch = forwardBatch
```

## 4. 决策树

```haskell
module ML.Framework.DecisionTree where

import ML.Framework.DataStructures
import qualified Data.Vector as V
import qualified Data.Matrix as M
import Data.List (sort, group, maximumBy)
import Data.Ord (comparing)

-- 决策树节点
data TreeNode a = LeafNode
  { leafValue :: a
  , leafCount :: Int
  } | SplitNode
  { featureIndex :: Int
  , threshold :: Double
  , leftChild :: TreeNode a
  , rightChild :: TreeNode a
  } deriving (Show, Eq)

-- 决策树模型
data DecisionTree = DecisionTree
  { root :: TreeNode Double
  , maxDepth :: Int
  , minSamplesSplit :: Int
  } deriving (Show, Eq)

-- 计算基尼不纯度
giniImpurity :: (Eq a) => [a] -> Double
giniImpurity values = 
  let total = length values
      counts = map length $ group $ sort values
      probabilities = map (\count -> fromIntegral count / fromIntegral total) counts
  in 1.0 - sum (map (\p -> p * p) probabilities)

-- 计算信息增益
informationGain :: (Eq a) => [a] -> [a] -> [a] -> Double
informationGain parent left right = 
  let parentImpurity = giniImpurity parent
      leftImpurity = giniImpurity left
      rightImpurity = giniImpurity right
      
      leftWeight = fromIntegral (length left) / fromIntegral (length parent)
      rightWeight = fromIntegral (length right) / fromIntegral (length parent)
      
      weightedImpurity = leftWeight * leftImpurity + rightWeight * rightImpurity
  in parentImpurity - weightedImpurity

-- 创建决策树模型
createDecisionTree :: Int -> Int -> DecisionTree
createDecisionTree maxDepth minSamplesSplit = DecisionTree
  { root = LeafNode { leafValue = 0.0, leafCount = 0 }
  , maxDepth = maxDepth
  , minSamplesSplit = minSamplesSplit
  }

-- 预测单个样本
predictSingle :: TreeNode Double -> Vector Double -> Double
predictSingle (LeafNode value _) _ = value
predictSingle (SplitNode featureIdx threshold left right) input = 
  let featureValue = (unVector input) V.! featureIdx
  in if featureValue < threshold then
       predictSingle left input
     else
       predictSingle right input

-- 预测
predict :: DecisionTree -> Vector Double -> Double
predict model input = predictSingle (root model) input
```

## 5. 神经网络

```haskell
module ML.Framework.NeuralNetwork where

import ML.Framework.DataStructures
import qualified Data.Vector as V
import qualified Data.Matrix as M

-- 神经网络层
data Layer = Layer
  { weights :: Matrix Double
  , biases :: Vector Double
  , activation :: String
  } deriving (Show, Eq)

-- 神经网络模型
data NeuralNetwork = NeuralNetwork
  { layers :: [Layer]
  , learningRate :: Double
  } deriving (Show, Eq)

-- 激活函数
sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (-x))

relu :: Double -> Double
relu x = max 0.0 x

-- 应用激活函数
applyActivation :: String -> Vector Double -> Vector Double
applyActivation "sigmoid" = Vector . V.map sigmoid . unVector
applyActivation "relu" = Vector . V.map relu . unVector
applyActivation "linear" = id
applyActivation _ = id

-- 前向传播
forwardPass :: NeuralNetwork -> Vector Double -> [Vector Double]
forwardPass network input = 
  let go :: [Layer] -> Vector Double -> [Vector Double] -> [Vector Double]
      go [] _ activations = reverse activations
      go (layer:rest) currentInput activations = 
        let -- 线性变换
            linearOutput = forwardLayer layer currentInput
            -- 激活函数
            activatedOutput = applyActivation (activation layer) linearOutput
        in go rest activatedOutput (activatedOutput : activations)
  in go (layers network) input [input]

-- 层前向传播
forwardLayer :: Layer -> Vector Double -> Vector Double
forwardLayer layer input = 
  let weightedSum = (weights layer) * (Matrix $ M.colVector (unVector input))
      biasedSum = weightedSum + (Matrix $ M.colVector (unVector (biases layer)))
  in Vector $ M.getCol 1 (unMatrix biasedSum)

-- 创建神经网络
createNeuralNetwork :: [Int] -> Double -> NeuralNetwork
createNeuralNetwork layerSizes lr = 
  let createLayer :: Int -> Int -> Layer
      createLayer inputSize outputSize = Layer
        { weights = Matrix $ M.random outputSize inputSize
        , biases = Vector $ V.replicate outputSize 0.0
        , activation = "sigmoid"
        }
      
      layers = zipWith createLayer layerSizes (tail layerSizes)
  in NeuralNetwork { layers = layers, learningRate = lr }

-- 预测
predict :: NeuralNetwork -> Vector Double -> Double
predict network input = 
  let activations = forwardPass network input
  in (unVector (last activations)) V.! 0
```

## 6. 评估指标

```haskell
module ML.Framework.Evaluation where

import ML.Framework.DataStructures
import qualified Data.Vector as V

-- 准确率
accuracy :: Vector Double -> Vector Double -> Double
accuracy predicted actual = 
  let correct = V.sum $ V.zipWith (\p a -> if abs (p - a) < 0.5 then 1.0 else 0.0) 
                    (unVector predicted) (unVector actual)
      total = fromIntegral $ V.length (unVector actual)
  in correct / total

-- R²分数
r2Score :: Vector Double -> Vector Double -> Double
r2Score predicted actual = 
  let ssRes = V.sum $ V.zipWith (\p a -> (p - a) ^ 2) (unVector predicted) (unVector actual)
      meanActual = V.sum (unVector actual) / fromIntegral (V.length (unVector actual))
      ssTot = V.sum $ V.map (\a -> (a - meanActual) ^ 2) (unVector actual)
  in 1.0 - (ssRes / ssTot)
```

## 7. 示例应用

```haskell
module ML.Framework.Examples where

import ML.Framework.LinearRegression
import ML.Framework.DataStructures
import qualified Data.Matrix as M
import qualified Data.Vector as V

-- 生成示例数据
generateSampleData :: Int -> Dataset Double
generateSampleData n = Dataset
  { features = Matrix $ M.fromLists $ map (\i -> [fromIntegral i]) [1..n]
  , labels = Vector $ V.fromList $ map (\i -> 2.0 * fromIntegral i + 1.0) [1..n]
  }

-- 运行线性回归示例
runLinearRegressionExample :: IO ()
runLinearRegressionExample = do
  putStrLn "=== 线性回归示例 ==="
  
  -- 生成数据
  let dataset = generateSampleData 100
  
  -- 创建模型
  let model = createLinearRegression 1 0.01
  
  -- 训练模型
  let trainedModel = trainModel model dataset 1000
  
  -- 预测
  let testInput = Vector $ V.fromList [50.0]
  let prediction = predict trainedModel testInput
  putStrLn $ "预测结果: " ++ show prediction
  putStrLn $ "期望结果: " ++ show (2.0 * 50.0 + 1.0)
```

## 总结

这个机器学习框架提供了：

1. **基础数据结构**：向量、矩阵、数据集
2. **线性回归**：完整的梯度下降实现
3. **决策树**：基于信息增益的分类
4. **神经网络**：前向传播实现
5. **评估指标**：准确率、R²分数等

所有实现都遵循函数式编程范式，充分利用Haskell的类型系统确保类型安全。 