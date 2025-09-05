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

### 1. 卷积神经网络

```rust
// CNN实现
use candle_core::{Device, Tensor, Result};
use candle_nn::{Conv2d, conv2d, linear, Conv2dConfig};

#[derive(Debug)]
pub struct ConvLayer {
    conv: Conv2d,
    activation: ActivationFunction,
}

#[derive(Debug)]
pub enum ActivationFunction {
    ReLU,
    Sigmoid,
    Tanh,
    LeakyReLU(f64),
}

impl ConvLayer {
    pub fn new(
        in_channels: usize,
        out_channels: usize,
        kernel_size: usize,
        device: &Device,
    ) -> Result<Self> {
        let config = Conv2dConfig {
            stride: 1,
            padding: 0,
            dilation: 1,
            groups: 1,
        };
        
        let conv = conv2d(in_channels, out_channels, kernel_size, config, device)?;
        
        Ok(Self {
            conv,
            activation: ActivationFunction::ReLU,
        })
    }
    
    pub fn forward(&self, x: &Tensor) -> Result<Tensor> {
        let conv_output = self.conv.forward(x)?;
        self.apply_activation(&conv_output)
    }
    
    fn apply_activation(&self, x: &Tensor) -> Result<Tensor> {
        match self.activation {
            ActivationFunction::ReLU => x.relu(),
            ActivationFunction::Sigmoid => x.sigmoid(),
            ActivationFunction::Tanh => x.tanh(),
            ActivationFunction::LeakyReLU(alpha) => {
                let positive = x.relu()?;
                let negative = (x * alpha)?.min(&Tensor::zeros_like(x)?)?;
                positive.add(&negative)
            }
        }
    }
}

// 完整的CNN模型
#[derive(Debug)]
pub struct CNN {
    conv_layers: Vec<ConvLayer>,
    fc_layers: Vec<LinearLayer>,
    dropout_rate: f64,
}

impl CNN {
    pub fn new(device: &Device) -> Result<Self> {
        let conv_layers = vec![
            ConvLayer::new(3, 32, 3, device)?,   // 输入: 3通道 (RGB)
            ConvLayer::new(32, 64, 3, device)?,  // 32 -> 64 特征图
            ConvLayer::new(64, 128, 3, device)?, // 64 -> 128 特征图
        ];
        
        let fc_layers = vec![
            LinearLayer::new(128 * 7 * 7, 512, device)?, // 假设输入是28x28，经过卷积后是7x7
            LinearLayer::new(512, 10, device)?,           // 10类分类
        ];
        
        Ok(Self {
            conv_layers,
            fc_layers,
            dropout_rate: 0.5,
        })
    }
    
    pub fn forward(&self, x: &Tensor, training: bool) -> Result<Tensor> {
        let mut output = x.clone();
        
        // 卷积层
        for conv_layer in &self.conv_layers {
            output = conv_layer.forward(&output)?;
            output = max_pool2d(&output, 2)?; // 2x2 最大池化
        }
        
        // 展平
        let batch_size = output.dim(0)?;
        output = output.reshape(&[batch_size, -1])?;
        
        // 全连接层
        for (i, fc_layer) in self.fc_layers.iter().enumerate() {
            output = fc_layer.forward(&output)?;
            
            // 除了最后一层，都应用dropout
            if training && i < self.fc_layers.len() - 1 {
                output = dropout(&output, self.dropout_rate)?;
            }
        }
        
        Ok(output)
    }
}

// 辅助函数
fn max_pool2d(x: &Tensor, kernel_size: usize) -> Result<Tensor> {
    // 简化的最大池化实现
    // 实际应用中应该使用优化的实现
    todo!("Implement optimized max pooling")
}

fn dropout(x: &Tensor, rate: f64) -> Result<Tensor> {
    if rate == 0.0 {
        return Ok(x.clone());
    }
    
    // 生成掩码
    let mask = Tensor::rand_like(x)?;
    let threshold = Tensor::full(1.0 - rate, x.shape(), x.device())?;
    let dropout_mask = mask.ge(&threshold)?;
    
    // 应用dropout并缩放
    let scale = 1.0 / (1.0 - rate);
    x.mul(&dropout_mask)?.mul(&Tensor::full(scale, x.shape(), x.device())?)
}

#[derive(Debug)]
pub struct LinearLayer {
    weight: Tensor,
    bias: Tensor,
}

impl LinearLayer {
    pub fn new(in_features: usize, out_features: usize, device: &Device) -> Result<Self> {
        // Xavier初始化
        let std = (2.0 / (in_features + out_features) as f64).sqrt();
        let weight = Tensor::randn(0.0, std, &[out_features, in_features], device)?;
        let bias = Tensor::zeros(&[out_features], device)?;
        
        Ok(Self { weight, bias })
    }
    
    pub fn forward(&self, x: &Tensor) -> Result<Tensor> {
        let linear_output = x.matmul(&self.weight.t()?)?;
        linear_output.add(&self.bias)
    }
}
```

### 2. 循环神经网络

```haskell
-- LSTM实现
{-# LANGUAGE RecordWildCards #-}

data LSTMCell = LSTMCell
  { forgetGate :: LinearLayer
  , inputGate :: LinearLayer
  , candidateGate :: LinearLayer
  , outputGate :: LinearLayer
  , hiddenSize :: Int
  } deriving (Show)

data LSTMState = LSTMState
  { hiddenState :: Vector Double
  , cellState :: Vector Double
  } deriving (Show)

-- LSTM前向传播
lstmForward :: LSTMCell -> Vector Double -> LSTMState -> LSTMState
lstmForward LSTMCell{..} input LSTMState{..} = 
  let combined = hiddenState V.++ input
      
      -- 遗忘门
      ft = sigmoid $ applyLinear forgetGate combined
      
      -- 输入门
      it = sigmoid $ applyLinear inputGate combined
      
      -- 候选值
      ct_tilde = tanh $ applyLinear candidateGate combined
      
      -- 更新细胞状态
      newCellState = V.zipWith3 (\f c i -> f * c + i * ct_tilde) 
                                ft cellState it
      
      -- 输出门
      ot = sigmoid $ applyLinear outputGate combined
      
      -- 新的隐藏状态
      newHiddenState = V.zipWith (*) ot (V.map tanh newCellState)
      
  in LSTMState newHiddenState newCellState
  where
    sigmoid x = 1 / (1 + exp (-x))

-- 序列处理
processSequence :: LSTMCell -> [Vector Double] -> LSTMState -> [Vector Double]
processSequence cell inputs initialState = 
  let states = scanl (lstmForward cell) initialState inputs
  in map hiddenState (tail states)

-- 注意力机制
data AttentionLayer = AttentionLayer
  { queryProjection :: LinearLayer
  , keyProjection :: LinearLayer
  , valueProjection :: LinearLayer
  , outputProjection :: LinearLayer
  , headDim :: Int
  , numHeads :: Int
  } deriving (Show)

-- 多头注意力
multiHeadAttention :: AttentionLayer -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
multiHeadAttention AttentionLayer{..} queries keys values = 
  let queryHeads = splitHeads $ applyLinearMatrix queryProjection queries
      keyHeads = splitHeads $ applyLinearMatrix keyProjection keys
      valueHeads = splitHeads $ applyLinearMatrix valueProjection values
      
      attentionOutputs = zipWith3 scaledDotProductAttention queryHeads keyHeads valueHeads
      concatenated = concatHeads attentionOutputs
      
  in applyLinearMatrix outputProjection concatenated
  where
    splitHeads :: Matrix Double -> [Matrix Double]
    splitHeads m = [getHeadMatrix i m | i <- [0..numHeads-1]]
    
    concatHeads :: [Matrix Double] -> Matrix Double
    concatHeads = foldl1 concatColumns

scaledDotProductAttention :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
scaledDotProductAttention q k v = 
  let scores = matmul q (transpose k)
      scaledScores = scaleMatrix (1 / sqrt (fromIntegral $ cols q)) scores
      attentionWeights = softmaxMatrix scaledScores
  in matmul attentionWeights v

-- Transformer块
data TransformerBlock = TransformerBlock
  { selfAttention :: AttentionLayer
  , feedForward :: [LinearLayer]
  , layerNorm1 :: LayerNorm
  , layerNorm2 :: LayerNorm
  , dropoutRate :: Double
  } deriving (Show)

transformerForward :: TransformerBlock -> Matrix Double -> Matrix Double
transformerForward TransformerBlock{..} input = 
  let -- 自注意力 + 残差连接
      attnOutput = multiHeadAttention selfAttention input input input
      normed1 = applyLayerNorm layerNorm1 (addMatrix input attnOutput)
      
      -- 前馈网络 + 残差连接
      ffOutput = foldl (\x layer -> applyLinearMatrix layer x) normed1 feedForward
      normed2 = applyLayerNorm layerNorm2 (addMatrix normed1 ffOutput)
      
  in normed2
```

## 强化学习

### 1. Q学习

```rust
// Q学习实现
use std::collections::HashMap;
use rand::prelude::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State(pub Vec<i32>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Action(pub i32);

pub struct QLearningAgent {
    q_table: HashMap<(State, Action), f64>,
    learning_rate: f64,
    discount_factor: f64,
    epsilon: f64,
    epsilon_decay: f64,
    epsilon_min: f64,
}

impl QLearningAgent {
    pub fn new(
        learning_rate: f64,
        discount_factor: f64,
        epsilon: f64,
        epsilon_decay: f64,
        epsilon_min: f64,
    ) -> Self {
        Self {
            q_table: HashMap::new(),
            learning_rate,
            discount_factor,
            epsilon,
            epsilon_decay,
            epsilon_min,
        }
    }
    
    pub fn get_q_value(&self, state: &State, action: &Action) -> f64 {
        *self.q_table.get(&(state.clone(), action.clone())).unwrap_or(&0.0)
    }
    
    pub fn update_q_value(
        &mut self,
        state: &State,
        action: &Action,
        reward: f64,
        next_state: &State,
        possible_actions: &[Action],
    ) {
        let current_q = self.get_q_value(state, action);
        
        // 找到下一状态的最大Q值
        let max_next_q = possible_actions
            .iter()
            .map(|a| self.get_q_value(next_state, a))
            .fold(f64::NEG_INFINITY, f64::max);
        
        // Q学习更新公式
        let new_q = current_q + self.learning_rate * 
            (reward + self.discount_factor * max_next_q - current_q);
        
        self.q_table.insert((state.clone(), action.clone()), new_q);
    }
    
    pub fn choose_action(&mut self, state: &State, possible_actions: &[Action]) -> Action {
        let mut rng = thread_rng();
        
        if rng.gen::<f64>() < self.epsilon {
            // 探索：随机选择动作
            possible_actions[rng.gen_range(0..possible_actions.len())].clone()
        } else {
            // 利用：选择Q值最高的动作
            possible_actions
                .iter()
                .max_by(|a, b| {
                    self.get_q_value(state, a)
                        .partial_cmp(&self.get_q_value(state, b))
                        .unwrap()
                })
                .unwrap()
                .clone()
        }
    }
    
    pub fn decay_epsilon(&mut self) {
        self.epsilon = (self.epsilon * self.epsilon_decay).max(self.epsilon_min);
    }
}

// 深度Q网络 (DQN)
use candle_core::{Device, Tensor};
use candle_nn::{linear, Linear, VarBuilder};

pub struct DQN {
    network: QNetwork,
    target_network: QNetwork,
    optimizer: Optimizer,
    replay_buffer: ReplayBuffer,
    device: Device,
}

pub struct QNetwork {
    layers: Vec<Linear>,
}

impl QNetwork {
    pub fn new(input_dim: usize, hidden_dims: &[usize], output_dim: usize, vs: VarBuilder) -> candle_core::Result<Self> {
        let mut layers = Vec::new();
        let mut current_dim = input_dim;
        
        for &hidden_dim in hidden_dims {
            layers.push(linear(current_dim, hidden_dim, vs.pp(&format!("layer_{}", layers.len())))?);
            current_dim = hidden_dim;
        }
        
        layers.push(linear(current_dim, output_dim, vs.pp("output"))?);
        
        Ok(Self { layers })
    }
    
    pub fn forward(&self, x: &Tensor) -> candle_core::Result<Tensor> {
        let mut output = x.clone();
        
        for (i, layer) in self.layers.iter().enumerate() {
            output = layer.forward(&output)?;
            
            // 除了输出层，都应用ReLU激活
            if i < self.layers.len() - 1 {
                output = output.relu()?;
            }
        }
        
        Ok(output)
    }
}

// 经验回放缓冲区
#[derive(Debug, Clone)]
pub struct Experience {
    pub state: Vec<f32>,
    pub action: usize,
    pub reward: f32,
    pub next_state: Vec<f32>,
    pub done: bool,
}

pub struct ReplayBuffer {
    buffer: Vec<Experience>,
    capacity: usize,
    position: usize,
}

impl ReplayBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            capacity,
            position: 0,
        }
    }
    
    pub fn push(&mut self, experience: Experience) {
        if self.buffer.len() < self.capacity {
            self.buffer.push(experience);
        } else {
            self.buffer[self.position] = experience;
        }
        self.position = (self.position + 1) % self.capacity;
    }
    
    pub fn sample(&self, batch_size: usize) -> Vec<Experience> {
        let mut rng = thread_rng();
        (0..batch_size)
            .map(|_| {
                let idx = rng.gen_range(0..self.buffer.len());
                self.buffer[idx].clone()
            })
            .collect()
    }
    
    pub fn len(&self) -> usize {
        self.buffer.len()
    }
}

// 策略梯度算法 (REINFORCE)
pub struct PolicyGradientAgent {
    policy_network: PolicyNetwork,
    optimizer: Optimizer,
    gamma: f64,
}

impl PolicyGradientAgent {
    pub fn train_episode(&mut self, episode: &[Experience]) -> candle_core::Result<f64> {
        let mut returns = Vec::new();
        let mut g = 0.0;
        
        // 计算折扣回报
        for experience in episode.iter().rev() {
            g = experience.reward + self.gamma * g;
            returns.push(g);
        }
        returns.reverse();
        
        // 标准化回报
        let mean = returns.iter().sum::<f64>() / returns.len() as f64;
        let std = (returns.iter()
            .map(|r| (r - mean).powi(2))
            .sum::<f64>() / returns.len() as f64).sqrt();
        
        for r in &mut returns {
            *r = (*r - mean) / (std + 1e-8);
        }
        
        // 计算策略梯度损失
        let mut total_loss = 0.0;
        for (experience, &ret) in episode.iter().zip(returns.iter()) {
            let state_tensor = Tensor::from_slice(
                &experience.state,
                &[1, experience.state.len()],
                &self.policy_network.device,
            )?;
            
            let action_probs = self.policy_network.forward(&state_tensor)?;
            let log_prob = action_probs.get(experience.action)?.log()?;
            let loss = -log_prob.to_scalar::<f64>()? * ret;
            total_loss += loss;
        }
        
        // 反向传播和优化
        // self.optimizer.backward_and_step(total_loss)?;
        
        Ok(total_loss / episode.len() as f64)
    }
}

pub struct PolicyNetwork {
    network: QNetwork,
    device: Device,
}

impl PolicyNetwork {
    pub fn forward(&self, x: &Tensor) -> candle_core::Result<Tensor> {
        let logits = self.network.forward(x)?;
        logits.softmax(candle_core::D::Minus1) // 转换为概率分布
    }
}
```

### 2. Actor-Critic算法

```haskell
-- Actor-Critic实现
data ActorCriticAgent = ActorCriticAgent
  { actor :: PolicyNetwork
  , critic :: ValueNetwork
  , actorOptimizer :: Optimizer
  , criticOptimizer :: Optimizer
  , gamma :: Double
  , actorLR :: Double
  , criticLR :: Double
  } deriving (Show)

-- 策略网络 (Actor)
data PolicyNetwork = PolicyNetwork
  { policyLayers :: [LinearLayer]
  , outputActivation :: ActivationFunction
  } deriving (Show)

-- 价值网络 (Critic)  
data ValueNetwork = ValueNetwork
  { valueLayers :: [LinearLayer]
  } deriving (Show)

-- Actor-Critic训练步骤
trainActorCritic :: ActorCriticAgent -> Experience -> ActorCriticAgent
trainActorCritic agent@ActorCriticAgent{..} experience = 
  let state = expState experience
      action = expAction experience
      reward = expReward experience
      nextState = expNextState experience
      done = expDone experience
      
      -- 计算TD误差
      currentValue = evaluateValue critic state
      nextValue = if done then 0 else evaluateValue critic nextState
      target = reward + gamma * nextValue
      tdError = target - currentValue
      
      -- 更新Critic
      criticLoss = tdError ^ 2
      newCritic = updateValueNetwork critic state target criticOptimizer
      
      -- 更新Actor
      actionProb = getPolicyProb actor state action
      actorLoss = -log actionProb * tdError
      newActor = updatePolicyNetwork actor state action tdError actorOptimizer
      
  in agent { actor = newActor, critic = newCritic }

-- 策略概率计算
getPolicyProb :: PolicyNetwork -> State -> Action -> Double
getPolicyProb PolicyNetwork{..} state action = 
  let logits = foldl applyLinear (stateToVector state) policyLayers
      probs = softmax logits
  in probs V.! actionToIndex action

-- 价值评估
evaluateValue :: ValueNetwork -> State -> Double
evaluateValue ValueNetwork{..} state = 
  let stateVec = stateToVector state
      value = foldl applyLinear stateVec valueLayers
  in V.head value

-- PPO (Proximal Policy Optimization)
data PPOAgent = PPOAgent
  { oldPolicy :: PolicyNetwork
  , newPolicy :: PolicyNetwork
  , valueNetwork :: ValueNetwork
  , clipRatio :: Double
  , ppoEpochs :: Int
  , batchSize :: Int
  } deriving (Show)

-- PPO目标函数
ppoObjective :: PPOAgent -> [Experience] -> Double
ppoObjective PPOAgent{..} experiences = 
  let advantages = computeAdvantages valueNetwork experiences
      ratios = map (computeRatio oldPolicy newPolicy) experiences
      clippedRatios = zipWith (clipRatio clipRatio) ratios advantages
      surrogateObjective = zipWith (*) clippedRatios advantages
  in sum surrogateObjective / fromIntegral (length experiences)
  where
    clipRatio eps ratio advantage = 
      let clipped = max (1 - eps) (min (1 + eps) ratio)
      in min (ratio * advantage) (clipped * advantage)

-- 优势函数计算 (GAE)
computeAdvantages :: ValueNetwork -> [Experience] -> [Double]
computeAdvantages valueNet experiences = 
  let values = map (evaluateValue valueNet . expState) experiences
      rewards = map expReward experiences
      deltas = zipWith3 (\r v v' -> r + gamma * v' - v) 
                       rewards values (tail values ++ [0])
      lambda = 0.95
  in scanr (\delta acc -> delta + gamma * lambda * acc) 0 deltas
```

## 模型部署与MLOps

### 1. 模型序列化

```rust
// 模型序列化和部署
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::{BufReader, BufWriter};

#[derive(Serialize, Deserialize)]
pub struct SerializableModel {
    pub model_type: String,
    pub version: String,
    pub parameters: Vec<f32>,
    pub architecture: ModelArchitecture,
    pub metadata: ModelMetadata,
}

#[derive(Serialize, Deserialize)]
pub struct ModelArchitecture {
    pub layers: Vec<LayerConfig>,
    pub input_shape: Vec<usize>,
    pub output_shape: Vec<usize>,
}

#[derive(Serialize, Deserialize)]
pub struct LayerConfig {
    pub layer_type: String,
    pub input_dim: usize,
    pub output_dim: usize,
    pub activation: String,
    pub parameters: Vec<f32>,
}

#[derive(Serialize, Deserialize)]
pub struct ModelMetadata {
    pub training_accuracy: f64,
    pub validation_accuracy: f64,
    pub training_time: String,
    pub data_version: String,
    pub feature_names: Vec<String>,
}

impl SerializableModel {
    pub fn save_to_file(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let file = File::create(path)?;
        let writer = BufWriter::new(file);
        serde_json::to_writer_pretty(writer, self)?;
        Ok(())
    }
    
    pub fn load_from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let model = serde_json::from_reader(reader)?;
        Ok(model)
    }
    
    pub fn to_onnx(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        // 转换为ONNX格式
        todo!("Implement ONNX conversion")
    }
    
    pub fn to_tensorrt(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        // 转换为TensorRT格式以在GPU上优化推理
        todo!("Implement TensorRT conversion")
    }
}

// 模型服务器
use axum::{
    extract::{Json, Path},
    http::StatusCode,
    response::Json as ResponseJson,
    routing::{get, post},
    Router,
};
use tokio::net::TcpListener;

#[derive(Deserialize)]
pub struct PredictionRequest {
    pub features: Vec<f32>,
    pub model_version: Option<String>,
}

#[derive(Serialize)]
pub struct PredictionResponse {
    pub prediction: Vec<f32>,
    pub confidence: f64,
    pub model_version: String,
    pub inference_time_ms: f64,
}

pub struct ModelServer {
    models: std::collections::HashMap<String, SerializableModel>,
    current_model: String,
}

impl ModelServer {
    pub fn new() -> Self {
        Self {
            models: std::collections::HashMap::new(),
            current_model: String::new(),
        }
    }
    
    pub fn load_model(&mut self, version: String, model: SerializableModel) {
        self.models.insert(version.clone(), model);
        self.current_model = version;
    }
    
    pub async fn predict(&self, request: PredictionRequest) -> Result<PredictionResponse, StatusCode> {
        let start_time = std::time::Instant::now();
        
        let model_version = request.model_version
            .unwrap_or_else(|| self.current_model.clone());
        
        let model = self.models.get(&model_version)
            .ok_or(StatusCode::NOT_FOUND)?;
        
        // 执行推理
        let prediction = self.run_inference(model, &request.features)
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
        
        let confidence = self.calculate_confidence(&prediction);
        let inference_time = start_time.elapsed().as_millis() as f64;
        
        Ok(PredictionResponse {
            prediction,
            confidence,
            model_version,
            inference_time_ms: inference_time,
        })
    }
    
    fn run_inference(&self, model: &SerializableModel, features: &[f32]) -> Result<Vec<f32>, Box<dyn std::error::Error>> {
        // 实现模型推理逻辑
        // 这里简化为直接返回特征向量
        Ok(features.to_vec())
    }
    
    fn calculate_confidence(&self, prediction: &[f32]) -> f64 {
        // 计算预测置信度
        let max_value = prediction.iter().fold(f32::NEG_INFINITY, |a, &b| a.max(b));
        let sum_exp: f32 = prediction.iter().map(|&x| (x - max_value).exp()).sum();
        let max_prob = (max_value - max_value).exp() / sum_exp;
        max_prob as f64
    }
}

// REST API端点
pub async fn create_routes() -> Router {
    Router::new()
        .route("/predict", post(predict_handler))
        .route("/models", get(list_models_handler))
        .route("/models/:version", get(get_model_info_handler))
        .route("/health", get(health_check_handler))
}

async fn predict_handler(
    Json(request): Json<PredictionRequest>,
) -> Result<ResponseJson<PredictionResponse>, StatusCode> {
    // 这里需要访问模型服务器实例
    todo!("Implement prediction handler with model server access")
}

async fn health_check_handler() -> ResponseJson<serde_json::Value> {
    ResponseJson(serde_json::json!({
        "status": "healthy",
        "timestamp": chrono::Utc::now().to_rfc3339(),
        "version": env!("CARGO_PKG_VERSION")
    }))
}
```

### 2. 监控和A/B测试

```rust
// 模型监控
use prometheus::{Counter, Histogram, Gauge, Registry};
use std::sync::Arc;

#[derive(Clone)]
pub struct ModelMetrics {
    prediction_counter: Counter,
    prediction_latency: Histogram,
    model_accuracy: Gauge,
    data_drift_score: Gauge,
    error_counter: Counter,
}

impl ModelMetrics {
    pub fn new(registry: &Registry) -> Result<Self, prometheus::Error> {
        let prediction_counter = Counter::new(
            "ml_predictions_total",
            "Total number of predictions made",
        )?;
        registry.register(Box::new(prediction_counter.clone()))?;
        
        let prediction_latency = Histogram::with_opts(
            prometheus::HistogramOpts::new(
                "ml_prediction_duration_seconds",
                "Time taken for predictions",
            ).buckets(vec![0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0]),
        )?;
        registry.register(Box::new(prediction_latency.clone()))?;
        
        let model_accuracy = Gauge::new(
            "ml_model_accuracy",
            "Current model accuracy",
        )?;
        registry.register(Box::new(model_accuracy.clone()))?;
        
        let data_drift_score = Gauge::new(
            "ml_data_drift_score",
            "Data drift detection score",
        )?;
        registry.register(Box::new(data_drift_score.clone()))?;
        
        let error_counter = Counter::new(
            "ml_prediction_errors_total",
            "Total number of prediction errors",
        )?;
        registry.register(Box::new(error_counter.clone()))?;
        
        Ok(Self {
            prediction_counter,
            prediction_latency,
            model_accuracy,
            data_drift_score,
            error_counter,
        })
    }
    
    pub fn record_prediction(&self, latency: f64, success: bool) {
        self.prediction_counter.inc();
        self.prediction_latency.observe(latency);
        
        if !success {
            self.error_counter.inc();
        }
    }
    
    pub fn update_accuracy(&self, accuracy: f64) {
        self.model_accuracy.set(accuracy);
    }
    
    pub fn update_drift_score(&self, score: f64) {
        self.data_drift_score.set(score);
    }
}

// A/B测试框架
#[derive(Debug, Clone)]
pub struct ABTestConfig {
    pub test_name: String,
    pub traffic_split: f64, // 0.0 to 1.0
    pub control_model: String,
    pub treatment_model: String,
    pub start_time: chrono::DateTime<chrono::Utc>,
    pub end_time: chrono::DateTime<chrono::Utc>,
}

pub struct ABTestManager {
    tests: std::collections::HashMap<String, ABTestConfig>,
    results: std::collections::HashMap<String, ABTestResults>,
}

#[derive(Debug, Clone)]
pub struct ABTestResults {
    pub control_metrics: TestMetrics,
    pub treatment_metrics: TestMetrics,
    pub statistical_significance: f64,
    pub winner: Option<String>,
}

#[derive(Debug, Clone)]
pub struct TestMetrics {
    pub total_requests: u64,
    pub total_errors: u64,
    pub avg_latency: f64,
    pub avg_accuracy: f64,
    pub conversion_rate: f64,
}

impl ABTestManager {
    pub fn new() -> Self {
        Self {
            tests: std::collections::HashMap::new(),
            results: std::collections::HashMap::new(),
        }
    }
    
    pub fn create_test(&mut self, config: ABTestConfig) {
        self.tests.insert(config.test_name.clone(), config);
    }
    
    pub fn should_use_treatment(&self, test_name: &str, user_id: &str) -> bool {
        if let Some(config) = self.tests.get(test_name) {
            let now = chrono::Utc::now();
            if now >= config.start_time && now <= config.end_time {
                // 使用用户ID的哈希来确定分组
                let hash = std::collections::hash_map::DefaultHasher::new();
                use std::hash::{Hash, Hasher};
                user_id.hash(&mut hash);
                let hash_value = hash.finish();
                let probability = (hash_value % 10000) as f64 / 10000.0;
                
                return probability < config.traffic_split;
            }
        }
        false
    }
    
    pub fn record_result(
        &mut self,
        test_name: &str,
        is_treatment: bool,
        latency: f64,
        success: bool,
        accuracy: f64,
    ) {
        // 记录A/B测试结果
        let results = self.results.entry(test_name.to_string())
            .or_insert_with(|| ABTestResults {
                control_metrics: TestMetrics::default(),
                treatment_metrics: TestMetrics::default(),
                statistical_significance: 0.0,
                winner: None,
            });
        
        let metrics = if is_treatment {
            &mut results.treatment_metrics
        } else {
            &mut results.control_metrics
        };
        
        metrics.total_requests += 1;
        if !success {
            metrics.total_errors += 1;
        }
        
        // 更新移动平均
        let n = metrics.total_requests as f64;
        metrics.avg_latency = (metrics.avg_latency * (n - 1.0) + latency) / n;
        metrics.avg_accuracy = (metrics.avg_accuracy * (n - 1.0) + accuracy) / n;
    }
    
    pub fn analyze_test(&mut self, test_name: &str) -> Option<&ABTestResults> {
        if let Some(results) = self.results.get_mut(test_name) {
            // 执行统计显著性检验
            let significance = self.calculate_statistical_significance(
                &results.control_metrics,
                &results.treatment_metrics,
            );
            
            results.statistical_significance = significance;
            
            // 确定获胜者
            if significance > 0.95 {
                if results.treatment_metrics.avg_accuracy > results.control_metrics.avg_accuracy {
                    results.winner = Some("treatment".to_string());
                } else {
                    results.winner = Some("control".to_string());
                }
            }
            
            Some(results)
        } else {
            None
        }
    }
    
    fn calculate_statistical_significance(&self, control: &TestMetrics, treatment: &TestMetrics) -> f64 {
        // 简化的t检验实现
        if control.total_requests < 30 || treatment.total_requests < 30 {
            return 0.0; // 样本量不足
        }
        
        let control_mean = control.avg_accuracy;
        let treatment_mean = treatment.avg_accuracy;
        
        // 假设标准差
        let control_std = 0.1; // 简化假设
        let treatment_std = 0.1;
        
        let n1 = control.total_requests as f64;
        let n2 = treatment.total_requests as f64;
        
        let standard_error = ((control_std.powi(2) / n1) + (treatment_std.powi(2) / n2)).sqrt();
        let t_stat = (treatment_mean - control_mean).abs() / standard_error;
        
        // 简化的p值计算（实际应该使用t分布）
        let p_value = 2.0 * (1.0 - (1.0 + t_stat).ln());
        1.0 - p_value.max(0.0).min(1.0)
    }
}

impl Default for TestMetrics {
    fn default() -> Self {
        Self {
            total_requests: 0,
            total_errors: 0,
            avg_latency: 0.0,
            avg_accuracy: 0.0,
            conversion_rate: 0.0,
        }
    }
}
```

## 总结

函数式编程在机器学习中的优势：

1. **数学表达力**: 函数式编程与机器学习的数学基础天然契合
2. **组合性**: 复杂模型可以通过简单组件组合构建
3. **并行性**: 纯函数特性使得并行计算更安全高效
4. **类型安全**: 编译时保证模型结构和数据流的正确性
5. **可重现性**: 确定性计算保证实验的可重现性

现代机器学习的关键要素：

- **深度学习**: CNN、RNN、Transformer等现代架构
- **强化学习**: Q学习、策略梯度、Actor-Critic算法
- **模型部署**: 序列化、服务化、监控和A/B测试
- **MLOps**: 版本控制、持续集成、自动化管道
- **可观测性**: 指标监控、性能分析、异常检测

通过结合函数式编程的理论优势和现代机器学习技术，我们能够构建更可靠、可维护和可扩展的AI系统。

---

**相关链接**：

- [算法实现](../../07-Implementation/004-Algorithms.md)
- [性能优化](../../07-Implementation/006-Performance-Optimization.md)
- [系统架构](../../06-Architecture/001-System-Architecture.md)
- [分布式系统](../../06-Architecture/003-Distributed-Systems.md)
