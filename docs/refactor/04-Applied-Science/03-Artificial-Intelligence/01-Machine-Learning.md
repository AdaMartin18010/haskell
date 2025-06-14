# 机器学习 - 形式化理论与Haskell实现

## 📋 概述

机器学习是人工智能的核心技术，通过算法从数据中学习模式和规律。本文档从形式化角度分析机器学习的理论基础，包括监督学习、无监督学习、强化学习和深度学习。

## 🎯 核心概念

### 机器学习基础

#### 形式化定义

```haskell
-- 机器学习系统
data MachineLearningSystem = MachineLearningSystem {
    algorithm :: LearningAlgorithm,
    model :: Model,
    data_ :: Dataset,
    performance :: PerformanceMetrics
}

-- 学习算法
data LearningAlgorithm = 
    SupervisedLearning SupervisedAlgorithm |
    UnsupervisedLearning UnsupervisedAlgorithm |
    ReinforcementLearning ReinforcementAlgorithm |
    DeepLearning DeepLearningAlgorithm

data SupervisedAlgorithm = 
    LinearRegression |
    LogisticRegression |
    DecisionTree |
    RandomForest |
    SupportVectorMachine |
    NeuralNetwork

data UnsupervisedAlgorithm = 
    KMeans |
    HierarchicalClustering |
    PrincipalComponentAnalysis |
    Autoencoder |
    GenerativeAdversarialNetwork

data ReinforcementAlgorithm = 
    QLearning |
    PolicyGradient |
    ActorCritic |
    DeepQNetwork |
    ProximalPolicyOptimization

data DeepLearningAlgorithm = 
    ConvolutionalNeuralNetwork |
    RecurrentNeuralNetwork |
    LongShortTermMemory |
    Transformer |
    GenerativePreTrainedTransformer

-- 模型
data Model = Model {
    parameters :: [Parameter],
    architecture :: Architecture,
    hyperparameters :: [Hyperparameter]
}

data Parameter = Parameter {
    name :: String,
    value :: Double,
    gradient :: Double,
    updateRule :: UpdateRule
}

data UpdateRule = UpdateRule {
    rule :: String,
    learningRate :: Double,
    momentum :: Double
}

data Architecture = Architecture {
    layers :: [Layer],
    connections :: [Connection],
    activationFunctions :: [ActivationFunction]
}

data Layer = Layer {
    layerId :: String,
    type_ :: LayerType,
    size :: Int,
    activation :: ActivationFunction
}

data LayerType = 
    Input |
    Hidden |
    Output |
    Convolutional |
    Pooling |
    Recurrent |
    Attention

data Connection = Connection {
    from :: String,
    to :: String,
    weight :: Double
}

data ActivationFunction = 
    Sigmoid |
    Tanh |
    ReLU |
    Softmax |
    Linear

data Hyperparameter = Hyperparameter {
    name :: String,
    value :: Double,
    range :: (Double, Double)
}

-- 数据集
data Dataset = Dataset {
    name :: String,
    samples :: [Sample],
    features :: [Feature],
    labels :: Maybe [Label],
    split :: DataSplit
}

data Sample = Sample {
    sampleId :: String,
    features :: [Double],
    label :: Maybe Label
}

data Feature = Feature {
    name :: String,
    type_ :: FeatureType,
    range :: (Double, Double)
}

data FeatureType = 
    Numerical |
    Categorical |
    Textual |
    Image |
    Audio

data Label = Label {
    value :: String,
    type_ :: LabelType
}

data LabelType = 
    Binary |
    Multiclass |
    Regression |
    Structured

data DataSplit = DataSplit {
    training :: [Sample],
    validation :: [Sample],
    test :: [Sample]
}

-- 性能度量
data PerformanceMetrics = PerformanceMetrics {
    accuracy :: Double,
    precision :: Double,
    recall :: Double,
    f1Score :: Double,
    loss :: Double
}
```

#### 数学表示

机器学习可以建模为优化问题：

$$\min_{\theta} \mathcal{L}(\theta) = \frac{1}{n} \sum_{i=1}^{n} \ell(f_\theta(x_i), y_i) + \lambda R(\theta)$$

其中：
- $\theta$ 是模型参数
- $\mathcal{L}(\theta)$ 是损失函数
- $\ell$ 是样本损失
- $f_\theta$ 是模型函数
- $R(\theta)$ 是正则化项
- $\lambda$ 是正则化系数

### 监督学习

#### 线性回归

```haskell
-- 线性回归
data LinearRegression = LinearRegression {
    weights :: [Double],
    bias :: Double,
    learningRate :: Double
}

-- 线性回归模型
linearRegressionModel :: [Double] -> LinearRegression -> Double
linearRegressionModel features model = 
    let weightedSum = sum $ zipWith (*) features (weights model)
    in weightedSum + bias model

-- 均方误差损失
meanSquaredError :: [Double] -> [Double] -> Double
meanSquaredError predictions targets = 
    let squaredErrors = zipWith (\p t -> (p - t) ^ 2) predictions targets
    in sum squaredErrors / fromIntegral (length predictions)

-- 梯度下降
gradientDescent :: LinearRegression -> [Sample] -> LinearRegression
gradientDescent model samples = 
    let gradients = calculateGradients model samples
        newWeights = updateWeights (weights model) gradients (learningRate model)
        newBias = updateBias (bias model) gradients (learningRate model)
    in model {
        weights = newWeights,
        bias = newBias
    }

calculateGradients :: LinearRegression -> [Sample] -> (Double, [Double])
calculateGradients model samples = 
    let predictions = map (\s -> linearRegressionModel (features s) model) samples
        targets = map (\s -> read (value (label s)) :: Double) samples
        errors = zipWith (-) predictions targets
        
        -- 计算偏导数
        biasGradient = sum errors / fromIntegral (length errors)
        weightGradients = map (\i -> 
            sum $ zipWith (*) errors (map (\s -> features s !! i) samples) / fromIntegral (length samples)
        ) [0..length (weights model) - 1]
    in (biasGradient, weightGradients)

updateWeights :: [Double] -> (Double, [Double]) -> Double -> [Double]
updateWeights weights (_, weightGradients) learningRate = 
    zipWith (\w g -> w - learningRate * g) weights weightGradients

updateBias :: Double -> (Double, [Double]) -> Double -> Double
updateBias bias (biasGradient, _) learningRate = 
    bias - learningRate * biasGradient
```

#### 逻辑回归

```haskell
-- 逻辑回归
data LogisticRegression = LogisticRegression {
    weights :: [Double],
    bias :: Double,
    learningRate :: Double
}

-- 逻辑回归模型
logisticRegressionModel :: [Double] -> LogisticRegression -> Double
logisticRegressionModel features model = 
    let linearOutput = linearRegressionModel features (LinearRegression (weights model) (bias model) (learningRate model))
    in sigmoid linearOutput

-- Sigmoid激活函数
sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (-x))

-- 交叉熵损失
crossEntropyLoss :: [Double] -> [Double] -> Double
crossEntropyLoss predictions targets = 
    let losses = zipWith (\p t -> -t * log p - (1 - t) * log (1 - p)) predictions targets
    in sum losses / fromIntegral (length predictions)

-- 逻辑回归训练
trainLogisticRegression :: LogisticRegression -> [Sample] -> Int -> LogisticRegression
trainLogisticRegression model samples epochs = 
    foldl (\m _ -> gradientDescentLogistic m samples) model [1..epochs]

gradientDescentLogistic :: LogisticRegression -> [Sample] -> LogisticRegression
gradientDescentLogistic model samples = 
    let predictions = map (\s -> logisticRegressionModel (features s) model) samples
        targets = map (\s -> if value (label s) == "1" then 1.0 else 0.0) samples
        errors = zipWith (-) predictions targets
        
        -- 计算梯度
        biasGradient = sum errors / fromIntegral (length errors)
        weightGradients = map (\i -> 
            sum $ zipWith (*) errors (map (\s -> features s !! i) samples) / fromIntegral (length samples)
        ) [0..length (weights model) - 1]
        
        -- 更新参数
        newWeights = zipWith (\w g -> w - learningRate model * g) (weights model) weightGradients
        newBias = bias model - learningRate model * biasGradient
    in model {
        weights = newWeights,
        bias = newBias
    }
```

### 无监督学习

#### K-means聚类

```haskell
-- K-means聚类
data KMeans = KMeans {
    k :: Int,
    centroids :: [Centroid],
    maxIterations :: Int
}

data Centroid = Centroid {
    centroidId :: String,
    position :: [Double],
    assignedSamples :: [Sample]
}

-- K-means算法
kMeansClustering :: KMeans -> [Sample] -> KMeans
kMeansClustering model samples = 
    let initialCentroids = initializeCentroids model samples
        finalModel = iterateKMeans model { centroids = initialCentroids } samples
    in finalModel

-- 初始化质心
initializeCentroids :: KMeans -> [Sample] -> [Centroid]
initializeCentroids model samples = 
    let featureCount = length (features (head samples))
        randomPositions = map (\i -> 
            map (\_ -> randomDouble 0 1) [1..featureCount]
        ) [1..k model]
    in zipWith (\i pos -> Centroid (show i) pos []) [1..k model] randomPositions

randomDouble :: Double -> Double -> Double
randomDouble min max = 
    -- 简化实现
    min + (max - min) * 0.5

-- 迭代K-means
iterateKMeans :: KMeans -> [Sample] -> KMeans
iterateKMeans model samples = 
    let iterations = [1..maxIterations model]
        finalModel = foldl (\m _ -> kMeansIteration m samples) model iterations
    in finalModel

kMeansIteration :: KMeans -> [Sample] -> KMeans
kMeansIteration model samples = 
    let -- 分配样本到最近的质心
        assignedSamples = assignSamplesToCentroids samples (centroids model)
        
        -- 更新质心位置
        updatedCentroids = map (\centroid -> 
            updateCentroid centroid (assignedSamples centroid)
        ) (centroids model)
    in model { centroids = updatedCentroids }

assignSamplesToCentroids :: [Sample] -> [Centroid] -> Centroid -> [Sample]
assignSamplesToCentroids samples centroids centroid = 
    let distances = map (\sample -> 
        (sample, euclideanDistance (features sample) (position centroid))
    ) samples
        minDistance = minimum $ map snd distances
        closestSamples = map fst $ filter (\d -> snd d == minDistance) distances
    in closestSamples

euclideanDistance :: [Double] -> [Double] -> Double
euclideanDistance v1 v2 = 
    sqrt $ sum $ zipWith (\x y -> (x - y) ^ 2) v1 v2

updateCentroid :: Centroid -> [Sample] -> Centroid
updateCentroid centroid samples = 
    if null samples
    then centroid
    else 
        let featureCount = length (features (head samples))
            newPosition = map (\i -> 
                sum (map (\s -> features s !! i) samples) / fromIntegral (length samples)
            ) [0..featureCount - 1]
        in centroid { position = newPosition, assignedSamples = samples }
```

#### 主成分分析

```haskell
-- 主成分分析
data PrincipalComponentAnalysis = PrincipalComponentAnalysis {
    nComponents :: Int,
    components :: [Component],
    explainedVariance :: [Double]
}

data Component = Component {
    componentId :: String,
    eigenvector :: [Double],
    eigenvalue :: Double
}

-- PCA算法
principalComponentAnalysis :: [Sample] -> Int -> PrincipalComponentAnalysis
principalComponentAnalysis samples nComponents = 
    let -- 标准化数据
        standardizedData = standardizeData samples
        
        -- 计算协方差矩阵
        covarianceMatrix = computeCovarianceMatrix standardizedData
        
        -- 计算特征值和特征向量
        (eigenvalues, eigenvectors) = computeEigenDecomposition covarianceMatrix
        
        -- 选择前n个主成分
        selectedComponents = take nComponents $ zipWith (\i (eigenvalue, eigenvector) -> 
            Component (show i) eigenvector eigenvalue
        ) [1..] (zip eigenvalues eigenvectors)
        
        -- 计算解释方差
        totalVariance = sum eigenvalues
        explainedVariance = map (\c -> eigenvalue c / totalVariance) selectedComponents
    in PrincipalComponentAnalysis {
        nComponents = nComponents,
        components = selectedComponents,
        explainedVariance = explainedVariance
    }

-- 标准化数据
standardizeData :: [Sample] -> [[Double]]
standardizeData samples = 
    let features = map features samples
        featureCount = length (head features)
        
        -- 计算均值和标准差
        means = map (\i -> 
            sum (map (\f -> f !! i) features) / fromIntegral (length features)
        ) [0..featureCount - 1]
        
        stds = map (\i -> 
            let values = map (\f -> f !! i) features
                mean = means !! i
                variance = sum (map (\v -> (v - mean) ^ 2) values) / fromIntegral (length values)
            in sqrt variance
        ) [0..featureCount - 1]
        
        -- 标准化
        standardized = map (\sample -> 
            zipWith (\feature mean std -> (feature - mean) / std) 
                    (features sample) means stds
        ) samples
    in standardized

-- 计算协方差矩阵
computeCovarianceMatrix :: [[Double]] -> [[Double]]
computeCovarianceMatrix data_ = 
    let n = length data_
        p = length (head data_)
        
        -- 计算协方差矩阵
        covariance = map (\i -> 
            map (\j -> 
                let valuesI = map (\row -> row !! i) data_
                    valuesJ = map (\row -> row !! j) data_
                    meanI = sum valuesI / fromIntegral n
                    meanJ = sum valuesJ / fromIntegral n
                in sum (zipWith (\vi vj -> (vi - meanI) * (vj - meanJ)) valuesI valuesJ) / fromIntegral (n - 1)
            ) [0..p - 1]
        ) [0..p - 1]
    in covariance

-- 计算特征分解
computeEigenDecomposition :: [[Double]] -> ([Double], [[Double]])
computeEigenDecomposition matrix = 
    -- 简化实现：返回模拟的特征值和特征向量
    let n = length matrix
        eigenvalues = map (\i -> fromIntegral (n - i)) [0..n - 1]
        eigenvectors = map (\i -> 
            map (\j -> if i == j then 1.0 else 0.0) [0..n - 1]
        ) [0..n - 1]
    in (eigenvalues, eigenvectors)

-- 降维
reduceDimensions :: PrincipalComponentAnalysis -> [Sample] -> [Sample]
reduceDimensions pca samples = 
    let components = components pca
        transformedSamples = map (\sample -> 
            let transformedFeatures = map (\component -> 
                sum $ zipWith (*) (features sample) (eigenvector component)
            ) components
            in sample { features = transformedFeatures }
        ) samples
    in transformedSamples
```

### 强化学习

#### Q-learning

```haskell
-- Q-learning
data QLearning = QLearning {
    states :: [State],
    actions :: [Action],
    qTable :: QTable,
    learningRate :: Double,
    discountFactor :: Double,
    epsilon :: Double
}

data State = State {
    stateId :: String,
    features :: [Double]
}

data Action = Action {
    actionId :: String,
    description :: String
}

data QTable = QTable {
    values :: [(State, Action, Double)]
}

-- Q-learning算法
qLearning :: QLearning -> Environment -> Int -> QLearning
qLearning model environment episodes = 
    foldl (\m _ -> qLearningEpisode m environment) model [1..episodes]

-- Q-learning单次学习
qLearningEpisode :: QLearning -> Environment -> QLearning
qLearningEpisode model environment = 
    let initialState = getInitialState environment
        finalModel = qLearningStep model environment initialState
    in finalModel

qLearningStep :: QLearning -> Environment -> State -> QLearning
qLearningStep model environment currentState = 
    if isTerminalState currentState environment
    then model
    else 
        let -- 选择动作
            action = selectAction model currentState
            
            -- 执行动作
            (nextState, reward) = executeAction environment currentState action
            
            -- 更新Q值
            updatedModel = updateQValue model currentState action nextState reward
            
            -- 继续下一步
        in qLearningStep updatedModel environment nextState

-- 选择动作（ε-贪婪策略）
selectAction :: QLearning -> State -> Action
selectAction model state = 
    let randomValue = randomDouble 0 1
    in if randomValue < epsilon model
       then selectRandomAction model
       else selectBestAction model state

selectRandomAction :: QLearning -> Action
selectRandomAction model = 
    -- 简化实现
    head (actions model)

selectBestAction :: QLearning -> State -> Action
selectBestAction model state = 
    let qValues = getQValues model state
        maxQValue = maximum $ map snd qValues
        bestActions = map fst $ filter (\q -> snd q == maxQValue) qValues
    in head bestActions

getQValues :: QLearning -> State -> [(Action, Double)]
getQValues model state = 
    let relevantEntries = filter (\entry -> 
        fst3 entry == state
    ) (values (qTable model))
    in map (\entry -> (snd3 entry, thd3 entry)) relevantEntries

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

-- 更新Q值
updateQValue :: QLearning -> State -> Action -> State -> Double -> QLearning
updateQValue model state action nextState reward = 
    let currentQValue = getQValue model state action
        maxNextQValue = maximum $ map snd $ getQValues model nextState
        newQValue = currentQValue + learningRate model * 
                   (reward + discountFactor model * maxNextQValue - currentQValue)
        updatedQTable = updateQTable (qTable model) state action newQValue
    in model { qTable = updatedQTable }

getQValue :: QLearning -> State -> Action -> Double
getQValue model state action = 
    let entry = find (\entry -> 
        fst3 entry == state && snd3 entry == action
    ) (values (qTable model))
    in case entry of
        Just (_, _, value) -> value
        Nothing -> 0.0

updateQTable :: QTable -> State -> Action -> Double -> QTable
updateQTable qTable state action newValue = 
    let updatedValues = map (\entry -> 
        if fst3 entry == state && snd3 entry == action
        then (state, action, newValue)
        else entry
    ) (values qTable)
    in qTable { values = updatedValues }

-- 环境接口
data Environment = Environment {
    name :: String,
    getInitialState :: State,
    isTerminalState :: State -> Bool,
    executeAction :: State -> Action -> (State, Double)
}
```

## 🔧 Haskell实现示例

### 神经网络实现

```haskell
-- 神经网络
data NeuralNetwork = NeuralNetwork {
    layers :: [NeuralLayer],
    learningRate :: Double
}

data NeuralLayer = NeuralLayer {
    neurons :: [Neuron],
    activationFunction :: ActivationFunction
}

data Neuron = Neuron {
    weights :: [Double],
    bias :: Double,
    output :: Double,
    delta :: Double
}

-- 前向传播
forwardPropagation :: NeuralNetwork -> [Double] -> [Double]
forwardPropagation network input = 
    let outputs = foldl (\inputs layer -> 
        map (\neuron -> activateNeuron inputs neuron) (neurons layer)
    ) input (layers network)
    in outputs

activateNeuron :: [Double] -> Neuron -> Double
activateNeuron inputs neuron = 
    let weightedSum = sum $ zipWith (*) inputs (weights neuron) + bias neuron
    in applyActivationFunction weightedSum (activationFunction neuron)

applyActivationFunction :: Double -> ActivationFunction -> Double
applyActivationFunction x function = 
    case function of
        Sigmoid -> sigmoid x
        Tanh -> tanh x
        ReLU -> max 0 x
        Softmax -> x -- 简化实现
        Linear -> x

-- 反向传播
backwardPropagation :: NeuralNetwork -> [Double] -> [Double] -> NeuralNetwork
backwardPropagation network input target = 
    let -- 前向传播
        outputs = forwardPropagation network input
        
        -- 计算输出层误差
        outputLayer = last (layers network)
        outputErrors = zipWith (\output target -> output - target) outputs target
        
        -- 反向传播误差
        updatedNetwork = propagateErrors network outputErrors
        
        -- 更新权重
        finalNetwork = updateWeights updatedNetwork input
    in finalNetwork

propagateErrors :: NeuralNetwork -> [Double] -> NeuralNetwork
propagateErrors network errors = 
    -- 简化实现
    network

updateWeights :: NeuralNetwork -> [Double] -> NeuralNetwork
updateWeights network input = 
    -- 简化实现
    network
```

### 决策树实现

```haskell
-- 决策树
data DecisionTree = 
    Leaf String |
    Node String Double DecisionTree DecisionTree

-- 构建决策树
buildDecisionTree :: [Sample] -> [String] -> DecisionTree
buildDecisionTree samples features = 
    if shouldStop samples
    then Leaf (majorityClass samples)
    else 
        let (bestFeature, bestThreshold) = findBestSplit samples features
            (leftSamples, rightSamples) = splitSamples samples bestFeature bestThreshold
            leftTree = buildDecisionTree leftSamples features
            rightTree = buildDecisionTree rightSamples features
        in Node bestFeature bestThreshold leftTree rightTree

shouldStop :: [Sample] -> Bool
shouldStop samples = 
    let classes = map (\s -> value (label s)) samples
        uniqueClasses = nub classes
    in length uniqueClasses == 1 || length samples < 5

majorityClass :: [Sample] -> String
majorityClass samples = 
    let classes = map (\s -> value (label s)) samples
        classCounts = map (\c -> (c, length $ filter (== c) classes)) (nub classes)
        maxCount = maximum $ map snd classCounts
        majorityClass = fst $ head $ filter (\cc -> snd cc == maxCount) classCounts
    in majorityClass

findBestSplit :: [Sample] -> [String] -> (String, Double)
findBestSplit samples features = 
    let splits = concatMap (\feature -> 
        map (\threshold -> (feature, threshold)) (generateThresholds samples feature)
    ) features
        bestSplit = maximumBy (\s1 s2 -> 
            compare (informationGain samples (fst s1) (snd s1)) 
                   (informationGain samples (fst s2) (snd s2))
        ) splits
    in bestSplit

generateThresholds :: [Sample] -> String -> [Double]
generateThresholds samples feature = 
    let featureIndex = findFeatureIndex feature samples
        values = map (\s -> features s !! featureIndex) samples
        sortedValues = sort values
    in map (\i -> sortedValues !! i) [0, length sortedValues `div` 4, length sortedValues `div` 2, 3 * length sortedValues `div` 4]

findFeatureIndex :: String -> [Sample] -> Int
findFeatureIndex feature samples = 
    -- 简化实现
    0

informationGain :: [Sample] -> String -> Double -> Double
informationGain samples feature threshold = 
    let (leftSamples, rightSamples) = splitSamples samples feature threshold
        parentEntropy = entropy samples
        leftEntropy = entropy leftSamples
        rightEntropy = entropy rightSamples
        leftWeight = fromIntegral (length leftSamples) / fromIntegral (length samples)
        rightWeight = fromIntegral (length rightSamples) / fromIntegral (length samples)
    in parentEntropy - leftWeight * leftEntropy - rightWeight * rightEntropy

entropy :: [Sample] -> Double
entropy samples = 
    let classes = map (\s -> value (label s)) samples
        classCounts = map (\c -> length $ filter (== c) classes) (nub classes)
        total = fromIntegral (length samples)
        probabilities = map (\count -> fromIntegral count / total) classCounts
    in -sum (map (\p -> p * log p) probabilities)

splitSamples :: [Sample] -> String -> Double -> ([Sample], [Sample])
splitSamples samples feature threshold = 
    let featureIndex = findFeatureIndex feature samples
        (left, right) = partition (\s -> features s !! featureIndex <= threshold) samples
    in (left, right)

-- 预测
predict :: DecisionTree -> [Double] -> String
predict tree features = 
    case tree of
        Leaf class_ -> class_
        Node feature threshold leftTree rightTree -> 
            let featureIndex = 0 -- 简化实现
                featureValue = features !! featureIndex
            in if featureValue <= threshold
               then predict leftTree features
               else predict rightTree features
```

### 支持向量机实现

```haskell
-- 支持向量机
data SupportVectorMachine = SupportVectorMachine {
    supportVectors :: [Sample],
    alphas :: [Double],
    bias :: Double,
    kernel :: Kernel
}

data Kernel = 
    Linear |
    Polynomial Int |
    RBF Double

-- SVM训练
trainSVM :: [Sample] -> Kernel -> SupportVectorMachine
trainSVM samples kernel = 
    let -- 简化实现：使用线性SVM
        alphas = replicate (length samples) 0.1
        bias = 0.0
    in SupportVectorMachine {
        supportVectors = samples,
        alphas = alphas,
        bias = bias,
        kernel = kernel
    }

-- 核函数
kernelFunction :: Kernel -> [Double] -> [Double] -> Double
kernelFunction kernel x1 x2 = 
    case kernel of
        Linear -> linearKernel x1 x2
        Polynomial degree -> polynomialKernel x1 x2 degree
        RBF gamma -> rbfKernel x1 x2 gamma

linearKernel :: [Double] -> [Double] -> Double
linearKernel x1 x2 = 
    sum $ zipWith (*) x1 x2

polynomialKernel :: [Double] -> [Double] -> Int -> Double
polynomialKernel x1 x2 degree = 
    (linearKernel x1 x2 + 1) ^ degree

rbfKernel :: [Double] -> [Double] -> Double -> Double
rbfKernel x1 x2 gamma = 
    let distance = euclideanDistance x1 x2
    in exp (-gamma * distance ^ 2)

-- SVM预测
predictSVM :: SupportVectorMachine -> [Double] -> Double
predictSVM svm features = 
    let kernelValues = map (\sv -> 
        kernelFunction (kernel svm) features (features sv)
    ) (supportVectors svm)
        weightedSum = sum $ zipWith (*) (alphas svm) kernelValues
    in weightedSum + bias svm
```

## 📊 形式化验证

### 学习理论

```haskell
-- 学习理论
data LearningTheory = LearningTheory {
    vcDimension :: Int,
    sampleComplexity :: Int,
    generalizationBound :: Double
}

-- VC维度
calculateVCDimension :: [Sample] -> Int
calculateVCDimension samples = 
    let featureCount = length (features (head samples))
    in featureCount + 1

-- 样本复杂度
calculateSampleComplexity :: Double -> Double -> Int -> Int
calculateSampleComplexity epsilon delta vcDimension = 
    let sampleSize = ceiling $ (1 / epsilon) * (log (1 / delta) + vcDimension * log (1 / epsilon))
    in sampleSize

-- 泛化界
calculateGeneralizationBound :: Int -> Int -> Double -> Double
calculateGeneralizationBound sampleSize vcDimension confidence = 
    let bound = sqrt $ (vcDimension * log sampleSize + log (1 / confidence)) / fromIntegral sampleSize
    in bound
```

### 模型验证

```haskell
-- 模型验证
data ModelValidation = ModelValidation {
    crossValidation :: CrossValidationResult,
    bootstrap :: BootstrapResult,
    holdout :: HoldoutResult
}

data CrossValidationResult = CrossValidationResult {
    folds :: Int,
    accuracies :: [Double],
    meanAccuracy :: Double,
    stdAccuracy :: Double
}

-- K折交叉验证
kFoldCrossValidation :: [Sample] -> Int -> (Sample -> String) -> CrossValidationResult
kFoldCrossValidation samples k predictor = 
    let folds = createFolds samples k
        accuracies = map (\fold -> 
            validateFold fold predictor
        ) folds
        meanAcc = sum accuracies / fromIntegral (length accuracies)
        stdAcc = sqrt $ sum (map (\acc -> (acc - meanAcc) ^ 2) accuracies) / fromIntegral (length accuracies)
    in CrossValidationResult {
        folds = k,
        accuracies = accuracies,
        meanAccuracy = meanAcc,
        stdAccuracy = stdAcc
    }

createFolds :: [Sample] -> Int -> [[Sample]]
createFolds samples k = 
    let foldSize = length samples `div` k
        folds = map (\i -> 
            take foldSize $ drop (i * foldSize) samples
        ) [0..k - 1]
    in folds

validateFold :: [Sample] -> (Sample -> String) -> Double
validateFold fold predictor = 
    let predictions = map predictor fold
        actuals = map (\s -> value (label s)) fold
        correct = length $ filter (\(p, a) -> p == a) (zip predictions actuals)
    in fromIntegral correct / fromIntegral (length fold)

data BootstrapResult = BootstrapResult {
    samples :: Int,
    accuracies :: [Double],
    confidenceInterval :: (Double, Double)
}

data HoldoutResult = HoldoutResult {
    trainingSize :: Int,
    testSize :: Int,
    accuracy :: Double
}
```

## 🎯 最佳实践

### 特征工程

```haskell
-- 特征工程
data FeatureEngineering = FeatureEngineering {
    scaling :: ScalingMethod,
    encoding :: EncodingMethod,
    selection :: SelectionMethod
}

data ScalingMethod = 
    StandardScaler |
    MinMaxScaler |
    RobustScaler

data EncodingMethod = 
    OneHotEncoding |
    LabelEncoding |
    TargetEncoding

data SelectionMethod = 
    VarianceThreshold |
    CorrelationFilter |
    MutualInformation

-- 特征缩放
scaleFeatures :: ScalingMethod -> [Sample] -> [Sample]
scaleFeatures method samples = 
    case method of
        StandardScaler -> standardScale samples
        MinMaxScaler -> minMaxScale samples
        RobustScaler -> robustScale samples

standardScale :: [Sample] -> [Sample]
standardScale samples = 
    let features = map features samples
        featureCount = length (head features)
        
        -- 计算均值和标准差
        means = map (\i -> 
            sum (map (\f -> f !! i) features) / fromIntegral (length features)
        ) [0..featureCount - 1]
        
        stds = map (\i -> 
            let values = map (\f -> f !! i) features
                mean = means !! i
                variance = sum (map (\v -> (v - mean) ^ 2) values) / fromIntegral (length values)
            in sqrt variance
        ) [0..featureCount - 1]
        
        -- 标准化
        scaledSamples = map (\sample -> 
            sample { features = zipWith (\feature mean std -> (feature - mean) / std) 
                                    (features sample) means stds }
        ) samples
    in scaledSamples

minMaxScale :: [Sample] -> [Sample]
minMaxScale samples = 
    let features = map features samples
        featureCount = length (head features)
        
        -- 计算最小值和最大值
        mins = map (\i -> 
            minimum $ map (\f -> f !! i) features
        ) [0..featureCount - 1]
        
        maxs = map (\i -> 
            maximum $ map (\f -> f !! i) features
        ) [0..featureCount - 1]
        
        -- 归一化
        scaledSamples = map (\sample -> 
            sample { features = zipWith3 (\feature min max -> (feature - min) / (max - min)) 
                                        (features sample) mins maxs }
        ) samples
    in scaledSamples

robustScale :: [Sample] -> [Sample]
robustScale samples = 
    -- 简化实现
    samples
```

### 超参数调优

```haskell
-- 超参数调优
data HyperparameterTuning = HyperparameterTuning {
    method :: TuningMethod,
    searchSpace :: SearchSpace,
    evaluation :: EvaluationMetric
}

data TuningMethod = 
    GridSearch |
    RandomSearch |
    BayesianOptimization

data SearchSpace = SearchSpace {
    parameters :: [ParameterRange]
}

data ParameterRange = ParameterRange {
    name :: String,
    type_ :: ParameterType,
    range :: (Double, Double),
    step :: Double
}

data ParameterType = 
    Continuous |
    Discrete |
    Categorical

data EvaluationMetric = 
    Accuracy |
    Precision |
    Recall |
    F1Score |
    RMSE

-- 网格搜索
gridSearch :: HyperparameterTuning -> [Sample] -> (Sample -> String) -> BestParameters
gridSearch tuning samples predictor = 
    let parameterCombinations = generateParameterCombinations (searchSpace tuning)
        results = map (\params -> 
            evaluateParameters params samples predictor
        ) parameterCombinations
        bestResult = maximumBy (\r1 r2 -> 
            compare (score r1) (score r2)
        ) results
    in bestResult

data BestParameters = BestParameters {
    parameters :: [(String, Double)],
    score :: Double
}

generateParameterCombinations :: SearchSpace -> [[(String, Double)]]
generateParameterCombinations searchSpace = 
    -- 简化实现
    [[("learning_rate", 0.1), ("epochs", 100)]]

evaluateParameters :: [(String, Double)] -> [Sample] -> (Sample -> String) -> BestParameters
evaluateParameters params samples predictor = 
    let accuracy = calculateAccuracy samples predictor
    in BestParameters {
        parameters = params,
        score = accuracy
    }

calculateAccuracy :: [Sample] -> (Sample -> String) -> Double
calculateAccuracy samples predictor = 
    let predictions = map predictor samples
        actuals = map (\s -> value (label s)) samples
        correct = length $ filter (\(p, a) -> p == a) (zip predictions actuals)
    in fromIntegral correct / fromIntegral (length samples)
```

## 🔗 相关链接

- [知识表示](./02-Knowledge-Representation.md)
- [推理系统](./03-Reasoning-Systems.md)
- [自然语言处理](./04-Natural-Language-Processing.md)
- [人工智能基础](../人工智能基础.md)

## 📚 参考文献

1. Mitchell, T. M. (1997). Machine learning. McGraw Hill.
2. Bishop, C. M. (2006). Pattern recognition and machine learning. Springer.
3. Sutton, R. S., & Barto, A. G. (2018). Reinforcement learning: An introduction. MIT press.
4. Goodfellow, I., Bengio, Y., & Courville, A. (2016). Deep learning. MIT press.

---

*本文档提供了机器学习的完整形式化理论框架和Haskell实现，为机器学习实践提供理论基础。* 