# 量化金融

## 概述

量化金融使用数学和统计方法来分析金融市场，进行投资决策和风险管理。本节将建立量化金融的形式化理论框架，并提供Haskell实现。

## 1. 金融模型基础

### 1.1 随机过程

**定义 1.1.1** (布朗运动)
布朗运动 $W_t$ 是一个连续时间随机过程，满足：

- $W_0 = 0$
- 增量独立：$W_{t+s} - W_t$ 与 $W_t$ 独立
- 正态分布：$W_{t+s} - W_t \sim N(0, s)$

**Haskell实现**：

```haskell
-- | 布朗运动
data BrownianMotion = BrownianMotion
  { timeSteps :: [Double]
  , values :: [Double]
  , drift :: Double
  , volatility :: Double
  } deriving (Show, Eq)

-- | 生成布朗运动路径
generateBrownianMotion :: Double -> Double -> Double -> Int -> BrownianMotion
generateBrownianMotion drift volatility tFinal nSteps = 
  let dt = tFinal / fromIntegral nSteps
      timeSteps = [i * dt | i <- [0..nSteps]]
      increments = generateNormalIncrements 0.0 (sqrt dt) nSteps
      values = scanl (+) 0.0 increments
  in BrownianMotion timeSteps values drift volatility

-- | 生成正态分布增量
generateNormalIncrements :: Double -> Double -> Int -> [Double]
generateNormalIncrements mean std n = 
  take n $ randomRs (normal mean std) (mkStdGen 42)

-- | 正态分布随机数生成
normal :: Double -> Double -> Double
normal mean std = 
  let u1 = randomRIO (0, 1)
      u2 = randomRIO (0, 1)
      z0 = sqrt (-2 * log u1) * cos (2 * pi * u2)
  in mean + std * z0

-- | 几何布朗运动
data GeometricBrownianMotion = GeometricBrownianMotion
  { initialPrice :: Double
  , drift :: Double
  , volatility :: Double
  , timeSteps :: [Double]
  , prices :: [Double]
  } deriving (Show, Eq)

-- | 生成几何布朗运动
generateGBM :: Double -> Double -> Double -> Double -> Int -> GeometricBrownianMotion
generateGBM s0 mu sigma tFinal nSteps = 
  let dt = tFinal / fromIntegral nSteps
      timeSteps = [i * dt | i <- [0..nSteps]]
      brownianIncrements = generateBrownianMotion 0.0 1.0 tFinal nSteps
      prices = scanl (\s dw -> s * exp ((mu - 0.5 * sigma^2) * dt + sigma * dw)) 
                    s0 (tail (values brownianIncrements))
  in GeometricBrownianMotion s0 mu sigma timeSteps prices
```

### 1.2 期权定价模型

**定义 1.2.1** (Black-Scholes模型)
Black-Scholes期权定价公式：

$$C(S, t) = SN(d_1) - Ke^{-r(T-t)}N(d_2)$$

其中：
$$d_1 = \frac{\ln(S/K) + (r + \sigma^2/2)(T-t)}{\sigma\sqrt{T-t}}$$
$$d_2 = d_1 - \sigma\sqrt{T-t}$$

**Haskell实现**：

```haskell
-- | 期权类型
data OptionType = Call | Put
  deriving (Show, Eq)

-- | 期权参数
data OptionParams = OptionParams
  { spotPrice :: Double
  , strikePrice :: Double
  , timeToMaturity :: Double
  , riskFreeRate :: Double
  , volatility :: Double
  } deriving (Show, Eq)

-- | Black-Scholes定价
blackScholes :: OptionType -> OptionParams -> Double
blackScholes optionType params = 
  let s = spotPrice params
      k = strikePrice params
      t = timeToMaturity params
      r = riskFreeRate params
      sigma = volatility params
      
      d1 = (log (s / k) + (r + sigma^2 / 2) * t) / (sigma * sqrt t)
      d2 = d1 - sigma * sqrt t
      
      callPrice = s * normalCDF d1 - k * exp (-r * t) * normalCDF d2
      putPrice = k * exp (-r * t) * normalCDF (-d2) - s * normalCDF (-d1)
  in case optionType of
       Call -> callPrice
       Put -> putPrice

-- | 标准正态分布累积函数
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))
  where
    erf z = 2 / sqrt pi * integrate (\t -> exp (-t^2)) 0 z

-- | 数值积分
integrate :: (Double -> Double) -> Double -> Double -> Double
integrate f a b = 
  let n = 1000
      dx = (b - a) / fromIntegral n
      points = [a + i * dx | i <- [0..n]]
      values = map f points
  in dx * sum values / 2

-- | 期权Greeks
data OptionGreeks = OptionGreeks
  { delta :: Double
  , gamma :: Double
  , theta :: Double
  , vega :: Double
  , rho :: Double
  } deriving (Show, Eq)

-- | 计算期权Greeks
calculateGreeks :: OptionType -> OptionParams -> OptionGreeks
calculateGreeks optionType params = 
  let s = spotPrice params
      k = strikePrice params
      t = timeToMaturity params
      r = riskFreeRate params
      sigma = volatility params
      
      d1 = (log (s / k) + (r + sigma^2 / 2) * t) / (sigma * sqrt t)
      d2 = d1 - sigma * sqrt t
      
      delta = case optionType of
                Call -> normalCDF d1
                Put -> normalCDF d1 - 1
      
      gamma = normalPDF d1 / (s * sigma * sqrt t)
      
      theta = case optionType of
                Call -> -s * normalPDF d1 * sigma / (2 * sqrt t) - r * k * exp (-r * t) * normalCDF d2
                Put -> -s * normalPDF d1 * sigma / (2 * sqrt t) + r * k * exp (-r * t) * normalCDF (-d2)
      
      vega = s * normalPDF d1 * sqrt t
      
      rho = case optionType of
              Call -> k * t * exp (-r * t) * normalCDF d2
              Put -> -k * t * exp (-r * t) * normalCDF (-d2)
  in OptionGreeks delta gamma theta vega rho

-- | 标准正态分布概率密度函数
normalPDF :: Double -> Double
normalPDF x = exp (-x^2 / 2) / sqrt (2 * pi)
```

## 2. 风险管理

### 2.1 风险度量

**定义 2.1.1** (VaR - 风险价值)
VaR是在给定置信水平下，投资组合在特定时间内的最大可能损失：

$$VaR_\alpha = \inf\{l \in \mathbb{R}: P(L \leq l) \geq \alpha\}$$

**Haskell实现**：

```haskell
-- | 风险度量
data RiskMetrics = RiskMetrics
  { var :: Double
  , cvar :: Double
  , volatility :: Double
  , sharpeRatio :: Double
  } deriving (Show, Eq)

-- | 计算VaR
calculateVaR :: [Double] -> Double -> Double
calculateVaR returns confidenceLevel = 
  let sortedReturns = sort returns
      index = floor (confidenceLevel * fromIntegral (length returns))
  in sortedReturns !! index

-- | 计算CVaR (条件风险价值)
calculateCVaR :: [Double] -> Double -> Double
calculateCVaR returns confidenceLevel = 
  let var = calculateVaR returns confidenceLevel
      tailReturns = filter (<= var) returns
  in sum tailReturns / fromIntegral (length tailReturns)

-- | 计算波动率
calculateVolatility :: [Double] -> Double
calculateVolatility returns = 
  let mean = sum returns / fromIntegral (length returns)
      variance = sum [(r - mean)^2 | r <- returns] / fromIntegral (length returns - 1)
  in sqrt variance

-- | 计算夏普比率
calculateSharpeRatio :: [Double] -> Double -> Double
calculateSharpeRatio returns riskFreeRate = 
  let meanReturn = sum returns / fromIntegral (length returns)
      volatility = calculateVolatility returns
  in (meanReturn - riskFreeRate) / volatility

-- | 投资组合风险分析
data Portfolio = Portfolio
  { weights :: [Double]
  , returns :: [[Double]]
  , riskMetrics :: RiskMetrics
  } deriving (Show, Eq)

-- | 计算投资组合风险
calculatePortfolioRisk :: Portfolio -> RiskMetrics
calculatePortfolioRisk portfolio = 
  let portfolioReturns = calculatePortfolioReturns portfolio
      var = calculateVaR portfolioReturns 0.05  -- 95% VaR
      cvar = calculateCVaR portfolioReturns 0.05
      volatility = calculateVolatility portfolioReturns
      sharpeRatio = calculateSharpeRatio portfolioReturns 0.02  -- 2% 无风险利率
  in RiskMetrics var cvar volatility sharpeRatio

-- | 计算投资组合收益
calculatePortfolioReturns :: Portfolio -> [Double]
calculatePortfolioReturns portfolio = 
  let nAssets = length (weights portfolio)
      nPeriods = length (head (returns portfolio))
      assetReturns = returns portfolio
  in [sum [weights portfolio !! i * assetReturns !! i !! t | i <- [0..nAssets-1]] 
      | t <- [0..nPeriods-1]]
```

### 2.2 投资组合优化

**定义 2.2.1** (马科维茨投资组合理论)
最小化投资组合风险，在给定收益目标下：

$$\min_w w^T \Sigma w$$
$$\text{s.t.} \quad w^T \mu = \mu_p$$
$$\quad \sum_i w_i = 1$$

**Haskell实现**：

```haskell
-- | 投资组合优化
data PortfolioOptimization = PortfolioOptimization
  { expectedReturns :: [Double]
  , covarianceMatrix :: [[Double]]
  , targetReturn :: Double
  } deriving (Show, Eq)

-- | 马科维茨优化
markowitzOptimization :: PortfolioOptimization -> [Double]
markowitzOptimization optimization = 
  let n = length (expectedReturns optimization)
      mu = expectedReturns optimization
      sigma = covarianceMatrix optimization
      target = targetReturn optimization
      
      -- 构建二次规划问题
      qp = QuadraticProgram
        { objectiveMatrix = sigma
        , objectiveVector = replicate n 0.0
        , constraintMatrix = [mu, replicate n 1.0]
        , constraintVector = [target, 1.0]
        , constraintTypes = [Equality, Equality]
        }
      
      solution = solveQuadraticProgram qp
  in solution

-- | 二次规划
data QuadraticProgram = QuadraticProgram
  { objectiveMatrix :: [[Double]]
  , objectiveVector :: [Double]
  , constraintMatrix :: [[Double]]
  , constraintVector :: [Double]
  , constraintTypes :: [ConstraintType]
  } deriving (Show, Eq)

data ConstraintType = Equality | Inequality
  deriving (Show, Eq)

-- | 求解二次规划
solveQuadraticProgram :: QuadraticProgram -> [Double]
solveQuadraticProgram qp = 
  let n = length (objectiveVector qp)
      -- 使用内点法求解
      initialPoint = replicate n (1.0 / fromIntegral n)
      solution = interiorPointMethod qp initialPoint
  in solution

-- | 内点法
interiorPointMethod :: QuadraticProgram -> [Double] -> [Double]
interiorPointMethod qp initial = 
  let tolerance = 1e-6
      maxIterations = 1000
      iterate = iterateStep qp
      convergence = iterateUntilConvergence iterate tolerance maxIterations
  in convergence initial

-- | 迭代步骤
iterateStep :: QuadraticProgram -> [Double] -> [Double]
iterateStep qp x = 
  let gradient = calculateGradient qp x
      hessian = calculateHessian qp x
      direction = solveLinearSystem hessian (map negate gradient)
      stepSize = calculateStepSize qp x direction
  in zipWith (+) x (map (* stepSize) direction)

-- | 计算梯度
calculateGradient :: QuadraticProgram -> [Double] -> [Double]
calculateGradient qp x = 
  let q = objectiveMatrix qp
      c = objectiveVector qp
  in zipWith (+) c (matrixVectorMultiply q x)

-- | 矩阵向量乘法
matrixVectorMultiply :: [[Double]] -> [Double] -> [Double]
matrixVectorMultiply matrix vector = 
  [sum [row !! i * vector !! i | i <- [0..length vector - 1]] | row <- matrix]
```

## 3. 算法交易

### 3.1 技术指标

**定义 3.1.1** (移动平均线)
简单移动平均线 (SMA)：

$$SMA_n = \frac{1}{n}\sum_{i=1}^n P_i$$

指数移动平均线 (EMA)：

$$EMA_t = \alpha P_t + (1-\alpha)EMA_{t-1}$$

**Haskell实现**：

```haskell
-- | 技术指标
data TechnicalIndicators = TechnicalIndicators
  { sma :: [Double]
  , ema :: [Double]
  , rsi :: [Double]
  , macd :: [Double]
  } deriving (Show, Eq)

-- | 计算简单移动平均线
calculateSMA :: [Double] -> Int -> [Double]
calculateSMA prices period = 
  let n = length prices
  in [sum (take period (drop i prices)) / fromIntegral period | i <- [0..n-period]]

-- | 计算指数移动平均线
calculateEMA :: [Double] -> Int -> [Double]
calculateEMA prices period = 
  let alpha = 2.0 / fromIntegral (period + 1)
      initialEMA = sum (take period prices) / fromIntegral period
      emaValues = scanl (\ema price -> alpha * price + (1 - alpha) * ema) 
                       initialEMA (drop period prices)
  in take period prices ++ emaValues

-- | 计算相对强弱指数 (RSI)
calculateRSI :: [Double] -> Int -> [Double]
calculateRSI prices period = 
  let returns = zipWith (-) (tail prices) prices
      gains = map (\r -> if r > 0 then r else 0) returns
      losses = map (\r -> if r < 0 then -r else 0) returns
      
      avgGains = calculateEMA gains period
      avgLosses = calculateEMA losses period
      
      rs = zipWith (/) avgGains avgLosses
      rsi = map (\r -> 100 - 100 / (1 + r)) rs
  in replicate period 50 ++ rsi  -- 初始值设为50

-- | 计算MACD
calculateMACD :: [Double] -> Int -> Int -> Int -> [Double]
calculateMACD prices fastPeriod slowPeriod signalPeriod = 
  let emaFast = calculateEMA prices fastPeriod
      emaSlow = calculateEMA prices slowPeriod
      macdLine = zipWith (-) emaFast emaSlow
      signalLine = calculateEMA macdLine signalPeriod
      histogram = zipWith (-) macdLine signalLine
  in histogram
```

### 3.2 交易策略

**定义 3.2.1** (交易策略)
交易策略是基于技术指标和价格模式生成买卖信号的算法。

**Haskell实现**：

```haskell
-- | 交易信号
data TradingSignal = Buy | Sell | Hold
  deriving (Show, Eq)

-- | 交易策略
data TradingStrategy = TradingStrategy
  { name :: String
  , parameters :: Map String Double
  , generateSignal :: [Double] -> TradingSignal
  } deriving (Show, Eq)

-- | 移动平均线交叉策略
movingAverageCrossover :: Int -> Int -> TradingStrategy
movingAverageCrossover shortPeriod longPeriod = TradingStrategy
  { name = "Moving Average Crossover"
  , parameters = Map.fromList [("shortPeriod", fromIntegral shortPeriod), 
                               ("longPeriod", fromIntegral longPeriod)]
  , generateSignal = \prices -> 
      let shortMA = calculateSMA prices shortPeriod
          longMA = calculateSMA prices longPeriod
          currentShort = last shortMA
          currentLong = last longMA
          previousShort = shortMA !! (length shortMA - 2)
          previousLong = longMA !! (length longMA - 2)
          
          currentCross = currentShort > currentLong
          previousCross = previousShort > previousLong
      in if currentCross && not previousCross
         then Buy
         else if not currentCross && previousCross
         then Sell
         else Hold
  }

-- | RSI策略
rsiStrategy :: Int -> Double -> Double -> TradingStrategy
rsiStrategy period oversold overbought = TradingStrategy
  { name = "RSI Strategy"
  , parameters = Map.fromList [("period", fromIntegral period), 
                               ("oversold", oversold), 
                               ("overbought", overbought)]
  , generateSignal = \prices -> 
      let rsi = calculateRSI prices period
          currentRSI = last rsi
          previousRSI = rsi !! (length rsi - 2)
      in if currentRSI < oversold && previousRSI >= oversold
         then Buy
         else if currentRSI > overbought && previousRSI <= overbought
         then Sell
         else Hold
  }

-- | 回测引擎
data BacktestEngine = BacktestEngine
  { strategy :: TradingStrategy
  , initialCapital :: Double
  , prices :: [Double]
  , positions :: [Int]
  , capital :: [Double]
  } deriving (Show, Eq)

-- | 运行回测
runBacktest :: TradingStrategy -> [Double] -> Double -> BacktestEngine
runBacktest strategy prices initialCapital = 
  let signals = map (\i -> generateSignal strategy (take (i+1) prices)) [0..length prices-1]
      positions = calculatePositions signals
      capital = calculateCapital positions prices initialCapital
  in BacktestEngine strategy initialCapital prices positions capital

-- | 计算持仓
calculatePositions :: [TradingSignal] -> [Int]
calculatePositions signals = 
  let initialPosition = 0
      updatePosition position signal = 
        case signal of
          Buy -> position + 1
          Sell -> position - 1
          Hold -> position
  in scanl updatePosition initialPosition signals

-- | 计算资金
calculateCapital :: [Int] -> [Double] -> Double -> [Double]
calculateCapital positions prices initialCapital = 
  let initialValue = initialCapital
      updateCapital (prevCapital, prevPosition) (position, price) = 
        let positionChange = position - prevPosition
            tradeValue = fromIntegral positionChange * price
            newCapital = prevCapital - tradeValue
        in (newCapital, position)
  in map fst $ scanl updateCapital (initialCapital, 0) (zip positions prices)
```

## 4. 机器学习在金融中的应用

### 4.1 预测模型

**定义 4.1.1** (时间序列预测)
使用机器学习模型预测金融时间序列的未来值。

**Haskell实现**：

```haskell
-- | 机器学习模型
data MLModel = LinearRegression [Double]
             | RandomForest Int Int
             | NeuralNetwork [Int]
             deriving (Show, Eq)

-- | 特征工程
data FeatureEngineering = FeatureEngineering
  { technicalFeatures :: [String]
  , fundamentalFeatures :: [String]
  , marketFeatures :: [String]
  } deriving (Show, Eq)

-- | 创建技术特征
createTechnicalFeatures :: [Double] -> [[Double]]
createTechnicalFeatures prices = 
  let returns = calculateReturns prices
      sma5 = calculateSMA prices 5
      sma20 = calculateSMA prices 20
      rsi = calculateRSI prices 14
      volatility = calculateRollingVolatility returns 20
  in [returns, sma5, sma20, rsi, volatility]

-- | 计算收益率
calculateReturns :: [Double] -> [Double]
calculateReturns prices = 
  zipWith (\p1 p2 -> (p1 - p2) / p2) (tail prices) prices

-- | 计算滚动波动率
calculateRollingVolatility :: [Double] -> Int -> [Double]
calculateRollingVolatility returns period = 
  let n = length returns
  in [calculateVolatility (take period (drop i returns)) | i <- [0..n-period]]

-- | 线性回归预测
linearRegressionPredict :: [Double] -> [Double] -> [Double] -> Double
linearRegressionPredict x y newX = 
  let coefficients = fitLinearRegression x y
  in sum (zipWith (*) coefficients newX)

-- | 拟合线性回归
fitLinearRegression :: [Double] -> [Double] -> [Double]
fitLinearRegression x y = 
  let n = length x
      xMean = sum x / fromIntegral n
      yMean = sum y / fromIntegral n
      
      numerator = sum [(x !! i - xMean) * (y !! i - yMean) | i <- [0..n-1]]
      denominator = sum [(x !! i - xMean)^2 | i <- [0..n-1]]
      
      slope = numerator / denominator
      intercept = yMean - slope * xMean
  in [intercept, slope]

-- | 随机森林预测
randomForestPredict :: RandomForest -> [[Double]] -> [Double] -> Double
randomForestPredict (RandomForest nTrees maxDepth) features target = 
  let trees = replicate nTrees (buildDecisionTree features target maxDepth)
      predictions = map (\tree -> predictTree tree features) trees
  in sum predictions / fromIntegral nTrees

-- | 决策树
data DecisionTree = Leaf Double
                  | Node Int Double DecisionTree DecisionTree
                  deriving (Show, Eq)

-- | 构建决策树
buildDecisionTree :: [[Double]] -> [Double] -> Int -> DecisionTree
buildDecisionTree features target maxDepth = 
  if maxDepth <= 0 || length target <= 1
  then Leaf (sum target / fromIntegral (length target))
  else
    let bestSplit = findBestSplit features target
    in case bestSplit of
         Nothing -> Leaf (sum target / fromIntegral (length target))
         Just (featureIndex, threshold, leftIndices, rightIndices) ->
           let leftFeatures = [features !! i | i <- leftIndices]
               leftTarget = [target !! i | i <- leftIndices]
               rightFeatures = [features !! i | i <- rightIndices]
               rightTarget = [target !! i | i <- rightIndices]
               
               leftTree = buildDecisionTree leftFeatures leftTarget (maxDepth - 1)
               rightTree = buildDecisionTree rightFeatures rightTarget (maxDepth - 1)
           in Node featureIndex threshold leftTree rightTree

-- | 预测决策树
predictTree :: DecisionTree -> [Double] -> Double
predictTree tree features = 
  case tree of
    Leaf value -> value
    Node featureIndex threshold leftTree rightTree ->
      let featureValue = features !! featureIndex
      in if featureValue <= threshold
         then predictTree leftTree features
         else predictTree rightTree features
```

### 4.2 风险管理模型

**定义 4.2.1** (信用风险模型)
使用机器学习评估借款人的信用风险。

**Haskell实现**：

```haskell
-- | 信用风险模型
data CreditRiskModel = CreditRiskModel
  { features :: [String]
  , model :: MLModel
  , threshold :: Double
  } deriving (Show, Eq)

-- | 借款人特征
data BorrowerFeatures = BorrowerFeatures
  { income :: Double
  , age :: Int
  , creditScore :: Int
  , debtToIncome :: Double
  , employmentYears :: Int
  } deriving (Show, Eq)

-- | 信用评分
data CreditScore = CreditScore
  { borrowerId :: String
  , score :: Double
  , riskLevel :: RiskLevel
  } deriving (Show, Eq)

data RiskLevel = Low | Medium | High
  deriving (Show, Eq)

-- | 计算信用评分
calculateCreditScore :: CreditRiskModel -> BorrowerFeatures -> CreditScore
calculateCreditScore model features = 
  let featureVector = extractFeatures features
      rawScore = predictModel model featureVector
      normalizedScore = normalizeScore rawScore
      riskLevel = classifyRisk normalizedScore
  in CreditScore "borrower123" normalizedScore riskLevel

-- | 提取特征
extractFeatures :: BorrowerFeatures -> [Double]
extractFeatures features = 
  [income features
  , fromIntegral (age features)
  , fromIntegral (creditScore features)
  , debtToIncome features
  , fromIntegral (employmentYears features)
  ]

-- | 预测模型
predictModel :: CreditRiskModel -> [Double] -> Double
predictModel model features = 
  case model of
    LinearRegression coefficients -> 
      sum (zipWith (*) coefficients (1.0 : features))
    RandomForest nTrees maxDepth -> 
      randomForestPredict (RandomForest nTrees maxDepth) [features] [0.0]
    NeuralNetwork layers -> 
      neuralNetworkPredict (NeuralNetwork layers) features

-- | 标准化评分
normalizeScore :: Double -> Double
normalizeScore score = 
  let minScore = 300.0
      maxScore = 850.0
  in min maxScore (max minScore score)

-- | 风险分类
classifyRisk :: Double -> RiskLevel
classifyRisk score = 
  if score >= 700
  then Low
  else if score >= 600
  then Medium
  else High

-- | 神经网络预测
neuralNetworkPredict :: NeuralNetwork -> [Double] -> Double
neuralNetworkPredict (NeuralNetwork layers) input = 
  let forwardPass = foldl forwardLayer input layers
  in last forwardPass

-- | 前向传播
forwardLayer :: [Double] -> Int -> [Double]
forwardLayer input layerSize = 
  let weights = replicate layerSize (replicate (length input) 0.1)  -- 简化权重
      biases = replicate layerSize 0.0
      outputs = [sum (zipWith (*) input weights !! i) + biases !! i | i <- [0..layerSize-1]]
  in map sigmoid outputs

-- | Sigmoid激活函数
sigmoid :: Double -> Double
sigmoid x = 1.0 / (1.0 + exp (-x))
```

## 5. 高频交易

### 5.1 市场微观结构

**定义 5.1.1** (订单簿)
订单簿记录了所有未成交的买卖订单。

**Haskell实现**：

```haskell
-- | 订单类型
data OrderType = Market | Limit
  deriving (Show, Eq)

data OrderSide = Buy | Sell
  deriving (Show, Eq)

-- | 订单
data Order = Order
  { orderId :: String
  , side :: OrderSide
  , orderType :: OrderType
  , price :: Double
  , quantity :: Int
  , timestamp :: UTCTime
  } deriving (Show, Eq)

-- | 订单簿
data OrderBook = OrderBook
  { bids :: [(Double, Int)]  -- (price, quantity)
  , asks :: [(Double, Int)]
  , lastPrice :: Double
  , spread :: Double
  } deriving (Show, Eq)

-- | 更新订单簿
updateOrderBook :: OrderBook -> Order -> OrderBook
updateOrderBook book order = 
  case side order of
    Buy -> 
      let newBids = insertOrder (bids book) (price order) (quantity order)
      in book { bids = newBids, spread = calculateSpread newBids (asks book) }
    Sell -> 
      let newAsks = insertOrder (asks book) (price order) (quantity order)
      in book { asks = newAsks, spread = calculateSpread (bids book) newAsks }

-- | 插入订单
insertOrder :: [(Double, Int)] -> Double -> Int -> [(Double, Int)]
insertOrder orders price quantity = 
  let existing = lookup price orders
  in case existing of
       Just existingQty -> 
         let newQuantity = existingQty + quantity
             otherOrders = filter (\(p, _) -> p /= price) orders
         in if newQuantity > 0
            then (price, newQuantity) : otherOrders
            else otherOrders
       Nothing -> 
         if quantity > 0
         then (price, quantity) : orders
         else orders

-- | 计算买卖价差
calculateSpread :: [(Double, Int)] -> [(Double, Int)] -> Double
calculateSpread bids asks = 
  case (bids, asks) of
    ((bidPrice, _):_, (askPrice, _):_) -> askPrice - bidPrice
    _ -> 0.0

-- | 高频交易策略
data HighFrequencyStrategy = HighFrequencyStrategy
  { name :: String
  , latency :: Int  -- 微秒
  , algorithm :: OrderBook -> [Order]
  } deriving (Show, Eq)

-- | 做市商策略
marketMakerStrategy :: HighFrequencyStrategy
marketMakerStrategy = HighFrequencyStrategy
  { name = "Market Maker"
  , latency = 10  -- 10微秒
  , algorithm = \orderBook -> 
      let bidPrice = fst (head (bids orderBook))
          askPrice = fst (head (asks orderBook))
          midPrice = (bidPrice + askPrice) / 2
          spread = askPrice - bidPrice
          
          newBidPrice = midPrice - spread * 0.1
          newAskPrice = midPrice + spread * 0.1
          
          bidOrder = Order "bid1" Buy Limit newBidPrice 100 (utcNow)
          askOrder = Order "ask1" Sell Limit newAskPrice 100 (utcNow)
      in [bidOrder, askOrder]
  }

-- | 统计套利策略
statisticalArbitrageStrategy :: HighFrequencyStrategy
statisticalArbitrageStrategy = HighFrequencyStrategy
  { name = "Statistical Arbitrage"
  , latency = 5  -- 5微秒
  , algorithm = \orderBook -> 
      let spread = spread orderBook
          avgSpread = 0.01  -- 历史平均价差
          
          orders = if spread > avgSpread * 1.5
                   then [Order "arb1" Sell Market 0 100 (utcNow)]
                   else if spread < avgSpread * 0.5
                   then [Order "arb2" Buy Market 0 100 (utcNow)]
                   else []
      in orders
  }
```

## 6. 总结

量化金融提供了系统化的方法来分析金融市场和进行投资决策。通过形式化建模和Haskell实现，我们可以：

1. **建立金融模型**：理解价格动态和风险因素
2. **管理投资风险**：计算VaR、CVaR等风险度量
3. **优化投资组合**：实现马科维茨投资组合理论
4. **开发交易策略**：基于技术指标和机器学习
5. **高频交易**：利用市场微观结构进行快速交易

这些理论和方法在资产管理、风险管理、算法交易等领域都有重要应用。

---

**参考文献**：

1. Hull, J. C. (2018). Options, Futures, and Other Derivatives. Pearson.
2. Markowitz, H. (1952). Portfolio Selection. Journal of Finance, 7(1), 77-91.
3. Murphy, J. J. (1999). Technical Analysis of the Financial Markets. New York Institute of Finance.
