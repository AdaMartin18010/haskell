# 网络动力学

## 概述

网络动力学研究网络中节点和边的动态变化过程，包括网络演化、信息传播、同步现象等。本节将建立网络动力学的形式化理论框架，并提供Haskell实现。

## 1. 网络演化模型

### 1.1 随机图模型

#### 1.1.1 Erdős-Rényi模型

**定义 1.1.1** (Erdős-Rényi随机图)
设 $G(n,p)$ 为 $n$ 个节点的随机图，每条边以概率 $p$ 独立存在：

$$P(G) = p^{|E|}(1-p)^{\binom{n}{2}-|E|}$$

**Haskell实现**：

```haskell
-- | Erdős-Rényi随机图模型
data ERGraph = ERGraph 
  { nodes :: Int
  , probability :: Double
  , edges :: [(Int, Int)]
  } deriving (Show, Eq)

-- | 生成Erdős-Rényi随机图
generateERGraph :: Int -> Double -> IO ERGraph
generateERGraph n p = do
  edges <- filterM (\_ -> randomIO < p) [(i,j) | i <- [0..n-1], j <- [i+1..n-1]]
  return $ ERGraph n p edges

-- | 计算图的密度
graphDensity :: ERGraph -> Double
graphDensity g = fromIntegral (length (edges g)) / fromIntegral (choose (nodes g) 2)
  where
    choose n k = product [n-k+1..n] `div` product [1..k]

-- | 计算平均度
averageDegree :: ERGraph -> Double
averageDegree g = 2.0 * fromIntegral (length (edges g)) / fromIntegral (nodes g)
```

#### 1.1.2 小世界网络模型

**定义 1.1.2** (小世界网络)
小世界网络具有高聚类系数和短平均路径长度的特征：

$$C \gg C_{random}, L \approx L_{random}$$

**Haskell实现**：

```haskell
-- | 小世界网络模型
data SmallWorldGraph = SmallWorldGraph
  { nodes :: Int
  , k :: Int  -- 每个节点的邻居数
  , p :: Double  -- 重连概率
  , edges :: [(Int, Int)]
  } deriving (Show, Eq)

-- | 生成小世界网络
generateSmallWorld :: Int -> Int -> Double -> SmallWorldGraph
generateSmallWorld n k p = SmallWorldGraph n k p edges
  where
    -- 初始环形网络
    ringEdges = [(i, (i+j) `mod` n) | i <- [0..n-1], j <- [1..k`div`2]]
    -- 随机重连
    edges = rewireEdges ringEdges p

-- | 重连边
rewireEdges :: [(Int, Int)] -> Double -> [(Int, Int)]
rewireEdges edges p = map rewireEdge edges
  where
    rewireEdge (u, v) = if randomIO < p then (u, randomNode) else (u, v)
    randomNode = randomRIO (0, n-1)
```

### 1.2 无标度网络模型

#### 1.2.1 Barabási-Albert模型

**定义 1.2.1** (优先连接)
新节点连接到现有节点的概率与节点的度成正比：

$$P(i) = \frac{k_i}{\sum_j k_j}$$

**Haskell实现**：

```haskell
-- | Barabási-Albert无标度网络
data BAGraph = BAGraph
  { nodes :: Int
  , m :: Int  -- 每次添加的边数
  , degrees :: Map Int Int
  , edges :: [(Int, Int)]
  } deriving (Show, Eq)

-- | 生成Barabási-Albert网络
generateBAGraph :: Int -> Int -> BAGraph
generateBAGraph n m = BAGraph n m degrees edges
  where
    -- 初始完全图
    initialNodes = [0..m]
    initialEdges = [(i,j) | i <- initialNodes, j <- [i+1..m]]
    initialDegrees = Map.fromList [(i, m) | i <- initialNodes]
    
    -- 逐步添加节点
    (degrees, edges) = foldl addNode (initialDegrees, initialEdges) [m+1..n-1]

-- | 添加新节点
addNode :: (Map Int Int, [(Int, Int)]) -> Int -> (Map Int Int, [(Int, Int)])
addNode (degrees, edges) newNode = (newDegrees, newEdges)
  where
    -- 选择连接目标
    targets = selectTargets degrees m
    -- 更新度和边
    newDegrees = foldl (\deg target -> Map.insertWith (+) target 1 deg) 
                      (Map.insert newNode m degrees) targets
    newEdges = edges ++ [(newNode, target) | target <- targets]

-- | 根据优先连接选择目标节点
selectTargets :: Map Int Int -> Int -> [Int]
selectTargets degrees m = take m $ map fst $ sortBy (flip compare `on` snd) 
                         $ Map.toList degrees
```

## 2. 传播动力学

### 2.1 SIR传播模型

**定义 2.1.1** (SIR模型)
SIR模型将人群分为三类：

- **S** (Susceptible): 易感者
- **I** (Infected): 感染者  
- **R** (Recovered): 康复者

**微分方程**：
$$\frac{dS}{dt} = -\beta SI$$
$$\frac{dI}{dt} = \beta SI - \gamma I$$
$$\frac{dR}{dt} = \gamma I$$

**Haskell实现**：

```haskell
-- | SIR传播模型
data SIRState = SIRState
  { susceptible :: Double
  , infected :: Double
  , recovered :: Double
  , time :: Double
  } deriving (Show, Eq)

-- | SIR参数
data SIRParams = SIRParams
  { beta :: Double  -- 传播率
  , gamma :: Double  -- 康复率
  } deriving (Show, Eq)

-- | SIR动力学方程
sirDynamics :: SIRParams -> SIRState -> SIRState
sirDynamics params state = SIRState
  { susceptible = s - beta params * s * i * dt
  , infected = i + (beta params * s * i - gamma params * i) * dt
  , recovered = r + gamma params * i * dt
  , time = t + dt
  }
  where
    s = susceptible state
    i = infected state
    r = recovered state
    t = time state
    dt = 0.01

-- | 模拟SIR传播
simulateSIR :: SIRParams -> SIRState -> Int -> [SIRState]
simulateSIR params initialState steps = 
  take steps $ iterate (sirDynamics params) initialState
```

### 2.2 网络上的传播

**定义 2.2.1** (网络传播阈值)
在网络上，传播阈值与网络结构相关：

$$R_0 = \frac{\beta}{\gamma} \cdot \frac{\langle k^2 \rangle}{\langle k \rangle}$$

**Haskell实现**：

```haskell
-- | 网络传播模型
data NetworkSIR = NetworkSIR
  { graph :: [(Int, Int)]
  , nodeStates :: Map Int NodeState
  , params :: SIRParams
  } deriving (Show, Eq)

data NodeState = Susceptible | Infected | Recovered
  deriving (Show, Eq, Enum)

-- | 网络传播步进
networkSIRStep :: NetworkSIR -> IO NetworkSIR
networkSIRStep sir = do
  -- 传播阶段
  newStates1 <- propagateInfection sir
  -- 康复阶段
  newStates2 <- recoveryProcess sir { nodeStates = newStates1 }
  return sir { nodeStates = newStates2 }

-- | 传播过程
propagateInfection :: NetworkSIR -> IO (Map Int NodeState)
propagateInfection sir = do
  let infectedNodes = Map.keys $ Map.filter (== Infected) (nodeStates sir)
  newInfections <- forM infectedNodes $ \node -> do
    let neighbors = getNeighbors node (graph sir)
    forM neighbors $ \neighbor -> do
      case Map.lookup neighbor (nodeStates sir) of
        Just Susceptible -> do
          shouldInfect <- randomIO < beta (params sir)
          return (neighbor, if shouldInfect then Infected else Susceptible)
        _ -> return (neighbor, nodeStates sir Map.! neighbor)
  return $ Map.union (nodeStates sir) (Map.fromList $ concat newInfections)

-- | 康复过程
recoveryProcess :: NetworkSIR -> IO (Map Int NodeState)
recoveryProcess sir = do
  let infectedNodes = Map.keys $ Map.filter (== Infected) (nodeStates sir)
  recoveries <- forM infectedNodes $ \node -> do
    shouldRecover <- randomIO < gamma (params sir)
    return (node, if shouldRecover then Recovered else Infected)
  return $ Map.union (nodeStates sir) (Map.fromList recoveries)
```

## 3. 同步现象

### 3.1 Kuramoto模型

**定义 3.1.1** (Kuramoto振荡器)
Kuramoto模型描述耦合振荡器的同步：

$$\frac{d\theta_i}{dt} = \omega_i + \frac{K}{N}\sum_{j=1}^N \sin(\theta_j - \theta_i)$$

**Haskell实现**：

```haskell
-- | Kuramoto振荡器
data KuramotoOscillator = KuramotoOscillator
  { phase :: Double
  , frequency :: Double
  } deriving (Show, Eq)

-- | Kuramoto系统
data KuramotoSystem = KuramotoSystem
  { oscillators :: [KuramotoOscillator]
  , coupling :: Double
  , adjacency :: [[Bool]]
  } deriving (Show, Eq)

-- | Kuramoto动力学
kuramotoDynamics :: KuramotoSystem -> [Double]
kuramotoDynamics system = map updatePhase [0..n-1]
  where
    n = length (oscillators system)
    phases = map phase (oscillators system)
    frequencies = map frequency (oscillators system)
    k = coupling system
    adj = adjacency system
    
    updatePhase i = frequencies !! i + 
                   k / fromIntegral n * 
                   sum [sin (phases !! j - phases !! i) | j <- [0..n-1], adj !! i !! j]

-- | 计算同步参数
synchronizationParameter :: KuramotoSystem -> Double
synchronizationParameter system = magnitude $ sum [cis phase | phase <- phases] / fromIntegral n
  where
    phases = map phase (oscillators system)
    n = length phases
```

### 3.2 同步阈值

**定理 3.2.1** (同步阈值)
对于全连接网络，同步阈值为：

$$K_c = \frac{2}{\pi g(0)}$$

其中 $g(\omega)$ 是频率分布函数。

**Haskell实现**：

```haskell
-- | 计算同步阈值
synchronizationThreshold :: [Double] -> Double
synchronizationThreshold frequencies = 2.0 / (pi * g0)
  where
    -- 频率分布函数在0处的值
    g0 = frequencyDensityAtZero frequencies

-- | 频率分布密度
frequencyDensityAtZero :: [Double] -> Double
frequencyDensityAtZero freqs = 
  let n = length freqs
      bandwidth = 0.1  -- 核密度估计带宽
      kernel x = exp (-x^2 / (2 * bandwidth^2)) / sqrt (2 * pi * bandwidth^2)
  in sum [kernel freq | freq <- freqs] / fromIntegral n
```

## 4. 网络稳定性

### 4.1 鲁棒性分析

**定义 4.1.1** (网络鲁棒性)
网络鲁棒性衡量网络在节点或边失效时的连通性保持能力。

**Haskell实现**：

```haskell
-- | 网络鲁棒性分析
data RobustnessAnalysis = RobustnessAnalysis
  { originalGraph :: [(Int, Int)]
  , attackStrategy :: AttackStrategy
  , failureSequence :: [Int]
  } deriving (Show, Eq)

data AttackStrategy = RandomAttack | TargetedAttack | CascadingFailure
  deriving (Show, Eq)

-- | 计算网络鲁棒性
networkRobustness :: [(Int, Int)] -> AttackStrategy -> Double
networkRobustness graph strategy = 
  let n = maximum [max u v | (u,v) <- graph] + 1
      failureSteps = [1..n]
      robustnessCurve = map (\k -> 
        let failedNodes = take k (generateFailureSequence graph strategy)
            remainingGraph = removeNodes graph failedNodes
        in largestComponentSize remainingGraph / fromIntegral n) failureSteps
  in sum robustnessCurve / fromIntegral n

-- | 生成失效序列
generateFailureSequence :: [(Int, Int)] -> AttackStrategy -> [Int]
generateFailureSequence graph strategy = case strategy of
  RandomAttack -> randomPermutation [0..n-1]
  TargetedAttack -> sortBy (flip compare `on` degree) [0..n-1]
  CascadingFailure -> simulateCascadingFailure graph
  where
    n = maximum [max u v | (u,v) <- graph] + 1
    degree node = length [v | (u,v) <- graph, u == node || v == node]

-- | 最大连通分量大小
largestComponentSize :: [(Int, Int)] -> Int
largestComponentSize graph = maximum $ map length $ connectedComponents graph
```

### 4.2 级联失效

**定义 4.2.1** (级联失效)
级联失效是指网络中一个节点的失效导致其他节点相继失效的过程。

**Haskell实现**：

```haskell
-- | 级联失效模型
data CascadingFailure = CascadingFailure
  { graph :: [(Int, Int)]
  , nodeLoads :: Map Int Double
  , nodeCapacities :: Map Int Double
  , failedNodes :: Set Int
  } deriving (Show, Eq)

-- | 模拟级联失效
simulateCascadingFailure :: [(Int, Int)] -> [Int]
simulateCascadingFailure graph = 
  let initialLoads = calculateInitialLoads graph
      initialCapacities = Map.map (* 1.5) initialLoads  -- 容量为负载的1.5倍
      initial = CascadingFailure graph initialLoads initialCapacities Set.empty
  in unfoldr stepCascade initial

-- | 级联失效步进
stepCascade :: CascadingFailure -> Maybe (Int, CascadingFailure)
stepCascade cf = 
  let overloadedNodes = findOverloadedNodes cf
  in case overloadedNodes of
    [] -> Nothing
    (node:_) -> Just (node, redistributeLoad cf node)

-- | 重新分配负载
redistributeLoad :: CascadingFailure -> Int -> CascadingFailure
redistributeLoad cf failedNode = 
  let neighbors = getNeighbors failedNode (graph cf)
      failedLoad = nodeLoads cf Map.! failedNode
      loadPerNeighbor = failedLoad / fromIntegral (length neighbors)
      newLoads = foldl (\loads neighbor -> 
        Map.insertWith (+) neighbor loadPerNeighbor loads) 
        (nodeLoads cf) neighbors
  in cf { nodeLoads = newLoads
        , failedNodes = Set.insert failedNode (failedNodes cf) }
```

## 5. 网络控制

### 5.1 可控性理论

**定义 5.1.1** (网络可控性)
网络可控性研究通过控制少数节点来驱动整个网络达到期望状态的能力。

**Haskell实现**：

```haskell
-- | 网络可控性分析
data ControllabilityAnalysis = ControllabilityAnalysis
  { adjacencyMatrix :: [[Double]]
  , controlNodes :: [Int]
  , controllabilityMatrix :: [[Double]]
  } deriving (Show, Eq)

-- | 计算可控性矩阵
controllabilityMatrix :: [[Double]] -> [Int] -> [[Double]]
controllabilityMatrix adj controlNodes = 
  let n = length adj
      b = controlInputMatrix n controlNodes
      kalman = kalmanControllabilityMatrix adj b
  in kalman

-- | 控制输入矩阵
controlInputMatrix :: Int -> [Int] -> [[Double]]
controlInputMatrix n controlNodes = 
  [[if i == j && i `elem` controlNodes then 1.0 else 0.0 | j <- [0..n-1]] | i <- [0..n-1]]

-- | Kalman可控性矩阵
kalmanControllabilityMatrix :: [[Double]] -> [[Double]] -> [[Double]]
kalmanControllabilityMatrix adj b = 
  let n = length adj
      powers = take n $ iterate (matrixMultiply adj) (identityMatrix n)
  in concatMap (\a -> matrixMultiply a b) powers

-- | 最小控制节点集
minimumControlNodes :: [[Double]] -> [Int]
minimumControlNodes adj = 
  let n = length adj
      maxMatch = maximumBipartiteMatching (bipartiteGraph adj)
  in [i | i <- [0..n-1], not (i `elem` maxMatch)]
```

### 5.2 最优控制

**定义 5.2.1** (最优控制)
最优控制寻找最小能量输入来驱动网络达到目标状态。

**Haskell实现**：

```haskell
-- | 最优控制问题
data OptimalControl = OptimalControl
  { system :: LinearSystem
  , targetState :: [Double]
  , timeHorizon :: Double
  , controlCost :: Double
  } deriving (Show, Eq)

data LinearSystem = LinearSystem
  { a :: [[Double]]  -- 系统矩阵
  , b :: [[Double]]  -- 控制矩阵
  } deriving (Show, Eq)

-- | 求解最优控制
solveOptimalControl :: OptimalControl -> [Double]
solveOptimalControl oc = 
  let riccati = solveRiccatiEquation (system oc) (timeHorizon oc)
      optimalGain = calculateOptimalGain riccati (system oc)
  in applyOptimalControl optimalGain (targetState oc)

-- | 求解Riccati方程
solveRiccatiEquation :: LinearSystem -> Double -> [[Double]]
solveRiccatiEquation sys t = 
  -- 使用数值方法求解Riccati微分方程
  let dt = 0.01
      steps = floor (t / dt)
      initialP = identityMatrix (length (a sys))
  in iterate (stepRiccati sys dt) initialP !! steps

-- | Riccati方程步进
stepRiccati :: LinearSystem -> Double -> [[Double]] -> [[Double]]
stepRiccati sys dt p = 
  let n = length (a sys)
      riccatiRHS = matrixAdd (matrixMultiply (a sys) p)
                             (matrixMultiply p (transpose (a sys)))
                             (matrixSubtract (matrixMultiply p (matrixMultiply (b sys) (transpose (b sys))) p)
                                            (identityMatrix n))
  in matrixAdd p (matrixScale dt riccatiRHS)
```

## 6. 应用实例

### 6.1 社交网络分析

**应用 6.1.1** (信息传播)
在社交网络中分析信息传播的动态过程。

```haskell
-- | 社交网络信息传播
data SocialNetwork = SocialNetwork
  { users :: [User]
  , connections :: [(Int, Int)]
  , information :: Map Int Information
  } deriving (Show, Eq)

data User = User
  { userId :: Int
  , influence :: Double
  , susceptibility :: Double
  } deriving (Show, Eq)

data Information = Information
  { content :: String
  , virality :: Double
  , lifetime :: Double
  } deriving (Show, Eq)

-- | 模拟信息传播
simulateInformationSpread :: SocialNetwork -> Int -> [SocialNetwork]
simulateInformationSpread network steps = 
  take steps $ iterate stepInformationSpread network

-- | 信息传播步进
stepInformationSpread :: SocialNetwork -> SocialNetwork
stepInformationSpread network = 
  let newInformation = Map.mapWithKey (\userId info -> 
    spreadInformation userId info network) (information network)
  in network { information = newInformation }

-- | 信息传播逻辑
spreadInformation :: Int -> Information -> SocialNetwork -> Information
spreadInformation userId info network = 
  let neighbors = getNeighbors userId (connections network)
      spreadProb = virality info * userInfluence userId network
  in if randomIO < spreadProb then info else info
```

### 6.2 生物网络分析

**应用 6.2.1** (蛋白质相互作用网络)
分析蛋白质相互作用网络的动力学特性。

```haskell
-- | 蛋白质相互作用网络
data ProteinNetwork = ProteinNetwork
  { proteins :: [Protein]
  , interactions :: [(Int, Int)]
  , expression :: Map Int Double
  } deriving (Show, Eq)

data Protein = Protein
  { proteinId :: Int
  , function :: String
  , regulation :: RegulationType
  } deriving (Show, Eq)

data RegulationType = Activator | Repressor | Neutral
  deriving (Show, Eq)

-- | 基因表达动力学
geneExpressionDynamics :: ProteinNetwork -> ProteinNetwork
geneExpressionDynamics network = 
  let newExpression = Map.mapWithKey (\proteinId expr -> 
    updateExpression proteinId expr network) (expression network)
  in network { expression = newExpression }

-- | 更新表达水平
updateExpression :: Int -> Double -> ProteinNetwork -> Double
updateExpression proteinId currentExpr network = 
  let neighbors = getNeighbors proteinId (interactions network)
      regulatoryEffect = sum [regulatoryInfluence neighborId network | neighborId <- neighbors]
      newExpr = currentExpr + 0.1 * regulatoryEffect
  in max 0.0 $ min 1.0 newExpr
```

## 7. 总结

网络动力学提供了理解复杂网络动态行为的强大工具。通过形式化建模和Haskell实现，我们可以：

1. **分析网络演化**：理解网络结构的形成和变化
2. **研究传播过程**：预测信息、疾病等在网络中的传播
3. **探索同步现象**：分析耦合系统的集体行为
4. **评估网络稳定性**：分析网络对失效的鲁棒性
5. **设计控制策略**：开发网络控制方法

这些理论和方法在社交网络、生物网络、技术网络等领域都有重要应用。

---

**参考文献**：

1. Newman, M. E. J. (2010). Networks: An Introduction. Oxford University Press.
2. Barrat, A., Barthélemy, M., & Vespignani, A. (2008). Dynamical Processes on Complex Networks. Cambridge University Press.
3. Strogatz, S. H. (2001). Exploring complex networks. Nature, 410(6825), 268-276.
