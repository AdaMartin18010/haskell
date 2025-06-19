# 网络动力学理论 (Network Dynamics Theory)

## 📋 文档信息

- **文档编号**: 04-12-02
- **所属层级**: 应用科学层 - 网络科学
- **创建时间**: 2024年12月19日
- **最后更新**: 2024年12月19日
- **文档状态**: 完成

---

## 🎯 概述

网络动力学研究网络结构随时间演化的规律，包括节点和边的动态变化、信息传播、同步现象等。本文档系统性地介绍网络演化模型、传播动力学、同步理论等核心概念。

## 📚 理论基础

### 1. 网络演化模型

#### 1.1 随机图模型

Erdős-Rényi随机图模型：

$$G(n,p) = \text{具有}n\text{个节点，每条边以概率}p\text{存在的图}$$

#### 1.2 优先连接模型

Barabási-Albert模型中的度分布：

$$P(k) \sim k^{-\gamma}$$

其中 $\gamma = 3$ 为幂律指数。

#### 1.3 小世界模型

Watts-Strogatz模型的聚类系数：

$$C(p) = C(0)(1-p)^3$$

其中 $p$ 是重连概率。

### 2. 传播动力学

#### 2.1 SIR模型

SIR传播模型的微分方程：

$$\frac{dS}{dt} = -\beta SI$$

$$\frac{dI}{dt} = \beta SI - \gamma I$$

$$\frac{dR}{dt} = \gamma I$$

其中 $\beta$ 是传播率，$\gamma$ 是恢复率。

#### 2.2 传播阈值

在随机网络中，传播阈值为：

$$T_c = \frac{\langle k \rangle}{\langle k^2 \rangle}$$

其中 $\langle k \rangle$ 是平均度，$\langle k^2 \rangle$ 是度的二阶矩。

### 3. 同步理论

#### 3.1 Kuramoto模型

Kuramoto同步模型的相位方程：

$$\frac{d\theta_i}{dt} = \omega_i + \frac{K}{N}\sum_{j=1}^{N} A_{ij}\sin(\theta_j - \theta_i)$$

其中 $\omega_i$ 是自然频率，$K$ 是耦合强度。

#### 3.2 同步序参量

同步序参量定义为：

$$r = \left|\frac{1}{N}\sum_{j=1}^{N} e^{i\theta_j}\right|$$

## 🔧 Haskell实现

### 1. 网络演化模型

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module NetworkScience.Dynamics where

import Data.Graph
import Data.List
import Data.Maybe
import Control.Monad.State
import System.Random
import Data.Vector (Vector)
import qualified Data.Vector as V

-- 网络节点
data NetworkNode = NetworkNode
  { nodeId :: Int
  , nodeDegree :: Int
  , nodeState :: NodeState
  } deriving Show

-- 节点状态
data NodeState = 
  Susceptible
  | Infected
  | Recovered
  | Active
  | Inactive
  deriving (Show, Eq)

-- 网络边
data NetworkEdge = NetworkEdge
  { sourceNode :: Int
  , targetNode :: Int
  , edgeWeight :: Double
  , edgeState :: EdgeState
  } deriving Show

-- 边状态
data EdgeState = 
  Active
  | Inactive
  | Temporary
  deriving (Show, Eq)

-- 动态网络
data DynamicNetwork = DynamicNetwork
  { nodes :: Vector NetworkNode
  , edges :: Vector NetworkEdge
  , time :: Double
  , evolutionRules :: [EvolutionRule]
  } deriving Show

-- 演化规则
data EvolutionRule = 
  PreferentialAttachment Double  -- 优先连接概率
  | RandomRewiring Double        -- 随机重连概率
  | NodeAddition Int             -- 节点添加
  | EdgeAddition Int             -- 边添加
  deriving Show

-- 创建随机图
createRandomGraph :: Int -> Double -> IO DynamicNetwork
createRandomGraph n p = do
  let nodes = V.fromList [NetworkNode i 0 Susceptible | i <- [0..n-1]]
      edges = createRandomEdges n p
  return $ DynamicNetwork nodes edges 0.0 []

-- 创建随机边
createRandomEdges :: Int -> Double -> Vector NetworkEdge
createRandomEdges n p = 
  let allPossibleEdges = [(i, j) | i <- [0..n-1], j <- [i+1..n-1]]
      edgeList = filter (\_ -> randomDouble < p) allPossibleEdges
      edges = [NetworkEdge i j 1.0 Active | (i, j) <- edgeList]
  in V.fromList edges
  where randomDouble = 0.5  -- 简化：固定概率

-- 优先连接模型
preferentialAttachment :: DynamicNetwork -> Int -> IO DynamicNetwork
preferentialAttachment network newNodeId = do
  let currentNodes = nodes network
      degrees = V.map nodeDegree currentNodes
      totalDegree = V.sum degrees
      
      -- 计算连接概率
      probabilities = V.map (\deg -> fromIntegral deg / fromIntegral totalDegree) degrees
      
      -- 选择连接目标
      targets = selectNodesByProbability probabilities 2
      
      -- 添加新边
      newEdges = [NetworkEdge newNodeId target 1.0 Active | target <- targets]
      
      -- 更新网络
      updatedNodes = V.snoc currentNodes (NetworkNode newNodeId 2 Susceptible)
      updatedEdges = V.concat [edges network, V.fromList newEdges]
  
  return $ network { nodes = updatedNodes, edges = updatedEdges }

-- 根据概率选择节点
selectNodesByProbability :: Vector Double -> Int -> [Int]
selectNodesByProbability probs count = 
  let cumulative = V.scanl (+) 0 probs
      total = V.last cumulative
      randomValues = [0.3, 0.7]  -- 简化：固定随机值
      selected = [findNodeIndex cumulative val | val <- take count randomValues]
  in selected
  where findNodeIndex cum val = 
          fromMaybe 0 $ V.findIndex (>= val) cum

-- 小世界重连
smallWorldRewiring :: DynamicNetwork -> Double -> IO DynamicNetwork
smallWorldRewiring network p = do
  let currentEdges = V.toList (edges network)
      rewireCount = floor (fromIntegral (length currentEdges) * p)
      
      -- 随机重连
      rewiredEdges = rewireEdges currentEdges rewireCount
      
      updatedEdges = V.fromList rewiredEdges
  
  return $ network { edges = updatedEdges }

-- 重连边
rewireEdges :: [NetworkEdge] -> Int -> [NetworkEdge]
rewireEdges edges count = 
  let -- 简化：随机选择边进行重连
      selectedEdges = take count edges
      remainingEdges = drop count edges
      
      -- 重连选中的边
      rewired = map rewireSingleEdge selectedEdges
  in rewired ++ remainingEdges

-- 重连单条边
rewireSingleEdge :: NetworkEdge -> NetworkEdge
rewireSingleEdge edge = 
  let newTarget = (targetNode edge + 1) `mod` 10  -- 简化：循环重连
  in edge { targetNode = newTarget }
```

### 2. 传播动力学

```haskell
-- 传播模型
data EpidemicModel = 
  SIRModel Double Double  -- 传播率和恢复率
  | SISModel Double Double  -- 传播率和恢复率
  | SIRSModel Double Double Double  -- 传播率、恢复率和免疫损失率
  deriving Show

-- 传播状态
data EpidemicState = EpidemicState
  { susceptible :: Int
  , infected :: Int
  , recovered :: Int
  , time :: Double
  } deriving Show

-- SIR传播模拟
simulateSIR :: DynamicNetwork -> EpidemicModel -> Double -> IO [EpidemicState]
simulateSIR network (SIRModel beta gamma) duration = do
  let initialState = EpidemicState 
        { susceptible = V.length (nodes network) - 1
        , infected = 1
        , recovered = 0
        , time = 0.0
        }
      
      timeSteps = [0.0, 0.1..duration]
      
      states = scanl (updateSIRState beta gamma) initialState timeSteps
  
  return states

-- 更新SIR状态
updateSIRState :: Double -> Double -> EpidemicState -> Double -> EpidemicState
updateSIRState beta gamma state dt = 
  let s = fromIntegral (susceptible state)
      i = fromIntegral (infected state)
      r = fromIntegral (recovered state)
      
      -- SIR微分方程
      ds = -beta * s * i * dt
      di = (beta * s * i - gamma * i) * dt
      dr = gamma * i * dt
      
      newS = max 0 (s + ds)
      newI = max 0 (i + di)
      newR = r + dr
  in EpidemicState 
       { susceptible = round newS
       , infected = round newI
       , recovered = round newR
       , time = time state + dt
       }

-- 网络传播模拟
simulateNetworkEpidemic :: DynamicNetwork -> EpidemicModel -> Double -> IO DynamicNetwork
simulateNetworkEpidemic network model duration = do
  let nodes = V.toList (nodes network)
      edges = V.toList (edges network)
      
      -- 初始化感染
      infectedNodes = [0]  -- 节点0被感染
      updatedNodes = map (\node -> 
                           if nodeId node `elem` infectedNodes
                           then node { nodeState = Infected }
                           else node) nodes
      
      -- 传播过程
      finalNodes = simulatePropagation updatedNodes edges model duration
  
  return $ network { nodes = V.fromList finalNodes }

-- 网络传播过程
simulatePropagation :: [NetworkNode] -> [NetworkEdge] -> EpidemicModel -> Double -> [NetworkNode]
simulatePropagation nodes edges (SIRModel beta gamma) duration = 
  let timeSteps = [0.0, 0.1..duration]
      
      propagationStep :: [NetworkNode] -> Double -> [NetworkNode]
      propagationStep currentNodes dt = 
        let infectedIds = [nodeId node | node <- currentNodes, nodeState node == Infected]
            susceptibleIds = [nodeId node | node <- currentNodes, nodeState node == Susceptible]
            
            -- 传播概率
            transmissionProb = 1 - exp (-beta * dt)
            
            -- 新感染
            newInfections = filter (\_ -> randomDouble < transmissionProb) susceptibleIds
            
            -- 恢复概率
            recoveryProb = 1 - exp (-gamma * dt)
            
            -- 新恢复
            newRecoveries = filter (\_ -> randomDouble < recoveryProb) infectedIds
            
            -- 更新节点状态
            updatedNodes = map (\node -> 
                                 let id = nodeId node
                                 in if id `elem` newInfections
                                    then node { nodeState = Infected }
                                    else if id `elem` newRecoveries
                                         then node { nodeState = Recovered }
                                         else node) currentNodes
        in updatedNodes
        where randomDouble = 0.1  -- 简化：固定随机值
      
      finalNodes = foldl propagationStep nodes timeSteps
  in finalNodes

-- 计算传播阈值
calculateTransmissionThreshold :: DynamicNetwork -> Double
calculateTransmissionThreshold network = 
  let degrees = V.map nodeDegree (nodes network)
      avgDegree = V.sum degrees / fromIntegral (V.length degrees)
      avgDegreeSquared = V.sum (V.map (\k -> fromIntegral k^2) degrees) / fromIntegral (V.length degrees)
  in avgDegree / avgDegreeSquared
```

### 3. 同步理论

```haskell
-- 振荡器
data Oscillator = Oscillator
  { oscillatorId :: Int
  , phase :: Double
  , naturalFrequency :: Double
  , couplingStrength :: Double
  } deriving Show

-- 同步网络
data SynchronizationNetwork = SynchronizationNetwork
  { oscillators :: Vector Oscillator
  , adjacencyMatrix :: Matrix Double
  , time :: Double
  } deriving Show

-- 矩阵类型
data Matrix a = Matrix
  { rows :: Int
  , cols :: Int
  , elements :: [[a]]
  } deriving Show

-- 创建同步网络
createSynchronizationNetwork :: Int -> IO SynchronizationNetwork
createSynchronizationNetwork n = do
  let oscillators = V.fromList [Oscillator i 0.0 (randomFrequency i) 1.0 | i <- [0..n-1]]
      adjacency = createRandomAdjacency n 0.3
  return $ SynchronizationNetwork oscillators adjacency 0.0
  where randomFrequency i = 1.0 + 0.1 * fromIntegral (i `mod` 5)

-- 创建随机邻接矩阵
createRandomAdjacency :: Int -> Double -> Matrix Double
createRandomAdjacency n p = 
  let elements = [[if i == j then 0.0 else if randomBool then 1.0 else 0.0 | j <- [0..n-1]] | i <- [0..n-1]]
  in Matrix n n elements
  where randomBool = True  -- 简化：固定连接

-- Kuramoto模型模拟
simulateKuramoto :: SynchronizationNetwork -> Double -> IO [SynchronizationNetwork]
simulateKuramoto network duration = do
  let timeSteps = [0.0, 0.01..duration]
      
      simulationStep :: SynchronizationNetwork -> Double -> SynchronizationNetwork
      simulationStep currentNetwork dt = 
        let currentOscillators = V.toList (oscillators currentNetwork)
            adjacency = adjacencyMatrix currentNetwork
            
            -- 更新相位
            updatedOscillators = map (\osc -> updateOscillatorPhase osc currentOscillators adjacency dt) currentOscillators
            
            newOscillators = V.fromList updatedOscillators
        in currentNetwork { oscillators = newOscillators, time = time currentNetwork + dt }
      
      networkHistory = scanl simulationStep network timeSteps
  return networkHistory

-- 更新振荡器相位
updateOscillatorPhase :: Oscillator -> [Oscillator] -> Matrix Double -> Double -> Oscillator
updateOscillatorPhase osc allOscillators adjacency dt = 
  let i = oscillatorId osc
      currentPhase = phase osc
      naturalFreq = naturalFrequency osc
      coupling = couplingStrength osc
      
      -- 计算耦合项
      couplingTerm = sum [getMatrixElement adjacency i j * sin (phase otherOsc - currentPhase) 
                         | otherOsc <- allOscillators, oscillatorId otherOsc /= i]
      
      -- Kuramoto方程
      phaseRate = naturalFreq + coupling * couplingTerm / fromIntegral (length allOscillators)
      newPhase = currentPhase + phaseRate * dt
  in osc { phase = newPhase }

-- 获取矩阵元素
getMatrixElement :: Matrix a -> Int -> Int -> a
getMatrixElement (Matrix _ _ elements) i j = elements !! i !! j

-- 计算同步序参量
calculateOrderParameter :: SynchronizationNetwork -> Double
calculateOrderParameter network = 
  let oscillators = V.toList (oscillators network)
      phases = map phase oscillators
      n = length phases
      
      -- 计算复数和的模
      realPart = sum [cos phi | phi <- phases] / fromIntegral n
      imagPart = sum [sin phi | phi <- phases] / fromIntegral n
      
      orderParam = sqrt (realPart^2 + imagPart^2)
  in orderParam

-- 同步分析
analyzeSynchronization :: SynchronizationNetwork -> Double -> IO ()
analyzeSynchronization network duration = do
  networkHistory <- simulateKuramoto network duration
  
  let orderParameters = map calculateOrderParameter networkHistory
      times = [time net | net <- networkHistory]
      
      finalOrderParam = last orderParameters
      avgOrderParam = sum orderParameters / fromIntegral (length orderParameters)
  
  putStrLn $ "同步分析结果:"
  putStrLn $ "最终序参量: " ++ show finalOrderParam
  putStrLn $ "平均序参量: " ++ show avgOrderParam
  putStrLn $ "同步程度: " ++ show (if finalOrderParam > 0.8 then "高" else if finalOrderParam > 0.5 then "中" else "低")
```

### 4. 网络稳定性分析

```haskell
-- 网络稳定性
data NetworkStability = NetworkStability
  { connectivity :: Double
  , robustness :: Double
  , efficiency :: Double
  , synchronizability :: Double
  } deriving Show

-- 计算网络稳定性
calculateNetworkStability :: DynamicNetwork -> NetworkStability
calculateNetworkStability network = 
  let nodes = V.toList (nodes network)
      edges = V.toList (edges network)
      
      -- 连通性
      connectivity = fromIntegral (length edges) / fromIntegral (length nodes * (length nodes - 1) `div` 2)
      
      -- 鲁棒性（简化：基于度分布）
      degrees = map nodeDegree nodes
      avgDegree = fromIntegral (sum degrees) / fromIntegral (length degrees)
      robustness = min 1.0 (avgDegree / 4.0)  -- 假设平均度4为理想值
      
      -- 效率（简化：基于平均路径长度）
      efficiency = 1.0 / (1.0 + avgDegree / 10.0)
      
      -- 可同步性（基于拉普拉斯矩阵特征值）
      synchronizability = calculateSynchronizability network
  in NetworkStability connectivity robustness efficiency synchronizability

-- 计算可同步性
calculateSynchronizability :: DynamicNetwork -> Double
calculateSynchronizability network = 
  let nodes = V.toList (nodes network)
      edges = V.toList (edges network)
      
      -- 构建拉普拉斯矩阵（简化）
      n = length nodes
      laplacian = [[if i == j then nodeDegree (nodes !! i) else 
                     if isConnected i j edges then -1 else 0 | j <- [0..n-1]] | i <- [0..n-1]]
      
      -- 计算特征值（简化：使用对角线元素）
      eigenvalues = [laplacian !! i !! i | i <- [0..n-1]]
      nonZeroEigenvalues = filter (> 0) eigenvalues
      
      -- 可同步性指标
      syncIndex = if null nonZeroEigenvalues 
                  then 0.0 
                  else minimum nonZeroEigenvalues / maximum nonZeroEigenvalues
  in syncIndex

-- 检查连接
isConnected :: Int -> Int -> [NetworkEdge] -> Bool
isConnected i j edges = any (\edge -> 
                              (sourceNode edge == i && targetNode edge == j) ||
                              (sourceNode edge == j && targetNode edge == i)) edges
```

## 📊 应用实例

### 1. 社交网络演化

```haskell
-- 社交网络演化模拟
simulateSocialNetworkEvolution :: Int -> Double -> IO [DynamicNetwork]
simulateSocialNetworkEvolution initialSize duration = do
  initialNetwork <- createRandomGraph initialSize 0.1
  let timeSteps = [0.0, 1.0..duration]
      
      evolutionStep :: DynamicNetwork -> Double -> IO DynamicNetwork
      evolutionStep network t = do
        -- 添加新节点
        let newNodeId = V.length (nodes network)
        network1 <- preferentialAttachment network newNodeId
        
        -- 小世界重连
        network2 <- smallWorldRewiring network1 0.01
        
        return network2
      
      evolution = scanM evolutionStep initialNetwork timeSteps
  return evolution

-- 扫描M操作
scanM :: Monad m => (a -> b -> m a) -> a -> [b] -> m [a]
scanM f a [] = return [a]
scanM f a (b:bs) = do
  a' <- f a b
  as <- scanM f a' bs
  return (a:as)
```

### 2. 疾病传播预测

```haskell
-- 疾病传播预测
predictEpidemicSpread :: DynamicNetwork -> EpidemicModel -> Double -> IO ()
predictEpidemicSpread network model duration = do
  -- 模拟传播
  states <- simulateSIR network model duration
  
  -- 分析结果
  let finalState = last states
      peakInfected = maximum [infected state | state <- states]
      totalAffected = recovered finalState + infected finalState
  
  putStrLn $ "疾病传播预测:"
  putStrLn $ "最终感染人数: " ++ show (infected finalState)
  putStrLn $ "最终恢复人数: " ++ show (recovered finalState)
  putStrLn $ "峰值感染人数: " ++ show peakInfected
  putStrLn $ "总受影响人数: " ++ show totalAffected
  
  -- 计算传播阈值
  let threshold = calculateTransmissionThreshold network
  putStrLn $ "传播阈值: " ++ show threshold
```

### 3. 网络同步控制

```haskell
-- 网络同步控制
controlNetworkSynchronization :: SynchronizationNetwork -> Double -> IO ()
controlNetworkSynchronization network targetOrderParam = do
  let initialOrderParam = calculateOrderParameter network
      
      -- 调整耦合强度
      adjustCoupling :: SynchronizationNetwork -> Double -> SynchronizationNetwork
      adjustCoupling net adjustment = 
        let oscillators = V.toList (oscillators net)
            adjustedOscillators = map (\osc -> osc { couplingStrength = couplingStrength osc + adjustment }) oscillators
        in net { oscillators = V.fromList adjustedOscillators }
      
      -- 控制策略
      controlStep :: SynchronizationNetwork -> IO SynchronizationNetwork
      controlStep net = do
        let currentOrderParam = calculateOrderParameter net
            error = targetOrderParam - currentOrderParam
            adjustment = 0.1 * error  -- 比例控制
        
        return $ adjustCoupling net adjustment
  
  -- 执行控制
  finalNetwork <- controlStep network
  let finalOrderParam = calculateOrderParameter finalNetwork
  
  putStrLn $ "同步控制结果:"
  putStrLn $ "初始序参量: " ++ show initialOrderParam
  putStrLn $ "目标序参量: " ++ show targetOrderParam
  putStrLn $ "最终序参量: " ++ show finalOrderParam
  putStrLn $ "控制误差: " ++ show (abs (targetOrderParam - finalOrderParam))
```

## 🔗 相关理论

- [网络结构理论](../12-Network-Science/01-Network-Structure.md)
- [复杂系统理论](../13-Complex-Systems/01-System-Dynamics.md)
- [统计物理理论](../11-Statistical-Physics/01-Statistical-Mechanics.md)
- [微分方程理论](../10-Mathematical-Physics/02-Differential-Equations.md)
- [图论基础](../09-Discrete-Mathematics/01-Graph-Theory.md)

## 📚 参考文献

1. Newman, M. E. J. (2010). *Networks: An Introduction*. Oxford University Press.
2. Barrat, A., Barthélemy, M., & Vespignani, A. (2008). *Dynamical Processes on Complex Networks*. Cambridge University Press.
3. Strogatz, S. H. (2001). *Exploring complex networks*. Nature.

---

**文档版本**: 1.0.0  
**维护者**: AI Assistant  
**最后更新**: 2024年12月19日 