# 生物网络

## 概述

生物网络研究生物系统中分子、细胞、组织之间的相互作用关系。本节将建立生物网络分析的形式化理论框架，并提供Haskell实现。

## 1. 蛋白质相互作用网络

### 1.1 网络表示

**定义 1.1.1** (蛋白质相互作用网络)
蛋白质相互作用网络 $G = (V, E, W)$ 是一个带权无向图，其中：

- $V$ 是蛋白质集合
- $E$ 是相互作用关系集合
- $W: E \rightarrow \mathbb{R}^+$ 是相互作用强度

**Haskell实现**：

```haskell
-- | 蛋白质相互作用网络
data ProteinInteractionNetwork = PINetwork
  { proteins :: [Protein]
  , interactions :: [(Int, Int, Double)]  -- (protein1, protein2, strength)
  , proteinFunctions :: Map Int [String]
  } deriving (Show, Eq)

data Protein = Protein
  { proteinId :: Int
  , name :: String
  , sequence :: String
  , molecularWeight :: Double
  , isoelectricPoint :: Double
  } deriving (Show, Eq)

-- | 创建蛋白质相互作用网络
createPINetwork :: [Protein] -> [(Int, Int, Double)] -> ProteinInteractionNetwork
createPINetwork proteins interactions = PINetwork
  { proteins = proteins
  , interactions = interactions
  , proteinFunctions = Map.empty
  }

-- | 获取蛋白质邻居
getProteinNeighbors :: Int -> ProteinInteractionNetwork -> [Int]
getProteinNeighbors proteinId network = 
  [if p1 == proteinId then p2 else p1 | (p1, p2, _) <- interactions network, 
                                       p1 == proteinId || p2 == proteinId]

-- | 计算蛋白质度
proteinDegree :: Int -> ProteinInteractionNetwork -> Int
proteinDegree proteinId network = length (getProteinNeighbors proteinId network)
```

### 1.2 功能模块识别

**定义 1.2.1** (功能模块)
功能模块是网络中功能相关的蛋白质子集，具有高内部连接密度。

**Haskell实现**：

```haskell
-- | 功能模块
data FunctionalModule = FunctionalModule
  { moduleId :: Int
  , members :: Set Int
  , function :: String
  , internalDensity :: Double
  } deriving (Show, Eq)

-- | 模块识别算法
identifyFunctionalModules :: ProteinInteractionNetwork -> [FunctionalModule]
identifyFunctionalModules network = 
  let communities = louvainAlgorithm network
      modules = map (\comm -> createFunctionalModule comm network) communities
  in filter (\module -> internalDensity module > 0.3) modules

-- | 创建功能模块
createFunctionalModule :: Community -> ProteinInteractionNetwork -> FunctionalModule
createFunctionalModule community network = FunctionalModule
  { moduleId = communityId community
  , members = members community
  , function = inferFunction (members community) network
  , internalDensity = calculateInternalDensity community network
  }

-- | 推断功能
inferFunction :: Set Int -> ProteinInteractionNetwork -> String
inferFunction proteinSet network = 
  let functions = concat [proteinFunctions network Map.! proteinId | 
                         proteinId <- Set.toList proteinSet]
      functionCounts = Map.fromListWith (+) [(func, 1) | func <- functions]
  in fst $ maximumBy (compare `on` snd) $ Map.toList functionCounts

-- | 计算内部密度
calculateInternalDensity :: Community -> ProteinInteractionNetwork -> Double
calculateInternalDensity community network = 
  let memberList = Set.toList (members community)
      possibleEdges = length memberList * (length memberList - 1) `div` 2
      actualEdges = countInternalEdges memberList network
  in if possibleEdges > 0 then fromIntegral actualEdges / fromIntegral possibleEdges else 0.0

-- | 计算内部边数
countInternalEdges :: [Int] -> ProteinInteractionNetwork -> Int
countInternalEdges members network = 
  length [edge | edge@(p1, p2, _) <- interactions network, 
                 p1 `elem` members, p2 `elem` members]
```

### 1.3 中心性分析

**定义 1.3.1** (蛋白质中心性)
蛋白质在网络中的重要性度量。

**Haskell实现**：

```haskell
-- | 蛋白质中心性分析
data ProteinCentrality = ProteinCentrality
  { proteinId :: Int
  , degreeCentrality :: Double
  , betweennessCentrality :: Double
  , closenessCentrality :: Double
  , eigenvectorCentrality :: Double
  } deriving (Show, Eq)

-- | 计算蛋白质中心性
calculateProteinCentrality :: Int -> ProteinInteractionNetwork -> ProteinCentrality
calculateProteinCentrality proteinId network = ProteinCentrality
  { proteinId = proteinId
  , degreeCentrality = degreeCentrality proteinId network
  , betweennessCentrality = betweennessCentrality proteinId network
  , closenessCentrality = closenessCentrality proteinId network
  , eigenvectorCentrality = eigenvectorCentrality proteinId network
  }

-- | 度中心性
degreeCentrality :: Int -> ProteinInteractionNetwork -> Double
degreeCentrality proteinId network = 
  let degree = proteinDegree proteinId network
      n = length (proteins network)
  in fromIntegral degree / fromIntegral (n - 1)

-- | 介数中心性
betweennessCentrality :: Int -> ProteinInteractionNetwork -> Double
betweennessCentrality proteinId network = 
  let n = length (proteins network)
      allPairs = [(i, j) | i <- [0..n-1], j <- [i+1..n-1], i /= j]
      totalPaths = sum [shortestPaths i j network | (i, j) <- allPairs]
      pathsThroughProtein = sum [shortestPathsThrough i j proteinId network | (i, j) <- allPairs]
  in if totalPaths > 0 then pathsThroughProtein / totalPaths else 0

-- | 特征向量中心性
eigenvectorCentrality :: Int -> ProteinInteractionNetwork -> Double
eigenvectorCentrality proteinId network = 
  let adjacency = buildProteinAdjacencyMatrix network
      eigenvalues = eigenDecomposition adjacency
      dominantEigenvector = head eigenvalues
  in dominantEigenvector !! proteinId
```

## 2. 基因调控网络

### 2.1 调控关系建模

**定义 2.1.1** (基因调控网络)
基因调控网络 $G = (V, E, W, T)$ 是一个带权有向图，其中：

- $V$ 是基因集合
- $E$ 是调控关系集合
- $W: E \rightarrow \mathbb{R}$ 是调控强度
- $T: E \rightarrow \{激活, 抑制\}$ 是调控类型

**Haskell实现**：

```haskell
-- | 基因调控网络
data GeneRegulatoryNetwork = GRNetwork
  { genes :: [Gene]
  , regulations :: [(Int, Int, Double, RegulationType)]
  , expressionLevels :: Map Int Double
  } deriving (Show, Eq)

data Gene = Gene
  { geneId :: Int
  , name :: String
  , chromosome :: String
  , startPosition :: Int
  , endPosition :: Int
  } deriving (Show, Eq)

data RegulationType = Activation | Repression
  deriving (Show, Eq)

-- | 创建基因调控网络
createGRNetwork :: [Gene] -> [(Int, Int, Double, RegulationType)] -> GeneRegulatoryNetwork
createGRNetwork genes regulations = GRNetwork
  { genes = genes
  , regulations = regulations
  , expressionLevels = Map.fromList [(geneId gene, 0.0) | gene <- genes]
  }

-- | 获取调控目标
getRegulatoryTargets :: Int -> GeneRegulatoryNetwork -> [Int]
getRegulatoryTargets geneId network = 
  [target | (regulator, target, _, _) <- regulations network, regulator == geneId]

-- | 获取调控因子
getRegulatoryFactors :: Int -> GeneRegulatoryNetwork -> [Int]
getRegulatoryFactors geneId network = 
  [regulator | (regulator, target, _, _) <- regulations network, target == geneId]
```

### 2.2 基因表达动力学

**定义 2.2.1** (基因表达动力学)
基因表达水平随时间的变化过程。

**Haskell实现**：

```haskell
-- | 基因表达动力学
data GeneExpressionDynamics = GEDynamics
  { network :: GeneRegulatoryNetwork
  , timeStep :: Double
  , degradationRates :: Map Int Double
  , synthesisRates :: Map Int Double
  } deriving (Show, Eq)

-- | 基因表达更新
updateGeneExpression :: GeneExpressionDynamics -> GeneRegulatoryNetwork -> GeneRegulatoryNetwork
updateGeneExpression dynamics network = 
  let newExpressionLevels = Map.mapWithKey (\geneId currentLevel -> 
    updateExpressionLevel geneId currentLevel dynamics network) (expressionLevels network)
  in network { expressionLevels = newExpressionLevels }

-- | 更新表达水平
updateExpressionLevel :: Int -> Double -> GeneExpressionDynamics -> GeneRegulatoryNetwork -> Double
updateExpressionLevel geneId currentLevel dynamics network = 
  let regulators = getRegulatoryFactors geneId network
      regulatoryEffect = calculateRegulatoryEffect geneId regulators dynamics network
      synthesisRate = synthesisRates dynamics Map.! geneId
      degradationRate = degradationRates dynamics Map.! geneId
      dt = timeStep dynamics
      newLevel = currentLevel + dt * (synthesisRate * regulatoryEffect - degradationRate * currentLevel)
  in max 0.0 newLevel

-- | 计算调控效应
calculateRegulatoryEffect :: Int -> [Int] -> GeneExpressionDynamics -> GeneRegulatoryNetwork -> Double
calculateRegulatoryEffect geneId regulators dynamics network = 
  let regulatoryTerms = [regulationTerm geneId regulator dynamics network | regulator <- regulators]
  in product regulatoryTerms

-- | 调控项
regulationTerm :: Int -> Int -> GeneExpressionDynamics -> GeneRegulatoryNetwork -> Double
regulationTerm target regulator dynamics network = 
  let regulation = findRegulation regulator target network
      regulatorLevel = expressionLevels network Map.! regulator
      strength = regulationStrength regulation
      regType = regulationType regulation
  in case regType of
       Activation -> hillFunction regulatorLevel strength
       Repression -> 1.0 - hillFunction regulatorLevel strength

-- | Hill函数
hillFunction :: Double -> Double -> Double
hillFunction x k = x / (k + x)
```

### 2.3 调控模块识别

**定义 2.3.1** (调控模块)
调控模块是功能相关的基因子集，具有相似的调控模式。

**Haskell实现**：

```haskell
-- | 调控模块
data RegulatoryModule = RegulatoryModule
  { moduleId :: Int
  , genes :: Set Int
  , regulators :: Set Int
  , expressionPattern :: [Double]
  } deriving (Show, Eq)

-- | 识别调控模块
identifyRegulatoryModules :: GeneRegulatoryNetwork -> [RegulatoryModule]
identifyRegulatoryModules network = 
  let genePairs = [(i, j) | i <- [0..length (genes network) - 1], 
                          j <- [i+1..length (genes network) - 1]]
      similarities = [(i, j, geneSimilarity i j network) | (i, j) <- genePairs]
      clusters = hierarchicalClustering similarities 0.7
      modules = map (\cluster -> createRegulatoryModule cluster network) clusters
  in modules

-- | 基因相似性
geneSimilarity :: Int -> Int -> GeneRegulatoryNetwork -> Double
geneSimilarity gene1 gene2 network = 
  let regulators1 = Set.fromList (getRegulatoryFactors gene1 network)
      regulators2 = Set.fromList (getRegulatoryFactors gene2 network)
      targets1 = Set.fromList (getRegulatoryTargets gene1 network)
      targets2 = Set.fromList (getRegulatoryTargets gene2 network)
      regulatorSim = jaccardSimilarity regulators1 regulators2
      targetSim = jaccardSimilarity targets1 targets2
  in (regulatorSim + targetSim) / 2.0

-- | Jaccard相似性
jaccardSimilarity :: Set Int -> Set Int -> Double
jaccardSimilarity set1 set2 = 
  let intersection = Set.size (Set.intersection set1 set2)
      union = Set.size (Set.union set1 set2)
  in if union > 0 then fromIntegral intersection / fromIntegral union else 0.0
```

## 3. 代谢网络

### 3.1 代谢网络表示

**定义 3.1.1** (代谢网络)
代谢网络 $G = (V, E, W)$ 是一个带权有向二分图，其中：

- $V = V_M \cup V_R$ 是代谢物和反应集合
- $E$ 是代谢物与反应的关系
- $W: E \rightarrow \mathbb{R}$ 是化学计量系数

**Haskell实现**：

```haskell
-- | 代谢网络
data MetabolicNetwork = MetabolicNetwork
  { metabolites :: [Metabolite]
  , reactions :: [Reaction]
  , stoichiometry :: Map (Int, Int) Double  -- (metabolite, reaction) -> coefficient
  , fluxes :: Map Int Double  -- reaction -> flux
  } deriving (Show, Eq)

data Metabolite = Metabolite
  { metaboliteId :: Int
  , name :: String
  , formula :: String
  , charge :: Int
  } deriving (Show, Eq)

data Reaction = Reaction
  { reactionId :: Int
  , name :: String
  , reversible :: Bool
  , bounds :: (Double, Double)  -- (lower, upper)
  } deriving (Show, Eq)

-- | 创建代谢网络
createMetabolicNetwork :: [Metabolite] -> [Reaction] -> [(Int, Int, Double)] -> MetabolicNetwork
createMetabolicNetwork metabolites reactions stoichiometry = MetabolicNetwork
  { metabolites = metabolites
  , reactions = reactions
  , stoichiometry = Map.fromList [(key, coeff) | (met, reac, coeff) <- stoichiometry, 
                                                let key = (met, reac)]
  , fluxes = Map.fromList [(reactionId reaction, 0.0) | reaction <- reactions]
  }

-- | 获取反应的反应物
getReactants :: Int -> MetabolicNetwork -> [(Int, Double)]
getReactants reactionId network = 
  [(metaboliteId, -coefficient) | ((metaboliteId, reacId), coefficient) <- Map.toList (stoichiometry network),
                                 reacId == reactionId, coefficient < 0]

-- | 获取反应的产物
getProducts :: Int -> MetabolicNetwork -> [(Int, Double)]
getProducts reactionId network = 
  [(metaboliteId, coefficient) | ((metaboliteId, reacId), coefficient) <- Map.toList (stoichiometry network),
                                reacId == reactionId, coefficient > 0]
```

### 3.2 代谢流分析

**定义 3.2.1** (代谢流平衡)
在稳态下，每个代谢物的净产生率为零：

$$\sum_j S_{ij} v_j = 0$$

其中 $S_{ij}$ 是化学计量矩阵，$v_j$ 是反应通量。

**Haskell实现**：

```haskell
-- | 代谢流平衡分析
data FluxBalanceAnalysis = FluxBalanceAnalysis
  { network :: MetabolicNetwork
  , objective :: ObjectiveFunction
  , constraints :: [Constraint]
  } deriving (Show, Eq)

data ObjectiveFunction = MaximizeGrowth | MaximizeProduct Int | MinimizeFlux
  deriving (Show, Eq)

data Constraint = Constraint
  { reactionId :: Int
  , lowerBound :: Double
  , upperBound :: Double
  } deriving (Show, Eq)

-- | 求解代谢流平衡
solveFluxBalance :: FluxBalanceAnalysis -> Map Int Double
solveFluxBalance fba = 
  let stoichiometryMatrix = buildStoichiometryMatrix (network fba)
      bounds = buildBounds (network fba) (constraints fba)
      objective = buildObjective (network fba) (objective fba)
      solution = linearProgramming stoichiometryMatrix bounds objective
  in Map.fromList $ zip [0..] solution

-- | 构建化学计量矩阵
buildStoichiometryMatrix :: MetabolicNetwork -> [[Double]]
buildStoichiometryMatrix network = 
  let nMetabolites = length (metabolites network)
      nReactions = length (reactions network)
  in [[stoichiometry network Map.! (metId, reacId) | reacId <- [0..nReactions-1]] 
      | metId <- [0..nMetabolites-1]]

-- | 构建边界约束
buildBounds :: MetabolicNetwork -> [Constraint] -> [(Double, Double)]
buildBounds network constraints = 
  let defaultBounds = [(lowerBound reaction, upperBound reaction) | reaction <- reactions network]
      constraintMap = Map.fromList [(reactionId constraint, 
                                   (lowerBound constraint, upperBound constraint)) | 
                                   constraint <- constraints]
  in [Map.findWithDefault defaultBound reactionId constraintMap | 
      (reactionId, defaultBound) <- zip [0..] defaultBounds]

-- | 构建目标函数
buildObjective :: MetabolicNetwork -> ObjectiveFunction -> [Double]
buildObjective network objective = 
  let nReactions = length (reactions network)
  in case objective of
       MaximizeGrowth -> replicate nReactions 0.0  -- 假设生物量反应为第一个
       MaximizeProduct metaboliteId -> 
         [if reactionId reaction == metaboliteId then 1.0 else 0.0 | reaction <- reactions network]
       MinimizeFlux -> replicate nReactions 1.0
```

### 3.3 代谢路径分析

**定义 3.3.1** (代谢路径)
代谢路径是从起始代谢物到目标代谢物的反应序列。

**Haskell实现**：

```haskell
-- | 代谢路径
data MetabolicPath = MetabolicPath
  { startMetabolite :: Int
  , endMetabolite :: Int
  , reactions :: [Int]
  , metabolites :: [Int]
  , flux :: Double
  } deriving (Show, Eq)

-- | 寻找代谢路径
findMetabolicPaths :: Int -> Int -> MetabolicNetwork -> [MetabolicPath]
findMetabolicPaths start end network = 
  let allPaths = findAllPaths start end network
      validPaths = filter (isValidPath network) allPaths
  in map (\path -> createMetabolicPath path network) validPaths

-- | 寻找所有路径
findAllPaths :: Int -> Int -> MetabolicNetwork -> [[Int]]
findAllPaths start end network = 
  let queue = [(start, [start])]
  in bfsPaths queue end network

-- | 广度优先搜索路径
bfsPaths :: [(Int, [Int])] -> Int -> MetabolicNetwork -> [[Int]]
bfsPaths [] _ _ = []
bfsPaths ((current, path):queue) target network = 
  if current == target then 
    path : bfsPaths queue target network
  else
    let neighbors = getMetaboliteNeighbors current network
        newPaths = [(neighbor, path ++ [neighbor]) | neighbor <- neighbors, 
                                                    neighbor `notElem` path]
    in bfsPaths (queue ++ newPaths) target network

-- | 获取代谢物邻居
getMetaboliteNeighbors :: Int -> MetabolicNetwork -> [Int]
getMetaboliteNeighbors metaboliteId network = 
  let connectedReactions = [reacId | ((metId, reacId), _) <- Map.toList (stoichiometry network),
                                   metId == metaboliteId]
      neighborMetabolites = concat [getReactionMetabolites reacId network | reacId <- connectedReactions]
  in nub $ filter (/= metaboliteId) neighborMetabolites

-- | 获取反应相关代谢物
getReactionMetabolites :: Int -> MetabolicNetwork -> [Int]
getReactionMetabolites reactionId network = 
  let reactants = map fst (getReactants reactionId network)
      products = map fst (getProducts reactionId network)
  in reactants ++ products
```

## 4. 网络比较分析

### 4.1 网络对齐

**定义 4.1.1** (网络对齐)
网络对齐寻找不同网络之间的节点对应关系。

**Haskell实现**：

```haskell
-- | 网络对齐
data NetworkAlignment = NetworkAlignment
  { network1 :: ProteinInteractionNetwork
  , network2 :: ProteinInteractionNetwork
  , nodeMapping :: Map Int Int
  , alignmentScore :: Double
  } deriving (Show, Eq)

-- | 全局网络对齐
globalNetworkAlignment :: ProteinInteractionNetwork -> ProteinInteractionNetwork -> NetworkAlignment
globalNetworkAlignment net1 net2 = 
  let similarityMatrix = buildSimilarityMatrix net1 net2
      mapping = hungarianAlgorithm similarityMatrix
      score = calculateAlignmentScore mapping net1 net2
  in NetworkAlignment net1 net2 mapping score

-- | 构建相似性矩阵
buildSimilarityMatrix :: ProteinInteractionNetwork -> ProteinInteractionNetwork -> [[Double]]
buildSimilarityMatrix net1 net2 = 
  let n1 = length (proteins net1)
      n2 = length (proteins net2)
  in [[nodeSimilarity i j net1 net2 | j <- [0..n2-1]] | i <- [0..n1-1]]

-- | 节点相似性
nodeSimilarity :: Int -> Int -> ProteinInteractionNetwork -> ProteinInteractionNetwork -> Double
nodeSimilarity node1 node2 net1 net2 = 
  let degree1 = proteinDegree node1 net1
      degree2 = proteinDegree node2 net2
      function1 = proteinFunctions net1 Map.! node1
      function2 = proteinFunctions net2 Map.! node2
      degreeSim = 1.0 - abs (fromIntegral degree1 - fromIntegral degree2) / max (fromIntegral degree1) (fromIntegral degree2)
      functionSim = jaccardSimilarity (Set.fromList function1) (Set.fromList function2)
  in (degreeSim + functionSim) / 2.0
```

### 4.2 网络演化分析

**定义 4.2.1** (网络演化)
分析网络结构随时间的演化过程。

**Haskell实现**：

```haskell
-- | 网络演化
data NetworkEvolution = NetworkEvolution
  { timePoints :: [Double]
  , networks :: [ProteinInteractionNetwork]
  , evolutionMetrics :: Map Double EvolutionMetrics
  } deriving (Show, Eq)

data EvolutionMetrics = EvolutionMetrics
  { nodeCount :: Int
  , edgeCount :: Int
  , averageDegree :: Double
  , clusteringCoefficient :: Double
  , diameter :: Double
  } deriving (Show, Eq)

-- | 分析网络演化
analyzeNetworkEvolution :: [ProteinInteractionNetwork] -> [Double] -> NetworkEvolution
analyzeNetworkEvolution networks times = NetworkEvolution
  { timePoints = times
  , networks = networks
  , evolutionMetrics = Map.fromList [(time, calculateMetrics network) | 
                                     (time, network) <- zip times networks]
  }

-- | 计算演化指标
calculateMetrics :: ProteinInteractionNetwork -> EvolutionMetrics
calculateMetrics network = EvolutionMetrics
  { nodeCount = length (proteins network)
  , edgeCount = length (interactions network)
  , averageDegree = 2.0 * fromIntegral (length (interactions network)) / fromIntegral (length (proteins network))
  , clusteringCoefficient = globalClusteringCoefficient network
  , diameter = networkDiameter network
  }
```

## 5. 应用实例

### 5.1 疾病基因识别

**应用 5.1.1** (疾病基因预测)
利用蛋白质相互作用网络预测疾病相关基因。

```haskell
-- | 疾病基因预测
data DiseaseGenePrediction = DiseaseGenePrediction
  { network :: ProteinInteractionNetwork
  , knownDiseaseGenes :: Set Int
  , candidateGenes :: [Int]
  , predictionScores :: Map Int Double
  } deriving (Show, Eq)

-- | 预测疾病基因
predictDiseaseGenes :: ProteinInteractionNetwork -> Set Int -> [Int]
predictDiseaseGenes network knownGenes = 
  let allGenes = [proteinId protein | protein <- proteins network]
      candidateGenes = filter (`Set.notMember` knownGenes) allGenes
      scores = Map.fromList [(gene, diseaseScore gene knownGenes network) | gene <- candidateGenes]
      sortedGenes = map fst $ sortBy (flip compare `on` snd) $ Map.toList scores
  in take 100 sortedGenes  -- 返回前100个候选基因

-- | 疾病评分
diseaseScore :: Int -> Set Int -> ProteinInteractionNetwork -> Double
diseaseScore gene knownGenes network = 
  let neighbors = getProteinNeighbors gene network
      diseaseNeighbors = filter (`Set.member` knownGenes) neighbors
      neighborScore = fromIntegral (length diseaseNeighbors) / fromIntegral (length neighbors)
      functionalScore = functionalSimilarity gene knownGenes network
  in 0.7 * neighborScore + 0.3 * functionalScore

-- | 功能相似性
functionalSimilarity :: Int -> Set Int -> ProteinInteractionNetwork -> Double
functionalSimilarity gene knownGenes network = 
  let geneFunctions = proteinFunctions network Map.! gene
      knownGeneFunctions = concat [proteinFunctions network Map.! knownGene | 
                                  knownGene <- Set.toList knownGenes]
      functionOverlap = length (intersect geneFunctions knownGeneFunctions)
      totalFunctions = length (union geneFunctions knownGeneFunctions)
  in if totalFunctions > 0 then fromIntegral functionOverlap / fromIntegral totalFunctions else 0.0
```

### 5.2 药物靶点预测

**应用 5.2.1** (药物靶点识别)
预测药物的潜在作用靶点。

```haskell
-- | 药物靶点预测
data DrugTargetPrediction = DrugTargetPrediction
  { network :: ProteinInteractionNetwork
  , knownTargets :: Set Int
  , drugProperties :: DrugProperties
  , predictedTargets :: Map Int Double
  } deriving (Show, Eq)

data DrugProperties = DrugProperties
  { molecularWeight :: Double
  , logP :: Double
  , hbd :: Int  -- 氢键供体数
  , hba :: Int  -- 氢键受体数
  } deriving (Show, Eq)

-- | 预测药物靶点
predictDrugTargets :: ProteinInteractionNetwork -> Set Int -> DrugProperties -> [Int]
predictDrugTargets network knownTargets properties = 
  let allProteins = [proteinId protein | protein <- proteins network]
      candidateTargets = filter (`Set.notMember` knownTargets) allProteins
      scores = Map.fromList [(protein, targetScore protein knownTargets properties network) | 
                             protein <- candidateTargets]
      sortedTargets = map fst $ sortBy (flip compare `on` snd) $ Map.toList scores
  in take 50 sortedTargets

-- | 靶点评分
targetScore :: Int -> Set Int -> DrugProperties -> ProteinInteractionNetwork -> Double
targetScore protein knownTargets properties network = 
  let networkScore = networkProximityScore protein knownTargets network
      functionalScore = functionalRelevanceScore protein properties network
      druggabilityScore = druggabilityScore protein network
  in 0.4 * networkScore + 0.4 * functionalScore + 0.2 * druggabilityScore

-- | 网络邻近性评分
networkProximityScore :: Int -> Set Int -> ProteinInteractionNetwork -> Double
networkProximityScore protein knownTargets network = 
  let distances = [shortestPathDistance protein target network | target <- Set.toList knownTargets]
      minDistance = minimum distances
  in exp (-minDistance)  -- 距离越近，评分越高
```

## 6. 总结

生物网络分析提供了理解生物系统复杂性的强大工具。通过形式化建模和Haskell实现，我们可以：

1. **分析蛋白质相互作用**：理解蛋白质功能和组织
2. **研究基因调控**：分析基因表达调控机制
3. **探索代谢网络**：理解代谢途径和通量分布
4. **比较网络结构**：发现不同物种间的保守模式
5. **预测疾病基因**：识别疾病相关基因和药物靶点

这些理论和方法在系统生物学、药物发现、个性化医疗等领域都有重要应用。

---

**参考文献**：

1. Barabási, A. L., & Oltvai, Z. N. (2004). Network biology: understanding the cell's functional organization. Nature Reviews Genetics, 5(2), 101-113.
2. Alon, U. (2007). Network motifs: theory and experimental approaches. Nature Reviews Genetics, 8(6), 450-461.
3. Palsson, B. Ø. (2015). Systems Biology: Constraint-based Reconstruction and Analysis. Cambridge University Press.
