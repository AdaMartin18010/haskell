# 社交网络

## 概述

社交网络分析研究人际关系网络的结构、动态和功能。本节将建立社交网络分析的形式化理论框架，并提供Haskell实现。

## 1. 社交网络基础

### 1.1 网络表示

**定义 1.1.1** (社交网络)
社交网络 $G = (V, E, W)$ 是一个带权有向图，其中：

- $V$ 是节点集合（用户）
- $E$ 是边集合（关系）
- $W: E \rightarrow \mathbb{R}^+$ 是权重函数（关系强度）

**Haskell实现**：

```haskell
-- | 社交网络表示
data SocialNetwork = SocialNetwork
  { nodes :: [User]
  , edges :: [(Int, Int, Double)]  -- (from, to, weight)
  , attributes :: Map Int UserAttributes
  } deriving (Show, Eq)

data User = User
  { userId :: Int
  , name :: String
  , joinDate :: UTCTime
  } deriving (Show, Eq)

data UserAttributes = UserAttributes
  { age :: Maybe Int
  , location :: Maybe String
  , interests :: [String]
  , activity :: Double
  } deriving (Show, Eq)

-- | 创建社交网络
createSocialNetwork :: [User] -> [(Int, Int, Double)] -> SocialNetwork
createSocialNetwork users relationships = SocialNetwork
  { nodes = users
  , edges = relationships
  , attributes = Map.empty
  }

-- | 添加用户属性
addUserAttributes :: SocialNetwork -> Map Int UserAttributes -> SocialNetwork
addUserAttributes network attrs = network { attributes = attrs }

-- | 获取用户邻居
getNeighbors :: Int -> SocialNetwork -> [Int]
getNeighbors userId network = 
  [to | (from, to, _) <- edges network, from == userId]

-- | 获取用户入度邻居
getInNeighbors :: Int -> SocialNetwork -> [Int]
getInNeighbors userId network = 
  [from | (from, to, _) <- edges network, to == userId]
```

### 1.2 网络度量

#### 1.2.1 中心性度量

**定义 1.2.1** (度中心性)
节点 $i$ 的度中心性为：

$$C_D(i) = \frac{k_i}{n-1}$$

其中 $k_i$ 是节点 $i$ 的度，$n$ 是网络节点数。

**Haskell实现**：

```haskell
-- | 度中心性
degreeCentrality :: Int -> SocialNetwork -> Double
degreeCentrality userId network = 
  let neighbors = getNeighbors userId network
      n = length (nodes network)
  in fromIntegral (length neighbors) / fromIntegral (n - 1)

-- | 接近中心性
closenessCentrality :: Int -> SocialNetwork -> Double
closenessCentrality userId network = 
  let distances = shortestPathDistances userId network
      totalDistance = sum distances
      n = length (nodes network)
  in if totalDistance > 0 then fromIntegral (n - 1) / totalDistance else 0

-- | 介数中心性
betweennessCentrality :: Int -> SocialNetwork -> Double
betweennessCentrality userId network = 
  let n = length (nodes network)
      allPairs = [(i, j) | i <- [0..n-1], j <- [i+1..n-1], i /= j]
      totalPaths = sum [shortestPaths i j network | (i, j) <- allPairs]
      pathsThroughNode = sum [shortestPathsThrough i j userId network | (i, j) <- allPairs]
  in if totalPaths > 0 then pathsThroughNode / totalPaths else 0

-- | 特征向量中心性
eigenvectorCentrality :: SocialNetwork -> Map Int Double
eigenvectorCentrality network = 
  let adjacency = buildAdjacencyMatrix network
      eigenvalues = eigenDecomposition adjacency
      dominantEigenvector = head eigenvalues
  in Map.fromList $ zip [0..] dominantEigenvector
```

#### 1.2.2 聚类系数

**定义 1.2.2** (局部聚类系数)
节点 $i$ 的局部聚类系数为：

$$C_i = \frac{2E_i}{k_i(k_i-1)}$$

其中 $E_i$ 是节点 $i$ 的邻居间的边数。

**Haskell实现**：

```haskell
-- | 局部聚类系数
localClusteringCoefficient :: Int -> SocialNetwork -> Double
localClusteringCoefficient userId network = 
  let neighbors = getNeighbors userId network
      k = length neighbors
      if k < 2 then 0 else
        let neighborEdges = countNeighborEdges neighbors network
        in 2.0 * fromIntegral neighborEdges / fromIntegral (k * (k - 1))

-- | 全局聚类系数
globalClusteringCoefficient :: SocialNetwork -> Double
globalClusteringCoefficient network = 
  let nodes = map userId (nodes network)
      localCoeffs = map (\n -> localClusteringCoefficient n network) nodes
  in sum localCoeffs / fromIntegral (length nodes)

-- | 计算邻居间边数
countNeighborEdges :: [Int] -> SocialNetwork -> Int
countNeighborEdges neighbors network = 
  length [edge | edge@(from, to, _) <- edges network, 
                 from `elem` neighbors, to `elem` neighbors, from < to]
```

## 2. 社区发现

### 2.1 社区定义

**定义 2.1.1** (社区)
社区是网络中节点的一个子集，其中内部连接密度高于外部连接密度。

**Haskell实现**：

```haskell
-- | 社区结构
data Community = Community
  { members :: Set Int
  , internalEdges :: Int
  , externalEdges :: Int
  } deriving (Show, Eq)

-- | 社区质量度量
data CommunityQuality = CommunityQuality
  { modularity :: Double
  , conductance :: Double
  , coverage :: Double
  } deriving (Show, Eq)

-- | 计算模块度
modularity :: [Community] -> SocialNetwork -> Double
modularity communities network = 
  let m = length (edges network)
      totalModularity = sum [communityModularity comm network m | comm <- communities]
  in totalModularity / (2.0 * fromIntegral m)

-- | 单个社区模块度
communityModularity :: Community -> SocialNetwork -> Int -> Double
communityModularity comm network m = 
  let internal = fromIntegral (internalEdges comm)
      total = fromIntegral (internalEdges comm + externalEdges comm)
      expected = (total * total) / (2.0 * fromIntegral m)
  in internal - expected
```

### 2.2 社区发现算法

#### 2.2.1 Louvain算法

**算法 2.2.1** (Louvain算法)
Louvain算法是一种基于模块度优化的社区发现算法。

**Haskell实现**：

```haskell
-- | Louvain算法
louvainAlgorithm :: SocialNetwork -> [Community]
louvainAlgorithm network = 
  let initialCommunities = map (\node -> Community (Set.singleton node) 0 0) 
                              [0..length (nodes network) - 1]
  in iterateLouvain network initialCommunities

-- | Louvain迭代
iterateLouvain :: SocialNetwork -> [Community] -> [Community]
iterateLouvain network communities = 
  let newCommunities = optimizeModularity network communities
  in if newCommunities == communities 
     then communities 
     else iterateLouvain network newCommunities

-- | 模块度优化
optimizeModularity :: SocialNetwork -> [Community] -> [Community]
optimizeModularity network communities = 
  let nodes = [0..length (nodes network) - 1]
      optimizedCommunities = foldl (\comms node -> 
        moveToBestCommunity node comms network) communities nodes
  in mergeCommunities optimizedCommunities

-- | 移动到最佳社区
moveToBestCommunity :: Int -> [Community] -> SocialNetwork -> [Community]
moveToBestCommunity node communities network = 
  let currentCommunity = findCommunity node communities
      possibleMoves = [comm | comm <- communities, comm /= currentCommunity]
      bestMove = maximumBy (compare `on` (\comm -> 
        modularityGain node currentCommunity comm network)) possibleMoves
  in if modularityGain node currentCommunity bestMove network > 0
     then moveNode node currentCommunity bestMove communities
     else communities

-- | 计算模块度增益
modularityGain :: Int -> Community -> Community -> SocialNetwork -> Double
modularityGain node fromComm toComm network = 
  let ki = fromIntegral (length (getNeighbors node network))
      ki_in = fromIntegral (internalConnections node toComm network)
      m = fromIntegral (length (edges network))
      deltaQ = (ki_in / m) - (ki * communityDegree toComm network) / (2 * m * m)
  in deltaQ
```

#### 2.2.2 标签传播算法

**算法 2.2.2** (标签传播)
标签传播算法通过迭代更新节点标签来发现社区。

**Haskell实现**：

```haskell
-- | 标签传播算法
labelPropagation :: SocialNetwork -> Map Int Int
labelPropagation network = 
  let initialLabels = Map.fromList [(i, i) | i <- [0..length (nodes network) - 1]]
  in iterateLabelPropagation network initialLabels

-- | 标签传播迭代
iterateLabelPropagation :: SocialNetwork -> Map Int Int -> Map Int Int
iterateLabelPropagation network labels = 
  let newLabels = updateLabels network labels
  in if newLabels == labels 
     then labels 
     else iterateLabelPropagation network newLabels

-- | 更新标签
updateLabels :: SocialNetwork -> Map Int Int -> Map Int Int
updateLabels network labels = 
  let nodes = [0..length (nodes network) - 1]
      shuffledNodes = shuffle nodes
  in foldl (\newLabels node -> 
    Map.insert node (mostFrequentLabel node network labels) newLabels) 
    labels shuffledNodes

-- | 最频繁标签
mostFrequentLabel :: Int -> SocialNetwork -> Map Int Int -> Int
mostFrequentLabel node network labels = 
  let neighbors = getNeighbors node network
      neighborLabels = [labels Map.! neighbor | neighbor <- neighbors]
      labelCounts = Map.fromListWith (+) [(label, 1) | label <- neighborLabels]
  in fst $ maximumBy (compare `on` snd) $ Map.toList labelCounts
```

## 3. 影响力分析

### 3.1 影响力传播模型

**定义 3.1.1** (独立级联模型)
在独立级联模型中，每个激活节点有一次机会以概率 $p_{uv}$ 激活其邻居。

**Haskell实现**：

```haskell
-- | 独立级联模型
data IndependentCascade = IndependentCascade
  { network :: SocialNetwork
  , activationProbabilities :: Map (Int, Int) Double
  , activatedNodes :: Set Int
  , newlyActivated :: Set Int
  } deriving (Show, Eq)

-- | 运行独立级联
runIndependentCascade :: IndependentCascade -> Int -> [Set Int]
runIndependentCascade ic steps = 
  take steps $ iterate stepCascade ic

-- | 级联步进
stepCascade :: IndependentCascade -> IndependentCascade
stepCascade ic = 
  let newActivations = Set.unions [tryActivate neighbor ic | 
                                   neighbor <- Set.toList (newlyActivated ic)]
  in ic { activatedNodes = Set.union (activatedNodes ic) newActivations
        , newlyActivated = newActivations }

-- | 尝试激活邻居
tryActivate :: Int -> IndependentCascade -> Set Int
tryActivate node ic = 
  let neighbors = getNeighbors node (network ic)
      activations = [neighbor | neighbor <- neighbors,
                               neighbor `Set.notMember` (activatedNodes ic),
                               randomIO < (activationProbabilities ic Map.! (node, neighbor))]
  in Set.fromList activations
```

### 3.2 影响力最大化

**问题 3.2.1** (影响力最大化)
给定预算 $k$，选择 $k$ 个种子节点，使得影响力传播最大化。

**Haskell实现**：

```haskell
-- | 影响力最大化
data InfluenceMaximization = InfluenceMaximization
  { network :: SocialNetwork
  , budget :: Int
  , cascadeModel :: CascadeModel
  } deriving (Show, Eq)

data CascadeModel = IndependentCascadeModel | LinearThresholdModel
  deriving (Show, Eq)

-- | 贪心算法
greedyInfluenceMaximization :: InfluenceMaximization -> [Int]
greedyInfluenceMaximization im = 
  let n = length (nodes (network im))
      candidates = [0..n-1]
  in greedySelect candidates (budget im) im

-- | 贪心选择
greedySelect :: [Int] -> Int -> InfluenceMaximization -> [Int]
greedySelect candidates k im = 
  if k <= 0 then [] else
    let bestNode = maximumBy (compare `on` (\node -> 
      marginalInfluence node (greedySelect candidates (k-1) im) im)) candidates
        remainingCandidates = filter (/= bestNode) candidates
    in bestNode : greedySelect remainingCandidates (k-1) im

-- | 边际影响力
marginalInfluence :: Int -> [Int] -> InfluenceMaximization -> Double
marginalInfluence node seedSet im = 
  let influenceWithNode = expectedInfluence (node:seedSet) im
      influenceWithoutNode = expectedInfluence seedSet im
  in influenceWithNode - influenceWithoutNode

-- | 期望影响力
expectedInfluence :: [Int] -> InfluenceMaximization -> Double
expectedInfluence seedSet im = 
  let simulations = 1000
      totalInfluence = sum [simulateCascade seedSet im | _ <- [1..simulations]]
  in totalInfluence / fromIntegral simulations

-- | 模拟级联
simulateCascade :: [Int] -> InfluenceMaximization -> Int
simulateCascade seedSet im = 
  let initialActivated = Set.fromList seedSet
      cascade = IndependentCascade (network im) Map.empty initialActivated initialActivated
      finalActivated = last $ runIndependentCascade cascade 10
  in Set.size finalActivated
```

## 4. 网络演化

### 4.1 网络增长模型

**定义 4.1.1** (优先连接模型)
新节点倾向于连接到度数高的现有节点。

**Haskell实现**：

```haskell
-- | 网络增长模型
data NetworkGrowth = NetworkGrowth
  { network :: SocialNetwork
  , growthRate :: Int  -- 每步添加的节点数
  , attachmentRule :: AttachmentRule
  } deriving (Show, Eq)

data AttachmentRule = PreferentialAttachment | RandomAttachment | Homophily
  deriving (Show, Eq)

-- | 模拟网络增长
simulateNetworkGrowth :: NetworkGrowth -> Int -> [SocialNetwork]
simulateNetworkGrowth ng steps = 
  scanl stepGrowth (network ng) [1..steps]

-- | 网络增长步进
stepGrowth :: SocialNetwork -> Int -> SocialNetwork
stepGrowth network step = 
  let newNodeId = length (nodes network)
      newUser = User newNodeId ("User" ++ show newNodeId) (utcNow)
      newEdges = generateNewEdges network newNodeId
  in network { nodes = nodes network ++ [newUser]
             , edges = edges network ++ newEdges }

-- | 生成新边
generateNewEdges :: SocialNetwork -> Int -> [(Int, Int, Double)]
generateNewEdges network newNodeId = 
  let existingNodes = [0..length (nodes network) - 1]
      targetNodes = selectTargetNodes existingNodes network
      weights = map (\_ -> randomRIO (0.1, 1.0)) targetNodes
  in zipWith (\target weight -> (newNodeId, target, weight)) targetNodes weights

-- | 选择目标节点
selectTargetNodes :: [Int] -> SocialNetwork -> [Int]
selectTargetNodes candidates network = 
  let degrees = map (\node -> (node, length (getNeighbors node network))) candidates
      totalDegree = sum [degree | (_, degree) <- degrees]
      probabilities = map (\(node, degree) -> 
        (node, fromIntegral degree / fromIntegral totalDegree)) degrees
  in weightedRandomSelection probabilities 3  -- 选择3个目标节点
```

### 4.2 同质性模型

**定义 4.2.1** (同质性)
相似的用户倾向于相互连接。

**Haskell实现**：

```haskell
-- | 同质性模型
data HomophilyModel = HomophilyModel
  { network :: SocialNetwork
  , similarityFunction :: SimilarityFunction
  , homophilyStrength :: Double
  } deriving (Show, Eq)

type SimilarityFunction = UserAttributes -> UserAttributes -> Double

-- | 计算用户相似性
userSimilarity :: UserAttributes -> UserAttributes -> Double
userSimilarity attr1 attr2 = 
  let ageSim = ageSimilarity (age attr1) (age attr2)
      locationSim = locationSimilarity (location attr1) (location attr2)
      interestSim = interestSimilarity (interests attr1) (interests attr2)
  in (ageSim + locationSim + interestSim) / 3.0

-- | 年龄相似性
ageSimilarity :: Maybe Int -> Maybe Int -> Double
ageSimilarity (Just age1) (Just age2) = 
  1.0 - min 1.0 (fromIntegral (abs (age1 - age2)) / 50.0)
ageSimilarity _ _ = 0.5

-- | 位置相似性
locationSimilarity :: Maybe String -> Maybe String -> Double
locationSimilarity (Just loc1) (Just loc2) = 
  if loc1 == loc2 then 1.0 else 0.0
locationSimilarity _ _ = 0.5

-- | 兴趣相似性
interestSimilarity :: [String] -> [String] -> Double
interestSimilarity interests1 interests2 = 
  let intersection = length (intersect interests1 interests2)
      union = length (union interests1 interests2)
  in if union > 0 then fromIntegral intersection / fromIntegral union else 0.0

-- | 基于同质性的连接概率
homophilyConnectionProbability :: Int -> Int -> HomophilyModel -> Double
homophilyConnectionProbability user1 user2 model = 
  let attr1 = attributes (network model) Map.! user1
      attr2 = attributes (network model) Map.! user2
      similarity = similarityFunction model attr1 attr2
      strength = homophilyStrength model
  in similarity * strength
```

## 5. 情感分析

### 5.1 情感传播

**定义 5.1.1** (情感传播)
情感在网络中的传播和演化过程。

**Haskell实现**：

```haskell
-- | 情感状态
data Sentiment = Positive | Negative | Neutral
  deriving (Show, Eq, Enum)

-- | 情感传播模型
data SentimentPropagation = SentimentPropagation
  { network :: SocialNetwork
  , userSentiments :: Map Int Sentiment
  , influenceWeights :: Map (Int, Int) Double
  , sentimentStrength :: Map Int Double
  } deriving (Show, Eq)

-- | 情感传播步进
stepSentimentPropagation :: SentimentPropagation -> SentimentPropagation
stepSentimentPropagation sp = 
  let newSentiments = Map.mapWithKey (\userId sentiment -> 
    updateSentiment userId sentiment sp) (userSentiments sp)
  in sp { userSentiments = newSentiments }

-- | 更新情感
updateSentiment :: Int -> Sentiment -> SentimentPropagation -> Sentiment
updateSentiment userId currentSentiment sp = 
  let neighbors = getNeighbors userId (network sp)
      neighborInfluences = [influenceWeight userId neighbor sp | neighbor <- neighbors]
      totalInfluence = sum neighborInfluences
      sentimentShift = sum [sentimentInfluence userId neighbor sp | neighbor <- neighbors]
  in if abs sentimentShift > threshold
     then if sentimentShift > 0 then Positive else Negative
     else currentSentiment
  where
    threshold = 0.5

-- | 情感影响力
sentimentInfluence :: Int -> Int -> SentimentPropagation -> Double
sentimentInfluence user1 user2 sp = 
  let weight = influenceWeights sp Map.! (user1, user2)
      sentiment1 = userSentiments sp Map.! user1
      sentiment2 = userSentiments sp Map.! user2
      strength1 = sentimentStrength sp Map.! user1
  in weight * strength1 * sentimentDifference sentiment1 sentiment2

-- | 情感差异
sentimentDifference :: Sentiment -> Sentiment -> Double
sentimentDifference s1 s2 = 
  fromIntegral (fromEnum s1 - fromEnum s2) / 2.0
```

## 6. 应用实例

### 6.1 推荐系统

**应用 6.1.1** (基于网络的推荐)
利用社交网络结构进行推荐。

```haskell
-- | 社交推荐系统
data SocialRecommender = SocialRecommender
  { network :: SocialNetwork
  , userPreferences :: Map Int [String]
  , itemRatings :: Map (Int, String) Double
  } deriving (Show, Eq)

-- | 基于朋友的推荐
friendBasedRecommendation :: Int -> SocialRecommender -> [String]
friendBasedRecommendation userId recommender = 
  let friends = getNeighbors userId (network recommender)
      friendPreferences = concat [userPreferences recommender Map.! friend | friend <- friends]
      itemScores = Map.fromListWith (+) [(item, 1.0) | item <- friendPreferences]
  in map fst $ sortBy (flip compare `on` snd) $ Map.toList itemScores

-- | 协同过滤推荐
collaborativeFiltering :: Int -> SocialRecommender -> [String]
collaborativeFiltering userId recommender = 
  let similarUsers = findSimilarUsers userId recommender
      recommendations = aggregateRecommendations similarUsers recommender
  in recommendations

-- | 找到相似用户
findSimilarUsers :: Int -> SocialRecommender -> [Int]
findSimilarUsers userId recommender = 
  let allUsers = [0..length (nodes (network recommender)) - 1]
      similarities = [(user, userSimilarity userId user recommender) | user <- allUsers, user /= userId]
  in map fst $ sortBy (flip compare `on` snd) similarities
```

### 6.2 谣言检测

**应用 6.2.1** (谣言传播检测)
检测和分析谣言在网络中的传播。

```haskell
-- | 谣言检测系统
data RumorDetection = RumorDetection
  { network :: SocialNetwork
  , rumorPatterns :: [RumorPattern]
  , detectionRules :: [DetectionRule]
  } deriving (Show, Eq)

data RumorPattern = RumorPattern
  { keywords :: [String]
  , propagationSpeed :: Double
  , userCharacteristics :: [String]
  } deriving (Show, Eq)

data DetectionRule = DetectionRule
  { ruleName :: String
  , threshold :: Double
  , weight :: Double
  } deriving (Show, Eq)

-- | 谣言检测
detectRumor :: String -> RumorDetection -> Double
detectRumor content detection = 
  let keywordScore = keywordMatching content (rumorPatterns detection)
      propagationScore = propagationAnalysis detection
      userScore = userBehaviorAnalysis detection
      finalScore = weightedAverage [keywordScore, propagationScore, userScore] 
                                   [0.4, 0.3, 0.3]
  in finalScore

-- | 关键词匹配
keywordMatching :: String -> [RumorPattern] -> Double
keywordMatching content patterns = 
  let matches = [pattern | pattern <- patterns, 
                         any (`isInfixOf` content) (keywords pattern)]
      scores = [propagationSpeed pattern | pattern <- matches]
  in if null scores then 0.0 else maximum scores
```

## 7. 总结

社交网络分析提供了理解人际关系网络的强大工具。通过形式化建模和Haskell实现，我们可以：

1. **分析网络结构**：理解社交网络的组织方式
2. **发现社区**：识别网络中的紧密连接群体
3. **评估影响力**：分析用户在网络中的影响力
4. **预测传播**：预测信息、行为在网络中的传播
5. **构建应用**：开发推荐系统、谣言检测等应用

这些理论和方法在社交媒体、市场营销、公共卫生等领域都有重要应用。

---

**参考文献**：

1. Wasserman, S., & Faust, K. (1994). Social Network Analysis: Methods and Applications. Cambridge University Press.
2. Newman, M. E. J. (2010). Networks: An Introduction. Oxford University Press.
3. Kempe, D., Kleinberg, J., & Tardos, É. (2003). Maximizing the spread of influence through a social network. KDD '03.
