# 传感器网络

## 概述

传感器网络是由大量分布式传感器节点组成的网络，用于收集、处理和传输环境数据。本节将建立传感器网络的形式化理论框架，并提供Haskell实现。

## 1. 传感器节点

### 1.1 节点结构

**定义 1.1.1** (传感器节点)
传感器节点是网络的基本单元，包含感知、处理、通信和能量管理模块。

**Haskell实现**：

```haskell
-- | 传感器节点
data SensorNode = SensorNode
  { nodeId :: NodeId
  , position :: Position
  , sensors :: [Sensor]
  , energy :: Double
  , neighbors :: [NodeId]
  } deriving (Show, Eq)

type NodeId = Int

data Position = Position
  { x :: Double
  , y :: Double
  , z :: Double
  } deriving (Show, Eq)

-- | 传感器类型
data Sensor = TemperatureSensor
            | HumiditySensor
            | PressureSensor
            | LightSensor
            | MotionSensor
            deriving (Show, Eq)

-- | 传感器读数
data SensorReading = SensorReading
  { sensor :: Sensor
  , value :: Double
  , timestamp :: UTCTime
  , quality :: Double
  } deriving (Show, Eq)

-- | 创建传感器节点
createSensorNode :: NodeId -> Position -> [Sensor] -> Double -> SensorNode
createSensorNode id pos sensors initialEnergy = SensorNode
  { nodeId = id
  , position = pos
  , sensors = sensors
  , energy = initialEnergy
  , neighbors = []
  }

-- | 获取传感器读数
getSensorReading :: SensorNode -> Sensor -> IO SensorReading
getSensorReading node sensor = do
  let value = simulateSensorValue sensor
      quality = calculateQuality node sensor
  return $ SensorReading sensor value (utcNow) quality

-- | 模拟传感器值
simulateSensorValue :: Sensor -> Double
simulateSensorValue sensor = 
  case sensor of
    TemperatureSensor -> randomRIO (15.0, 35.0)
    HumiditySensor -> randomRIO (30.0, 80.0)
    PressureSensor -> randomRIO (980.0, 1020.0)
    LightSensor -> randomRIO (0.0, 1000.0)
    MotionSensor -> randomRIO (0.0, 1.0)

-- | 计算数据质量
calculateQuality :: SensorNode -> Sensor -> Double
calculateQuality node sensor = 
  let energyFactor = energy node / 100.0  -- 假设最大能量为100
      sensorAge = 1.0  -- 简化的传感器年龄因子
  in min 1.0 (energyFactor * sensorAge)
```

### 1.2 能量管理

**定义 1.2.1** (能量消耗模型)
传感器节点的能量消耗包括感知、处理和通信消耗：

$$E_{total} = E_{sensing} + E_{processing} + E_{communication}$$

**Haskell实现**：

```haskell
-- | 能量消耗模型
data EnergyModel = EnergyModel
  { sensingPower :: Double
  , processingPower :: Double
  , transmissionPower :: Double
  , receptionPower :: Double
  } deriving (Show, Eq)

-- | 能量消耗
data EnergyConsumption = EnergyConsumption
  { sensing :: Double
  , processing :: Double
  , transmission :: Double
  , reception :: Double
  } deriving (Show, Eq)

-- | 计算能量消耗
calculateEnergyConsumption :: SensorNode -> EnergyModel -> Double -> EnergyConsumption
calculateEnergyConsumption node model duration = 
  let sensing = sensingPower model * duration
      processing = processingPower model * duration
      transmission = transmissionPower model * duration
      reception = receptionPower model * duration
  in EnergyConsumption sensing processing transmission reception

-- | 更新节点能量
updateNodeEnergy :: SensorNode -> EnergyConsumption -> SensorNode
updateNodeEnergy node consumption = 
  let totalConsumption = sensing consumption + processing consumption + 
                        transmission consumption + reception consumption
      newEnergy = max 0.0 (energy node - totalConsumption)
  in node { energy = newEnergy }

-- | 检查节点存活
isNodeAlive :: SensorNode -> Bool
isNodeAlive node = energy node > 0.0

-- | 能量效率路由
energyEfficientRouting :: [SensorNode] -> NodeId -> NodeId -> [NodeId]
energyEfficientRouting nodes source target = 
  let aliveNodes = filter isNodeAlive nodes
      distances = [(nodeId node, calculateDistance (findNode source nodes) node) | node <- aliveNodes]
      sortedNodes = sortBy (compare `on` snd) distances
  in map fst sortedNodes

-- | 计算距离
calculateDistance :: SensorNode -> SensorNode -> Double
calculateDistance node1 node2 = 
  let pos1 = position node1
      pos2 = position node2
      dx = x pos1 - x pos2
      dy = y pos1 - y pos2
      dz = z pos1 - z pos2
  in sqrt (dx^2 + dy^2 + dz^2)

-- | 查找节点
findNode :: NodeId -> [SensorNode] -> SensorNode
findNode id nodes = 
  case find (\node -> nodeId node == id) nodes of
    Just node -> node
    Nothing -> error "Node not found"
```

## 2. 网络拓扑

### 2.1 拓扑结构

**定义 2.1.1** (网络拓扑)
传感器网络的拓扑结构决定了节点间的连接关系和数据传输路径。

**Haskell实现**：

```haskell
-- | 网络拓扑
data NetworkTopology = StarTopology NodeId
                     | MeshTopology
                     | TreeTopology NodeId
                     | ClusterTopology [Cluster]
                     deriving (Show, Eq)

data Cluster = Cluster
  { clusterId :: Int
  , clusterHead :: NodeId
  , members :: [NodeId]
  } deriving (Show, Eq)

-- | 星形拓扑
createStarTopology :: [SensorNode] -> NodeId -> NetworkTopology
createStarTopology nodes centerId = 
  let updatedNodes = map (\node -> 
    if nodeId node == centerId
    then node { neighbors = [nodeId n | n <- nodes, nodeId n /= centerId] }
    else node { neighbors = [centerId] }) nodes
  in StarTopology centerId

-- | 网状拓扑
createMeshTopology :: [SensorNode] -> Double -> NetworkTopology
createMeshTopology nodes maxDistance = 
  let updatedNodes = map (\node -> 
    let nearbyNodes = [nodeId n | n <- nodes, 
                                 nodeId n /= nodeId node,
                                 calculateDistance node n <= maxDistance]
    in node { neighbors = nearbyNodes }) nodes
  in MeshTopology

-- | 树形拓扑
createTreeTopology :: [SensorNode] -> NodeId -> NetworkTopology
createTreeTopology nodes rootId = 
  let tree = buildTree nodes rootId []
      updatedNodes = map (\node -> 
        let children = findChildren (nodeId node) tree
        in node { neighbors = children }) nodes
  in TreeTopology rootId

-- | 构建树
buildTree :: [SensorNode] -> NodeId -> [(NodeId, NodeId)] -> [(NodeId, NodeId)]
buildTree nodes parentId edges = 
  let unassignedNodes = filter (\node -> 
    nodeId node /= parentId && not (any (\(_, child) -> child == nodeId node) edges)) nodes
      nearbyNodes = filter (\node -> 
        calculateDistance (findNode parentId nodes) node <= 50.0) unassignedNodes
  in if null nearbyNodes
     then edges
     else let child = head nearbyNodes
              newEdges = edges ++ [(parentId, nodeId child)]
          in buildTree nodes (nodeId child) newEdges

-- | 查找子节点
findChildren :: NodeId -> [(NodeId, NodeId)] -> [NodeId]
findChildren parentId edges = 
  [child | (parent, child) <- edges, parent == parentId]

-- | 分簇拓扑
createClusterTopology :: [SensorNode] -> Int -> NetworkTopology
createClusterTopology nodes numClusters = 
  let clusters = kMeansClustering nodes numClusters
      clusterHeads = selectClusterHeads clusters
      updatedNodes = assignToClusters nodes clusters clusterHeads
  in ClusterTopology clusters

-- | K-means聚类
kMeansClustering :: [SensorNode] -> Int -> [Cluster]
kMeansClustering nodes k = 
  let initialCenters = take k nodes
      clusters = iterate (\clusters -> updateClusters nodes clusters) 
                        (map (\node -> Cluster (nodeId node) (nodeId node) [nodeId node]) initialCenters)
  in clusters !! 10  -- 迭代10次

-- | 更新聚类
updateClusters :: [SensorNode] -> [Cluster] -> [Cluster]
updateClusters nodes clusters = 
  let assignments = assignNodesToClusters nodes clusters
      newClusters = map (\cluster -> 
        let clusterNodes = filter (\node -> nodeId node `elem` members cluster) nodes
            newCenter = calculateClusterCenter clusterNodes
        in cluster { clusterHead = nodeId newCenter }) clusters
  in newClusters

-- | 分配节点到聚类
assignNodesToClusters :: [SensorNode] -> [Cluster] -> [(NodeId, Int)]
assignNodesToClusters nodes clusters = 
  [(nodeId node, findNearestCluster node clusters) | node <- nodes]

-- | 查找最近聚类
findNearestCluster :: SensorNode -> [Cluster] -> Int
findNearestCluster node clusters = 
  let distances = [(clusterId cluster, calculateDistanceToCluster node cluster) | cluster <- clusters]
  in fst $ minimumBy (compare `on` snd) distances

-- | 计算到聚类的距离
calculateDistanceToCluster :: SensorNode -> Cluster -> Double
calculateDistanceToCluster node cluster = 
  let clusterNodes = filter (\n -> nodeId n `elem` members cluster) []
      center = calculateClusterCenter clusterNodes
  in calculateDistance node center

-- | 计算聚类中心
calculateClusterCenter :: [SensorNode] -> SensorNode
calculateClusterCenter nodes = 
  let avgX = sum [x (position node) | node <- nodes] / fromIntegral (length nodes)
      avgY = sum [y (position node) | node <- nodes] / fromIntegral (length nodes)
      avgZ = sum [z (position node) | node <- nodes] / fromIntegral (length nodes)
      centerPos = Position avgX avgY avgZ
  in head nodes { position = centerPos }
```

### 2.2 路由协议

**定义 2.2.1** (路由协议)
路由协议决定数据在网络中的传输路径。

**Haskell实现**：

```haskell
-- | 路由协议
data RoutingProtocol = Flooding
                     | Gossiping
                     | SPIN
                     | LEACH
                     deriving (Show, Eq)

-- | 路由表
data RoutingTable = RoutingTable
  { destination :: NodeId
  , nextHop :: NodeId
  , cost :: Double
  } deriving (Show, Eq)

-- | 洪泛路由
floodingRouting :: [SensorNode] -> NodeId -> NodeId -> [NodeId]
floodingRouting nodes source target = 
  let allNodes = [nodeId node | node <- nodes]
  in allNodes

-- | 闲聊路由
gossipingRouting :: [SensorNode] -> NodeId -> NodeId -> [NodeId]
gossipingRouting nodes source target = 
  let sourceNode = findNode source nodes
      neighbors = neighbors sourceNode
      randomNeighbor = neighbors !! (randomRIO (0, length neighbors - 1))
  in [randomNeighbor]

-- | SPIN路由
spinRouting :: [SensorNode] -> NodeId -> NodeId -> [NodeId]
spinRouting nodes source target = 
  let sourceNode = findNode source nodes
      neighbors = neighbors sourceNode
      -- SPIN使用元数据协商
      interestedNeighbors = filter (\neighbor -> 
        isInterestedInData neighbor target) neighbors
  in interestedNeighbors

-- | 检查节点是否对数据感兴趣
isInterestedInData :: NodeId -> NodeId -> Bool
isInterestedInData nodeId targetId = 
  -- 简化的兴趣检查
  nodeId /= targetId

-- | LEACH路由
leachRouting :: [SensorNode] -> [Cluster] -> NodeId -> NodeId -> [NodeId]
leachRouting nodes clusters source target = 
  let sourceCluster = findClusterByNode source clusters
      clusterHead = clusterHead sourceCluster
  in [clusterHead]
```

## 3. 数据收集

### 3.1 数据聚合

**定义 3.1.1** (数据聚合)
数据聚合将多个节点的数据合并，减少传输量和能量消耗。

**Haskell实现**：

```haskell
-- | 数据聚合
data DataAggregation = DataAggregation
  { aggregationType :: AggregationType
  , dataPoints :: [SensorReading]
  , result :: Double
  } deriving (Show, Eq)

data AggregationType = Average | Sum | Min | Max | Median
  deriving (Show, Eq)

-- | 执行数据聚合
performAggregation :: [SensorReading] -> AggregationType -> DataAggregation
performAggregation readings aggType = 
  let result = case aggType of
                 Average -> sum (map value readings) / fromIntegral (length readings)
                 Sum -> sum (map value readings)
                 Min -> minimum (map value readings)
                 Max -> maximum (map value readings)
                 Median -> calculateMedian (map value readings)
  in DataAggregation aggType readings result

-- | 计算中位数
calculateMedian :: [Double] -> Double
calculateMedian values = 
  let sorted = sort values
      n = length sorted
  in if odd n
     then sorted !! (n `div` 2)
     else (sorted !! (n `div` 2 - 1) + sorted !! (n `div` 2)) / 2

-- | 分层数据聚合
hierarchicalAggregation :: [SensorNode] -> [Cluster] -> AggregationType -> [DataAggregation]
hierarchicalAggregation nodes clusters aggType = 
  let clusterAggregations = map (\cluster -> 
    let clusterNodes = filter (\node -> nodeId node `elem` members cluster) nodes
        clusterReadings = concatMap (\node -> getNodeReadings node) clusterNodes
    in performAggregation clusterReadings aggType) clusters
  in clusterAggregations

-- | 获取节点读数
getNodeReadings :: SensorNode -> [SensorReading]
getNodeReadings node = 
  -- 简化的读数获取
  [SensorReading (head (sensors node)) 25.0 (utcNow) 0.9]
```

### 3.2 数据压缩

**定义 3.2.1** (数据压缩)
数据压缩减少传输数据量，节省能量。

**Haskell实现**：

```haskell
-- | 数据压缩
data DataCompression = DataCompression
  { compressionType :: CompressionType
  , originalData :: [Double]
  , compressedData :: [Double]
  , compressionRatio :: Double
  } deriving (Show, Eq)

data CompressionType = DeltaEncoding | HuffmanCoding | WaveletTransform
  deriving (Show, Eq)

-- | Delta编码
deltaEncoding :: [Double] -> DataCompression
deltaEncoding data = 
  let deltas = zipWith (-) data (0 : init data)
      compressed = filter (/= 0) deltas
      ratio = fromIntegral (length compressed) / fromIntegral (length data)
  in DataCompression DeltaEncoding data compressed ratio

-- | 小波变换压缩
waveletCompression :: [Double] -> Double -> DataCompression
waveletCompression data threshold = 
  let coefficients = waveletTransform data
      compressed = filter (\c -> abs c > threshold) coefficients
      ratio = fromIntegral (length compressed) / fromIntegral (length data)
  in DataCompression WaveletTransform data compressed ratio

-- | 小波变换
waveletTransform :: [Double] -> [Double]
waveletTransform data = 
  -- 简化的Haar小波变换
  let n = length data
      if n <= 1
      then data
      else let (approximation, detail) = haarDecomposition data
               compressedApprox = waveletTransform approximation
               compressedDetail = waveletTransform detail
           in compressedApprox ++ compressedDetail

-- | Haar小波分解
haarDecomposition :: [Double] -> ([Double], [Double])
haarDecomposition data = 
  let n = length data
      approximation = [(data !! (2*i) + data !! (2*i+1)) / 2 | i <- [0..n`div`2-1]]
      detail = [(data !! (2*i) - data !! (2*i+1)) / 2 | i <- [0..n`div`2-1]]
  in (approximation, detail)
```

## 4. 网络管理

### 4.1 拓扑控制

**定义 4.1.1** (拓扑控制)
拓扑控制优化网络连接，提高能量效率和网络性能。

**Haskell实现**：

```haskell
-- | 拓扑控制
data TopologyControl = TopologyControl
  { controlType :: ControlType
  , nodes :: [SensorNode]
  , optimizedTopology :: NetworkTopology
  } deriving (Show, Eq)

data ControlType = PowerControl | SleepScheduling | Clustering
  deriving (Show, Eq)

-- | 功率控制
powerControl :: [SensorNode] -> Double -> [SensorNode]
powerControl nodes targetConnectivity = 
  let updatedNodes = map (\node -> 
    let requiredPower = calculateRequiredPower node targetConnectivity
    in node { energy = min (energy node) requiredPower }) nodes
  in updatedNodes

-- | 计算所需功率
calculateRequiredPower :: SensorNode -> Double -> Double
calculateRequiredPower node connectivity = 
  let currentNeighbors = length (neighbors node)
      requiredNeighbors = round (connectivity * fromIntegral currentNeighbors)
      powerPerNeighbor = 1.0
  in fromIntegral requiredNeighbors * powerPerNeighbor

-- | 睡眠调度
sleepScheduling :: [SensorNode] -> Double -> [SensorNode]
sleepScheduling nodes dutyCycle = 
  let updatedNodes = map (\node -> 
    let shouldSleep = randomRIO (0, 1) > dutyCycle
    in if shouldSleep
       then node { energy = energy node * 0.1 }  -- 睡眠时消耗较少能量
       else node) nodes
  in updatedNodes

-- | 动态分簇
dynamicClustering :: [SensorNode] -> [Cluster]
dynamicClustering nodes = 
  let numClusters = max 1 (length nodes `div` 10)
      clusters = kMeansClustering nodes numClusters
      optimizedClusters = optimizeClusterHeads clusters nodes
  in optimizedClusters

-- | 优化簇头选择
optimizeClusterHeads :: [Cluster] -> [SensorNode] -> [Cluster]
optimizeClusterHeads clusters nodes = 
  map (\cluster -> 
    let clusterNodes = filter (\node -> nodeId node `elem` members cluster) nodes
        bestHead = selectBestClusterHead clusterNodes
    in cluster { clusterHead = nodeId bestHead }) clusters

-- | 选择最佳簇头
selectBestClusterHead :: [SensorNode] -> SensorNode
selectBestClusterHead nodes = 
  let scores = [(node, calculateClusterHeadScore node) | node <- nodes]
  in fst $ maximumBy (compare `on` snd) scores

-- | 计算簇头评分
calculateClusterHeadScore :: SensorNode -> Double
calculateClusterHeadScore node = 
  let energyScore = energy node / 100.0
      centralityScore = calculateCentrality node
  in energyScore * 0.7 + centralityScore * 0.3

-- | 计算中心性
calculateCentrality :: SensorNode -> Double
calculateCentrality node = 
  fromIntegral (length (neighbors node)) / 10.0  -- 简化的中心性计算
```

### 4.2 故障检测

**定义 4.2.1** (故障检测)
故障检测识别网络中的故障节点和连接问题。

**Haskell实现**：

```haskell
-- | 故障检测
data FaultDetection = FaultDetection
  { detectionType :: DetectionType
  , faultyNodes :: [NodeId]
  , networkHealth :: Double
  } deriving (Show, Eq)

data DetectionType = Heartbeat | NeighborMonitoring | DataAnomaly
  deriving (Show, Eq)

-- | 心跳检测
heartbeatDetection :: [SensorNode] -> Double -> FaultDetection
heartbeatDetection nodes timeout = 
  let currentTime = utcNow
      faultyNodes = [nodeId node | node <- nodes, 
                                  not (isNodeAlive node) || 
                                  isNodeUnresponsive node timeout]
      health = 1.0 - fromIntegral (length faultyNodes) / fromIntegral (length nodes)
  in FaultDetection Heartbeat faultyNodes health

-- | 检查节点无响应
isNodeUnresponsive :: SensorNode -> Double -> Bool
isNodeUnresponsive node timeout = 
  -- 简化的响应检查
  energy node < 10.0

-- | 邻居监控
neighborMonitoring :: [SensorNode] -> FaultDetection
neighborMonitoring nodes = 
  let faultyNodes = [nodeId node | node <- nodes, 
                                  length (neighbors node) == 0 && 
                                  energy node > 0]
      health = 1.0 - fromIntegral (length faultyNodes) / fromIntegral (length nodes)
  in FaultDetection NeighborMonitoring faultyNodes health

-- | 数据异常检测
dataAnomalyDetection :: [SensorNode] -> FaultDetection
dataAnomalyDetection nodes = 
  let readings = concatMap (\node -> getNodeReadings node) nodes
      anomalies = detectAnomalies readings
      faultyNodes = map (\anomaly -> findNodeByReading anomaly nodes) anomalies
      health = 1.0 - fromIntegral (length faultyNodes) / fromIntegral (length nodes)
  in FaultDetection DataAnomaly faultyNodes health

-- | 检测异常
detectAnomalies :: [SensorReading] -> [SensorReading]
detectAnomalies readings = 
  let values = map value readings
      mean = sum values / fromIntegral (length values)
      std = sqrt (sum [(v - mean)^2 | v <- values] / fromIntegral (length values))
      threshold = 2.0 * std
      anomalies = filter (\reading -> abs (value reading - mean) > threshold) readings
  in anomalies

-- | 根据读数查找节点
findNodeByReading :: SensorReading -> [SensorNode] -> NodeId
findNodeByReading reading nodes = 
  -- 简化的节点查找
  nodeId (head nodes)
```

## 5. 应用实例

### 5.1 环境监测

**应用 5.1.1** (环境监测网络)
监测温度、湿度、空气质量等环境参数。

```haskell
-- | 环境监测网络
data EnvironmentalMonitoring = EnvironmentalMonitoring
  { network :: [SensorNode]
  , monitoringArea :: Area
  , dataCollection :: [EnvironmentalData]
  } deriving (Show, Eq)

data Area = Area
  { minX :: Double
  , maxX :: Double
  , minY :: Double
  , maxY :: Double
  } deriving (Show, Eq)

data EnvironmentalData = EnvironmentalData
  { temperature :: Double
  , humidity :: Double
  , pressure :: Double
  , airQuality :: Double
  , location :: Position
  , timestamp :: UTCTime
  } deriving (Show, Eq)

-- | 部署环境监测网络
deployEnvironmentalNetwork :: Area -> Int -> EnvironmentalMonitoring
deployEnvironmentalNetwork area numNodes = 
  let nodes = [createEnvironmentalNode i area | i <- [0..numNodes-1]]
      topology = createMeshTopology nodes 100.0
      dataCollection = []
  in EnvironmentalMonitoring nodes area dataCollection

-- | 创建环境监测节点
createEnvironmentalNode :: Int -> Area -> SensorNode
createEnvironmentalNode id area = 
  let position = Position (randomRIO (minX area, maxX area))
                         (randomRIO (minY area, maxY area))
                         0.0
      sensors = [TemperatureSensor, HumiditySensor, PressureSensor, LightSensor]
  in createSensorNode id position sensors 100.0

-- | 收集环境数据
collectEnvironmentalData :: EnvironmentalMonitoring -> IO EnvironmentalMonitoring
collectEnvironmentalData monitoring = 
  let aliveNodes = filter isNodeAlive (network monitoring)
      environmentalData = map (\node -> 
        let readings = getNodeReadings node
            temp = findReading TemperatureSensor readings
            humidity = findReading HumiditySensor readings
            pressure = findReading PressureSensor readings
            light = findReading LightSensor readings
        in EnvironmentalData temp humidity pressure light (position node) (utcNow)) aliveNodes
  in return monitoring { dataCollection = environmentalData }

-- | 查找特定传感器读数
findReading :: Sensor -> [SensorReading] -> Double
findReading targetSensor readings = 
  case find (\reading -> sensor reading == targetSensor) readings of
    Just reading -> value reading
    Nothing -> 0.0
```

### 5.2 智能农业

**应用 5.2.1** (智能农业监测)
监测土壤湿度、温度、光照等农业参数。

```haskell
-- | 智能农业网络
data SmartAgriculture = SmartAgriculture
  { network :: [SensorNode]
  , cropType :: String
  , irrigationSystem :: IrrigationSystem
  } deriving (Show, Eq)

data IrrigationSystem = IrrigationSystem
  { zones :: [IrrigationZone]
  , schedule :: IrrigationSchedule
  } deriving (Show, Eq)

data IrrigationZone = IrrigationZone
  { zoneId :: Int
  , nodes :: [NodeId]
  , moistureThreshold :: Double
  } deriving (Show, Eq)

data IrrigationSchedule = IrrigationSchedule
  { frequency :: Int  -- 小时
  , duration :: Int   -- 分钟
  , active :: Bool
  } deriving (Show, Eq)

-- | 智能灌溉决策
smartIrrigationDecision :: SmartAgriculture -> [IrrigationDecision]
smartIrrigationDecision agriculture = 
  let zones = zones (irrigationSystem agriculture)
      decisions = map (\zone -> 
        let zoneNodes = filter (\node -> nodeId node `elem` nodes zone) (network agriculture)
            avgMoisture = calculateAverageMoisture zoneNodes
            shouldIrrigate = avgMoisture < moistureThreshold zone
        in IrrigationDecision (zoneId zone) shouldIrrigate avgMoisture) zones
  in decisions

-- | 灌溉决策
data IrrigationDecision = IrrigationDecision
  { zoneId :: Int
  , shouldIrrigate :: Bool
  , currentMoisture :: Double
  } deriving (Show, Eq)

-- | 计算平均湿度
calculateAverageMoisture :: [SensorNode] -> Double
calculateAverageMoisture nodes = 
  let moistureReadings = [findReading HumiditySensor (getNodeReadings node) | node <- nodes]
  in sum moistureReadings / fromIntegral (length moistureReadings)
```

## 6. 总结

传感器网络为物联网提供了基础的数据收集和处理能力。通过形式化建模和Haskell实现，我们可以：

1. **设计传感器节点**：优化感知、处理和通信能力
2. **管理网络拓扑**：实现高效的数据传输
3. **聚合和压缩数据**：减少能量消耗
4. **检测和处理故障**：保证网络可靠性
5. **支持应用开发**：环境监测、智能农业等

这些技术在现代物联网应用中发挥着关键作用。

---

**参考文献**：

1. Akyildiz, I. F., Su, W., Sankarasubramaniam, Y., & Cayirci, E. (2002). A survey on sensor networks. IEEE Communications Magazine, 40(8), 102-114.
2. Heinzelman, W. R., Chandrakasan, A., & Balakrishnan, H. (2000). Energy-efficient communication protocol for wireless microsensor networks. IEEE Computer Society.
3. Intanagonwiwat, C., Govindan, R., & Estrin, D. (2000). Directed diffusion: a scalable and robust communication paradigm for sensor networks. ACM MobiCom.
