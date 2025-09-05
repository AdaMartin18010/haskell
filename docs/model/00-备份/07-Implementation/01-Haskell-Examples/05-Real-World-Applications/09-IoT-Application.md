# 物联网应用 - Haskell实现

## 概述

本文档提供了一个完整的物联网应用的Haskell实现，包括设备管理、数据收集、处理规则、边缘计算等核心组件。

## 1. 基础数据结构

```haskell
{-# LANGUAGE GADTs, TypeFamilies, FlexibleContexts, DeriveGeneric #-}

module IoT.Core.DataStructures where

import Data.Time (UTCTime)
import Data.Text (Text)
import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)
import Data.Map (Map)
import qualified Data.Map as Map

-- 设备类型
data DeviceType = 
  Sensor
  | Actuator
  | Gateway
  | Controller
  deriving (Show, Eq, Generic)

instance ToJSON DeviceType
instance FromJSON DeviceType

-- 传感器类型
data SensorType = 
  Temperature
  | Humidity
  | Pressure
  | Light
  | Motion
  | Gas
  | Custom Text
  deriving (Show, Eq, Generic)

instance ToJSON SensorType
instance FromJSON SensorType

-- 设备
data Device = Device
  { deviceId :: DeviceId
  , deviceType :: DeviceType
  , name :: Text
  , location :: Location
  , status :: DeviceStatus
  , capabilities :: [Capability]
  , lastSeen :: UTCTime
  } deriving (Show, Eq, Generic)

instance ToJSON Device
instance FromJSON Device

-- 设备ID
newtype DeviceId = DeviceId { unDeviceId :: Text }
  deriving (Show, Eq, Ord)

-- 位置信息
data Location = Location
  { latitude :: Double
  , longitude :: Double
  , altitude :: Double
  , description :: Text
  } deriving (Show, Eq, Generic)

instance ToJSON Location
instance FromJSON Location

-- 设备状态
data DeviceStatus = 
  Online
  | Offline
  | Error
  | Maintenance
  deriving (Show, Eq, Generic)

instance ToJSON DeviceStatus
instance FromJSON DeviceStatus

-- 设备能力
data Capability = Capability
  { capabilityName :: Text
  , capabilityType :: Text
  , parameters :: Map Text Text
  } deriving (Show, Eq, Generic)

instance ToJSON Capability
instance FromJSON Capability

-- 传感器数据
data SensorData = SensorData
  { sensorId :: DeviceId
  , sensorType :: SensorType
  , value :: Double
  , unit :: Text
  , timestamp :: UTCTime
  , quality :: DataQuality
  } deriving (Show, Eq, Generic)

instance ToJSON SensorData
instance FromJSON SensorData

-- 数据质量
data DataQuality = 
  Excellent
  | Good
  | Fair
  | Poor
  | Invalid
  deriving (Show, Eq, Generic)

instance ToJSON DataQuality
instance FromJSON DataQuality

-- 执行器命令
data ActuatorCommand = ActuatorCommand
  { actuatorId :: DeviceId
  , command :: Text
  , parameters :: Map Text Text
  , timestamp :: UTCTime
  , priority :: Priority
  } deriving (Show, Eq, Generic)

instance ToJSON ActuatorCommand
instance FromJSON ActuatorCommand

-- 优先级
data Priority = 
  Low
  | Normal
  | High
  | Critical
  deriving (Show, Eq, Generic)

instance ToJSON Priority
instance FromJSON Priority

-- 处理规则
data ProcessingRule = ProcessingRule
  { ruleId :: RuleId
  , name :: Text
  , condition :: Condition
  , action :: Action
  , enabled :: Bool
  , priority :: Priority
  } deriving (Show, Eq, Generic)

instance ToJSON ProcessingRule
instance FromJSON ProcessingRule

-- 规则ID
newtype RuleId = RuleId { unRuleId :: Text }
  deriving (Show, Eq, Ord)

-- 条件
data Condition = 
  ThresholdCondition DeviceId SensorType Double Comparison
  | TimeCondition TimeRange
  | LogicalCondition LogicalOperator [Condition]
  | CustomCondition Text
  deriving (Show, Eq, Generic)

instance ToJSON Condition
instance FromJSON Condition

-- 比较操作符
data Comparison = 
  GreaterThan
  | LessThan
  | Equal
  | NotEqual
  | GreaterThanOrEqual
  | LessThanOrEqual
  deriving (Show, Eq, Generic)

instance ToJSON Comparison
instance FromJSON Comparison

-- 时间范围
data TimeRange = TimeRange
  { startTime :: UTCTime
  , endTime :: UTCTime
  } deriving (Show, Eq, Generic)

instance ToJSON TimeRange
instance FromJSON TimeRange

-- 逻辑操作符
data LogicalOperator = 
  And
  | Or
  | Not
  deriving (Show, Eq, Generic)

instance ToJSON LogicalOperator
instance FromJSON LogicalOperator

-- 动作
data Action = 
  SendCommand ActuatorCommand
  | SendNotification Text
  | LogEvent Text
  | CustomAction Text
  deriving (Show, Eq, Generic)

instance ToJSON Action
instance FromJSON Action

-- 物联网网络
data IoTSystem = IoTSystem
  { devices :: Map DeviceId Device
  , rules :: Map RuleId ProcessingRule
  , dataHistory :: [SensorData]
  , commandHistory :: [ActuatorCommand]
  } deriving (Show, Eq, Generic)

instance ToJSON IoTSystem
instance FromJSON IoTSystem
```

## 2. 设备管理

```haskell
module IoT.Core.DeviceManagement where

import IoT.Core.DataStructures
import Data.Time (getCurrentTime)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

-- 设备管理器状态
data DeviceManagerState = DeviceManagerState
  { devices :: Map DeviceId Device
  , deviceRegistry :: Map DeviceId DeviceInfo
  } deriving (Show, Eq)

-- 设备信息
data DeviceInfo = DeviceInfo
  { device :: Device
  , registrationTime :: UTCTime
  , lastHeartbeat :: UTCTime
  , heartbeatInterval :: Int  -- 秒
  } deriving (Show, Eq)

-- 设备管理器
type DeviceManager = State DeviceManagerState

-- 注册设备
registerDevice :: Device -> DeviceManager DeviceId
registerDevice device = do
  currentTime <- liftIO getCurrentTime
  let deviceInfo = DeviceInfo
        { device = device
        , registrationTime = currentTime
        , lastHeartbeat = currentTime
        , heartbeatInterval = 30
        }
  
  modify $ \state -> state
    { devices = Map.insert (deviceId device) device (devices state)
    , deviceRegistry = Map.insert (deviceId device) deviceInfo (deviceRegistry state)
    }
  
  return $ deviceId device

-- 更新设备状态
updateDeviceStatus :: DeviceId -> DeviceStatus -> DeviceManager ()
updateDeviceStatus deviceId status = do
  modify $ \state -> 
    let maybeDevice = Map.lookup deviceId (devices state)
        updatedDevice = maybeDevice >>= \device -> 
          Just $ device { status = status }
    in state { devices = Map.alter (const updatedDevice) deviceId (devices state) }

-- 处理设备心跳
processHeartbeat :: DeviceId -> DeviceManager ()
processHeartbeat deviceId = do
  currentTime <- liftIO getCurrentTime
  modify $ \state ->
    let maybeInfo = Map.lookup deviceId (deviceRegistry state)
        updatedInfo = maybeInfo >>= \info -> 
          Just $ info { lastHeartbeat = currentTime }
    in state { deviceRegistry = Map.alter (const updatedInfo) deviceId (deviceRegistry state) }

-- 创建设备
createSensor :: Text -> Location -> SensorType -> Device
createSensor name location sensorType = Device
  { deviceId = DeviceId name
  , deviceType = Sensor
  , name = name
  , location = location
  , status = Online
  , capabilities = [Capability
    { capabilityName = "sensing"
    , capabilityType = show sensorType
    , parameters = Map.empty
    }]
  , lastSeen = read "1970-01-01 00:00:00 UTC"
  }

createActuator :: Text -> Location -> [Capability] -> Device
createActuator name location capabilities = Device
  { deviceId = DeviceId name
  , deviceType = Actuator
  , name = name
  , location = location
  , status = Online
  , capabilities = capabilities
  , lastSeen = read "1970-01-01 00:00:00 UTC"
  }
```

## 3. 数据收集和处理

```haskell
module IoT.Core.DataProcessing where

import IoT.Core.DataStructures
import Data.Time (getCurrentTime)
import Data.List (sortBy)
import Data.Ord (comparing)
import Control.Monad.State

-- 数据处理器状态
data DataProcessorState = DataProcessorState
  { sensorData :: [SensorData]
  , processedData :: [ProcessedData]
  , statistics :: Map DeviceId DeviceStatistics
  } deriving (Show, Eq)

-- 处理后的数据
data ProcessedData = ProcessedData
  { originalData :: SensorData
  , processedValue :: Double
  , processingMethod :: Text
  , timestamp :: UTCTime
  } deriving (Show, Eq)

-- 设备统计信息
data DeviceStatistics = DeviceStatistics
  { deviceId :: DeviceId
  , dataCount :: Int
  , averageValue :: Double
  , minValue :: Double
  , maxValue :: Double
  , lastUpdate :: UTCTime
  } deriving (Show, Eq)

-- 数据处理器
type DataProcessor = State DataProcessorState

-- 添加传感器数据
addSensorData :: SensorData -> DataProcessor ()
addSensorData data = do
  modify $ \state -> state
    { sensorData = data : sensorData state }
  
  -- 更新统计信息
  updateDeviceStatistics data

-- 更新设备统计信息
updateDeviceStatistics :: SensorData -> DataProcessor ()
updateDeviceStatistics data = do
  state <- get
  let deviceId = sensorId data
      maybeStats = Map.lookup deviceId (statistics state)
      newStats = case maybeStats of
        Nothing -> DeviceStatistics
          { deviceId = deviceId
          , dataCount = 1
          , averageValue = value data
          , minValue = value data
          , maxValue = value data
          , lastUpdate = timestamp data
          }
        Just stats -> stats
          { dataCount = dataCount stats + 1
          , averageValue = (averageValue stats * fromIntegral (dataCount stats) + value data) / fromIntegral (dataCount stats + 1)
          , minValue = min (minValue stats) (value data)
          , maxValue = max (maxValue stats) (value data)
          , lastUpdate = timestamp data
          }
  
  modify $ \state -> state
    { statistics = Map.insert deviceId newStats (statistics state) }

-- 数据聚合
aggregateData :: DeviceId -> SensorType -> AggregationFunction -> DataProcessor Double
aggregateData deviceId sensorType aggFunc = do
  state <- get
  let relevantData = filter (\data -> 
        sensorId data == deviceId && sensorType data == sensorType) (sensorData state)
      values = map value relevantData
  
  case aggFunc of
    Average -> return $ if null values then 0 else sum values / fromIntegral (length values)
    Sum -> return $ sum values
    Min -> return $ if null values then 0 else minimum values
    Max -> return $ if null values then 0 else maximum values
    Count -> return $ fromIntegral $ length values

-- 聚合函数
data AggregationFunction = 
  Average
  | Sum
  | Min
  | Max
  | Count
  deriving (Show, Eq)

-- 异常检测
detectAnomalies :: DeviceId -> SensorType -> Double -> DataProcessor [SensorData]
detectAnomalies deviceId sensorType threshold = do
  state <- get
  let relevantData = filter (\data -> 
        sensorId data == deviceId && sensorType data == sensorType) (sensorData state)
      maybeStats = Map.lookup deviceId (statistics state)
  
  case maybeStats of
    Nothing -> return []
    Just stats -> 
      let mean = averageValue stats
          anomalies = filter (\data -> 
            abs (value data - mean) > threshold) relevantData
      in return anomalies
```

## 4. 规则引擎

```haskell
module IoT.Core.RuleEngine where

import IoT.Core.DataStructures
import Data.Time (getCurrentTime)
import Control.Monad.State
import Data.Maybe (fromMaybe)

-- 规则引擎状态
data RuleEngineState = RuleEngineState
  { rules :: Map RuleId ProcessingRule
  , ruleHistory :: [RuleExecution]
  , activeRules :: [RuleId]
  } deriving (Show, Eq)

-- 规则执行记录
data RuleExecution = RuleExecution
  { ruleId :: RuleId
  , timestamp :: UTCTime
  , condition :: Condition
  , action :: Action
  , success :: Bool
  , message :: Text
  } deriving (Show, Eq)

-- 规则引擎
type RuleEngine = State RuleEngineState

-- 添加规则
addRule :: ProcessingRule -> RuleEngine ()
addRule rule = do
  modify $ \state -> state
    { rules = Map.insert (ruleId rule) rule (rules state)
    , activeRules = if enabled rule then ruleId rule : activeRules state else activeRules state
    }

-- 评估条件
evaluateCondition :: Condition -> [SensorData] -> Bool
evaluateCondition (ThresholdCondition deviceId sensorType threshold comparison) data = 
  let relevantData = filter (\d -> sensorId d == deviceId && sensorType d == sensorType) data
  in case relevantData of
       [] -> False
       (latest:_) -> 
         let value = value latest
         in case comparison of
              GreaterThan -> value > threshold
              LessThan -> value < threshold
              Equal -> value == threshold
              NotEqual -> value /= threshold
              GreaterThanOrEqual -> value >= threshold
              LessThanOrEqual -> value <= threshold

evaluateCondition (TimeCondition timeRange) data = 
  let currentTime = getCurrentTime
  in currentTime >= startTime timeRange && currentTime <= endTime timeRange

evaluateCondition (LogicalCondition operator conditions) data = 
  let results = map (\c -> evaluateCondition c data) conditions
  in case operator of
       And -> all id results
       Or -> any id results
       Not -> case results of
                [result] -> not result
                _ -> False

evaluateCondition (CustomCondition _) data = True  -- 简化实现

-- 执行动作
executeAction :: Action -> IO Bool
executeAction (SendCommand command) = do
  putStrLn $ "执行命令: " ++ show command
  return True

executeAction (SendNotification message) = do
  putStrLn $ "发送通知: " ++ show message
  return True

executeAction (LogEvent message) = do
  putStrLn $ "记录事件: " ++ show message
  return True

executeAction (CustomAction action) = do
  putStrLn $ "自定义动作: " ++ show action
  return True

-- 处理传感器数据
processSensorData :: SensorData -> RuleEngine IO ()
processSensorData data = do
  state <- get
  let activeRules = map (\ruleId -> fromMaybe (error "Rule not found") $ Map.lookup ruleId (rules state)) (activeRules state)
  
  mapM_ (\rule -> do
    let condition = condition rule
        action = action rule
        conditionMet = evaluateCondition condition [data]
    
    if conditionMet then do
      currentTime <- liftIO getCurrentTime
      success <- liftIO $ executeAction action
      
      let execution = RuleExecution
            { ruleId = ruleId rule
            , timestamp = currentTime
            , condition = condition
            , action = action
            , success = success
            , message = "Rule executed successfully"
            }
      
      modify $ \state -> state
        { ruleHistory = execution : ruleHistory state }
    else
      return ()
  ) activeRules

-- 创建阈值规则
createThresholdRule :: RuleId -> Text -> DeviceId -> SensorType -> Double -> Comparison -> Action -> ProcessingRule
createThresholdRule ruleId name deviceId sensorType threshold comparison action = ProcessingRule
  { ruleId = ruleId
  , name = name
  , condition = ThresholdCondition deviceId sensorType threshold comparison
  , action = action
  , enabled = True
  , priority = Normal
  }
```

## 5. 边缘计算

```haskell
module IoT.Core.EdgeComputing where

import IoT.Core.DataStructures
import IoT.Core.RuleEngine
import Data.Time (getCurrentTime)
import Control.Concurrent (MVar, newMVar, readMVar, modifyMVar)

-- 边缘节点
data EdgeNode = EdgeNode
  { nodeId :: NodeId
  , location :: Location
  , connectedDevices :: [DeviceId]
  , processingRules :: [ProcessingRule]
  , dataBuffer :: MVar [SensorData]
  , commandQueue :: MVar [ActuatorCommand]
  } deriving (Show, Eq)

-- 节点ID
newtype NodeId = NodeId { unNodeId :: Text }
  deriving (Show, Eq, Ord)

-- 创建边缘节点
createEdgeNode :: NodeId -> Location -> IO EdgeNode
createEdgeNode nodeId location = do
  dataBuffer <- newMVar []
  commandQueue <- newMVar []
  
  return EdgeNode
    { nodeId = nodeId
    , location = location
    , connectedDevices = []
    , processingRules = []
    , dataBuffer = dataBuffer
    , commandQueue = commandQueue
    }

-- 添加设备到边缘节点
addDeviceToNode :: EdgeNode -> DeviceId -> EdgeNode
addDeviceToNode node deviceId = 
  node { connectedDevices = deviceId : connectedDevices node }

-- 添加规则到边缘节点
addRuleToNode :: EdgeNode -> ProcessingRule -> EdgeNode
addRuleToNode node rule = 
  node { processingRules = rule : processingRules node }

-- 处理传感器数据
processDataAtEdge :: EdgeNode -> SensorData -> IO ()
processDataAtEdge node data = do
  -- 添加到数据缓冲区
  modifyMVar (dataBuffer node) $ \buffer -> 
    return (data : buffer, ())
  
  -- 应用处理规则
  mapM_ (\rule -> do
    let condition = condition rule
        action = action rule
        conditionMet = evaluateCondition condition [data]
    
    if conditionMet then do
      success <- executeAction action
      putStrLn $ "边缘节点 " ++ show (nodeId node) ++ " 执行规则: " ++ show (ruleId rule)
    else
      return ()
  ) (processingRules node)

-- 边缘节点数据聚合
aggregateDataAtEdge :: EdgeNode -> DeviceId -> SensorType -> AggregationFunction -> IO Double
aggregateDataAtEdge node deviceId sensorType aggFunc = do
  buffer <- readMVar (dataBuffer node)
  let relevantData = filter (\data -> 
        sensorId data == deviceId && sensorType data == sensorType) buffer
      values = map value relevantData
  
  case aggFunc of
    Average -> return $ if null values then 0 else sum values / fromIntegral (length values)
    Sum -> return $ sum values
    Min -> return $ if null values then 0 else minimum values
    Max -> return $ if null values then 0 else maximum values
    Count -> return $ fromIntegral $ length values

-- 边缘节点监控
monitorEdgeNode :: EdgeNode -> IO ()
monitorEdgeNode node = do
  putStrLn $ "监控边缘节点: " ++ show (nodeId node)
  
  -- 检查连接设备状态
  putStrLn $ "连接设备数量: " ++ show (length (connectedDevices node))
  
  -- 检查数据缓冲区
  buffer <- readMVar (dataBuffer node)
  putStrLn $ "数据缓冲区大小: " ++ show (length buffer)
  
  -- 检查命令队列
  commandQueue <- readMVar (commandQueue node)
  putStrLn $ "命令队列大小: " ++ show (length commandQueue)
```

## 6. 示例应用

```haskell
module IoT.Examples where

import IoT.Core.DataStructures
import IoT.Core.DeviceManagement
import IoT.Core.DataProcessing
import IoT.Core.RuleEngine
import IoT.Core.EdgeComputing
import Data.Time (getCurrentTime)
import Control.Monad.State

-- 运行物联网示例
runIoTExample :: IO ()
runIoTExample = do
  putStrLn "=== 物联网应用示例 ==="
  
  -- 创建设备
  let location1 = Location { latitude = 40.7128, longitude = -74.0060, altitude = 10.0, description = "New York" }
  
  let temperatureSensor = createSensor "temp_sensor_1" location1 Temperature
  let lightActuator = createActuator "light_actuator_1" location1 
        [Capability { capabilityName = "light_control", capabilityType = "switch", parameters = Map.empty }]
  
  putStrLn "创建设备完成"
  
  -- 创建边缘节点
  edgeNode <- createEdgeNode (NodeId "edge_1") location1
  putStrLn "创建边缘节点完成"
  
  -- 添加设备到边缘节点
  let edgeNodeWithDevices = addDeviceToNode edgeNode (deviceId temperatureSensor)
  putStrLn "设备已添加到边缘节点"
  
  -- 创建处理规则
  let thresholdRule = createThresholdRule 
        (RuleId "temp_alert") 
        "温度过高警报" 
        (deviceId temperatureSensor) 
        Temperature 
        30.0 
        GreaterThan 
        (SendNotification "温度过高！")
  
  let edgeNodeWithRules = addRuleToNode edgeNodeWithDevices thresholdRule
  putStrLn "处理规则已添加到边缘节点"
  
  -- 模拟传感器数据
  currentTime <- getCurrentTime
  let sensorData1 = SensorData
        { sensorId = deviceId temperatureSensor
        , sensorType = Temperature
        , value = 25.0
        , unit = "°C"
        , timestamp = currentTime
        , quality = Good
        }
  
  let sensorData2 = SensorData
        { sensorId = deviceId temperatureSensor
        , sensorType = Temperature
        , value = 35.0
        , unit = "°C"
        , timestamp = currentTime
        , quality = Good
        }
  
  putStrLn "模拟传感器数据"
  
  -- 在边缘节点处理数据
  processDataAtEdge edgeNodeWithRules sensorData1
  processDataAtEdge edgeNodeWithRules sensorData2
  
  -- 数据聚合
  aggregatedValue <- aggregateDataAtEdge edgeNodeWithRules (deviceId temperatureSensor) Temperature Average
  putStrLn $ "温度平均值: " ++ show aggregatedValue
  
  -- 监控边缘节点
  monitorEdgeNode edgeNodeWithRules
  
  putStrLn "物联网应用示例完成"

main :: IO ()
main = runIoTExample
```

## 总结

这个物联网应用提供了：

1. **基础数据结构**：设备、传感器数据、执行器命令、处理规则等
2. **设备管理**：设备注册、状态监控、健康检查
3. **数据处理**：数据收集、聚合、异常检测
4. **规则引擎**：条件评估、动作执行、规则管理
5. **边缘计算**：边缘节点、本地处理、数据聚合
6. **示例应用**：完整的物联网系统演示

所有实现都遵循函数式编程范式，充分利用Haskell的类型系统确保类型安全。
