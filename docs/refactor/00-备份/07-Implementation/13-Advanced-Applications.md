# 高级应用实现

## 概述

高级应用实现模块提供了实际的应用场景，包括机器学习、区块链、物联网等领域的Haskell实现。

## 机器学习应用

### 基础机器学习框架

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module AdvancedApplications.MachineLearning where

import Control.Monad
import Data.List
import Data.Maybe
import System.Random

-- 数据类型
data Feature = Feature
  { featureName :: String
  , featureValue :: Double
  } deriving (Show, Eq)

data DataPoint = DataPoint
  { features :: [Feature]
  , label :: Maybe Double
  } deriving (Show, Eq)

data Dataset = Dataset
  { dataPoints :: [DataPoint]
  , featureNames :: [String]
  } deriving (Show)

-- 线性回归模型
data LinearRegressionModel = LinearRegressionModel
  { weights :: [Double]
  , bias :: Double
  , learningRate :: Double
  } deriving (Show)

-- 创建线性回归模型
createLinearRegressionModel :: Int -> Double -> LinearRegressionModel
createLinearRegressionModel numFeatures lr = 
  LinearRegressionModel (replicate numFeatures 0.0) 0.0 lr

-- 训练线性回归模型
trainLinearRegression :: LinearRegressionModel -> Dataset -> Int -> LinearRegressionModel
trainLinearRegression model dataset epochs = 
  foldl (\m _ -> trainEpoch m dataset) model [1..epochs]

trainEpoch :: LinearRegressionModel -> Dataset -> LinearRegressionModel
trainEpoch model dataset = 
  foldl (\m point -> updateModel m point) model (dataPoints dataset)

updateModel :: LinearRegressionModel -> DataPoint -> LinearRegressionModel
updateModel model point = 
  case label point of
    Just trueLabel -> 
      let prediction = predict model point
          error = trueLabel - prediction
          gradients = map (\f -> -2 * error * featureValue f) (features point)
          newWeights = zipWith (\w g -> w - learningRate model * g) (weights model) gradients
          newBias = bias model - learningRate model * (-2 * error)
      in model { weights = newWeights, bias = newBias }
    Nothing -> model

-- 预测
predict :: LinearRegressionModel -> DataPoint -> Double
predict model point = 
  let featureValues = map featureValue (features point)
      weightedSum = sum (zipWith (*) (weights model) featureValues)
  in weightedSum + bias model

-- 决策树模型
data DecisionTree = 
  Leaf Double
  | Node String Double DecisionTree DecisionTree
  deriving (Show)

-- 创建决策树
createDecisionTree :: Dataset -> DecisionTree
createDecisionTree dataset = 
  if allSameLabel dataset
    then Leaf (getMajorityLabel dataset)
    else 
      let (bestFeature, bestThreshold) = findBestSplit dataset
          (leftData, rightData) = splitData dataset bestFeature bestThreshold
      in Node bestFeature bestThreshold 
             (createDecisionTree leftData) 
             (createDecisionTree rightData)

-- 辅助函数
allSameLabel :: Dataset -> Bool
allSameLabel dataset = 
  let labels = mapMaybe label (dataPoints dataset)
  in length (nub labels) <= 1

getMajorityLabel :: Dataset -> Double
getMajorityLabel dataset = 
  let labels = mapMaybe label (dataPoints dataset)
  in head (labels ++ [0.0])

findBestSplit :: Dataset -> (String, Double)
findBestSplit dataset = 
  let features = featureNames dataset
      splits = concatMap (\f -> map (\t -> (f, t)) [0.5, 1.0, 1.5]) features
      bestSplit = minimumBy (\a b -> compare (splitQuality dataset a) (splitQuality dataset b)) splits
  in bestSplit

splitQuality :: Dataset -> (String, Double) -> Double
splitQuality dataset (feature, threshold) = 
  let (left, right) = splitData dataset feature threshold
      leftImpurity = calculateImpurity left
      rightImpurity = calculateImpurity right
      leftSize = length (dataPoints left)
      rightSize = length (dataPoints right)
      totalSize = leftSize + rightSize
  in (fromIntegral leftSize / fromIntegral totalSize) * leftImpurity +
     (fromIntegral rightSize / fromIntegral totalSize) * rightImpurity

calculateImpurity :: Dataset -> Double
calculateImpurity dataset = 
  let labels = mapMaybe label (dataPoints dataset)
      labelCounts = map (\l -> length (filter (== l) labels)) (nub labels)
      total = length labels
      probabilities = map (\c -> fromIntegral c / fromIntegral total) labelCounts
  in -sum (map (\p -> p * log p) (filter (> 0) probabilities))

splitData :: Dataset -> String -> Double -> (Dataset, Dataset)
splitData dataset feature threshold = 
  let (left, right) = partition (\point -> 
        let featureValue = getFeatureValue point feature
        in featureValue <= threshold) (dataPoints dataset)
  in (Dataset left (featureNames dataset), Dataset right (featureNames dataset))

getFeatureValue :: DataPoint -> String -> Double
getFeatureValue point featureName = 
  case find ((== featureName) . featureName) (features point) of
    Just feature -> featureValue feature
    Nothing -> 0.0

-- 预测决策树
predictTree :: DecisionTree -> DataPoint -> Double
predictTree (Leaf label) _ = label
predictTree (Node feature threshold leftTree rightTree) point = 
  let value = getFeatureValue point feature
  in if value <= threshold
       then predictTree leftTree point
       else predictTree rightTree point
```

## 区块链应用

### 基础区块链实现

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module AdvancedApplications.Blockchain where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Time
import System.IO
import Crypto.Hash.SHA256

-- 交易
data Transaction = Transaction
  { txId :: String
  , fromAddress :: String
  , toAddress :: String
  , amount :: Double
  , timestamp :: UTCTime
  } deriving (Show, Eq)

-- 区块
data Block = Block
  { blockIndex :: Int
  , blockTimestamp :: UTCTime
  , blockTransactions :: [Transaction]
  , blockPreviousHash :: String
  , blockHash :: String
  , blockNonce :: Int
  } deriving (Show, Eq)

-- 区块链
data Blockchain = Blockchain
  { blocks :: [Block]
  , pendingTransactions :: [Transaction]
  , difficulty :: Int
  } deriving (Show)

-- 创建创世区块
createGenesisBlock :: Block
createGenesisBlock = Block
  { blockIndex = 0
  , blockTimestamp = read "2024-01-01 00:00:00 UTC"
  , blockTransactions = []
  , blockPreviousHash = "0000000000000000000000000000000000000000000000000000000000000000"
  , blockHash = "0000000000000000000000000000000000000000000000000000000000000000"
  , blockNonce = 0
  }

-- 创建区块链
createBlockchain :: Int -> Blockchain
createBlockchain diff = Blockchain
  { blocks = [createGenesisBlock]
  , pendingTransactions = []
  , difficulty = diff
  }

-- 计算区块哈希
calculateBlockHash :: Block -> String
calculateBlockHash block = 
  let dataString = show (blockIndex block) ++ 
                   show (blockTimestamp block) ++ 
                   show (blockTransactions block) ++ 
                   blockPreviousHash block ++ 
                   show (blockNonce block)
  in show (hash dataString)

-- 挖矿
mineBlock :: Blockchain -> String -> Block
mineBlock blockchain minerAddress = 
  let lastBlock = last (blocks blockchain)
      newBlock = Block
        { blockIndex = blockIndex lastBlock + 1
        , blockTimestamp = read "2024-01-01 00:00:00 UTC"
        , blockTransactions = pendingTransactions blockchain
        , blockPreviousHash = blockHash lastBlock
        , blockHash = ""
        , blockNonce = 0
        }
      minedBlock = findValidHash newBlock (difficulty blockchain)
  in minedBlock

findValidHash :: Block -> Int -> Block
findValidHash block targetDifficulty = 
  let target = replicate targetDifficulty '0'
      isValid hash = take targetDifficulty hash == target
      tryNonce nonce = 
        let blockWithNonce = block { blockNonce = nonce }
            hash = calculateBlockHash blockWithNonce
        in if isValid hash
             then blockWithNonce { blockHash = hash }
             else tryNonce (nonce + 1)
  in tryNonce 0

-- 添加区块到区块链
addBlock :: Blockchain -> Block -> Blockchain
addBlock blockchain block = 
  blockchain { blocks = blocks blockchain ++ [block], pendingTransactions = [] }

-- 添加交易
addTransaction :: Blockchain -> Transaction -> Blockchain
addTransaction blockchain transaction = 
  blockchain { pendingTransactions = pendingTransactions blockchain ++ [transaction] }

-- 验证区块链
validateBlockchain :: Blockchain -> Bool
validateBlockchain blockchain = 
  let blockPairs = zip (blocks blockchain) (tail (blocks blockchain))
  in all validateBlockPair blockPairs

validateBlockPair :: (Block, Block) -> Bool
validateBlockPair (prev, current) = 
  blockPreviousHash current == blockHash prev &&
  calculateBlockHash current == blockHash current

-- 钱包
data Wallet = Wallet
  { walletAddress :: String
  , walletBalance :: Double
  , walletTransactions :: [Transaction]
  } deriving (Show)

-- 创建钱包
createWallet :: String -> Wallet
createWallet address = Wallet
  { walletAddress = address
  , walletBalance = 0.0
  , walletTransactions = []
  }

-- 发送交易
sendTransaction :: Wallet -> String -> Double -> Blockchain -> (Transaction, Blockchain)
sendTransaction wallet toAddress amount blockchain = 
  let transaction = Transaction
        { txId = generateTxId
        , fromAddress = walletAddress wallet
        , toAddress = toAddress
        , amount = amount
        , timestamp = read "2024-01-01 00:00:00 UTC"
        }
      newBlockchain = addTransaction blockchain transaction
  in (transaction, newBlockchain)

generateTxId :: String
generateTxId = "tx_" ++ show (length "transaction")
```

## 物联网应用

### 物联网设备管理

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module AdvancedApplications.IoT where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Time
import System.IO

-- 传感器类型
data SensorType = 
  TemperatureSensor
  | HumiditySensor
  | PressureSensor
  | LightSensor
  | MotionSensor
  deriving (Show, Eq)

-- 传感器数据
data SensorData = SensorData
  { sensorId :: String
  , sensorType :: SensorType
  , sensorValue :: Double
  , sensorTimestamp :: UTCTime
  , sensorLocation :: String
  } deriving (Show, Eq)

-- 物联网设备
data IoTDevice = IoTDevice
  { deviceId :: String
  , deviceType :: String
  , deviceLocation :: String
  , deviceSensors :: [SensorType]
  , deviceStatus :: DeviceStatus
  , deviceData :: [SensorData]
  } deriving (Show)

data DeviceStatus = 
  Online
  | Offline
  | Error
  | Maintenance
  deriving (Show, Eq)

-- 创建物联网设备
createIoTDevice :: String -> String -> String -> [SensorType] -> IoTDevice
createIoTDevice id deviceType location sensors = IoTDevice
  { deviceId = id
  , deviceType = deviceType
  , deviceLocation = location
  , deviceSensors = sensors
  , deviceStatus = Online
  , deviceData = []
  }

-- 物联网网关
data IoTGateway = IoTGateway
  { gatewayId :: String
  , gatewayLocation :: String
  , connectedDevices :: [IoTDevice]
  , gatewayStatus :: GatewayStatus
  } deriving (Show)

data GatewayStatus = 
  GatewayOnline
  | GatewayOffline
  | GatewayError
  deriving (Show, Eq)

-- 创建物联网网关
createIoTGateway :: String -> String -> IoTGateway
createIoTGateway id location = IoTGateway
  { gatewayId = id
  , gatewayLocation = location
  , connectedDevices = []
  , gatewayStatus = GatewayOnline
  }

-- 添加设备到网关
addDeviceToGateway :: IoTGateway -> IoTDevice -> IoTGateway
addDeviceToGateway gateway device = 
  gateway { connectedDevices = connectedDevices gateway ++ [device] }

-- 收集传感器数据
collectSensorData :: IoTDevice -> SensorType -> Double -> IO SensorData
collectSensorData device sensorType value = do
  currentTime <- getCurrentTime
  let sensorData = SensorData
        { sensorId = deviceId device ++ "_" ++ show sensorType
        , sensorType = sensorType
        , sensorValue = value
        , sensorTimestamp = currentTime
        , sensorLocation = deviceLocation device
        }
  return sensorData

-- 数据处理
data DataProcessor = DataProcessor
  { processorId :: String
  , processingRules :: [ProcessingRule]
  , processedData :: [SensorData]
  } deriving (Show)

data ProcessingRule = ProcessingRule
  { ruleId :: String
  , ruleCondition :: SensorData -> Bool
  , ruleAction :: SensorData -> IO ()
  } deriving (Show)

-- 创建数据处理器
createDataProcessor :: String -> [ProcessingRule] -> DataProcessor
createDataProcessor id rules = DataProcessor
  { processorId = id
  , processingRules = rules
  , processedData = []
  }

-- 处理传感器数据
processSensorData :: DataProcessor -> SensorData -> IO DataProcessor
processSensorData processor data = do
  let applicableRules = filter (\rule -> ruleCondition rule data) (processingRules processor)
  mapM_ (\rule -> ruleAction rule data) applicableRules
  return processor { processedData = processedData processor ++ [data] }

-- 物联网应用示例
iotApplication :: IO ()
iotApplication = do
  -- 创建设备
  let tempSensor = createIoTDevice "temp001" "TemperatureSensor" "Room1" [TemperatureSensor]
      humiditySensor = createIoTDevice "hum001" "HumiditySensor" "Room1" [HumiditySensor]
  
  -- 创建网关
  let gateway = createIoTGateway "gateway001" "Building1"
      gatewayWithDevices = addDeviceToGateway (addDeviceToGateway gateway tempSensor) humiditySensor
  
  -- 收集数据
  tempData <- collectSensorData tempSensor TemperatureSensor 25.5
  humidityData <- collectSensorData humiditySensor HumiditySensor 60.0
  
  -- 创建处理规则
  let highTempRule = ProcessingRule
        { ruleId = "high_temp"
        , ruleCondition = \data -> sensorType data == TemperatureSensor && sensorValue data > 30.0
        , ruleAction = \data -> putStrLn $ "High temperature alert: " ++ show (sensorValue data)
        }
  
  let lowHumidityRule = ProcessingRule
        { ruleId = "low_humidity"
        , ruleCondition = \data -> sensorType data == HumiditySensor && sensorValue data < 40.0
        , ruleAction = \data -> putStrLn $ "Low humidity alert: " ++ show (sensorValue data)
        }
  
  -- 创建数据处理器
  let processor = createDataProcessor "processor001" [highTempRule, lowHumidityRule]
  
  -- 处理数据
  _ <- processSensorData processor tempData
  _ <- processSensorData processor humidityData
  
  putStrLn "IoT application completed"
```

## 总结

高级应用实现模块提供了：

1. **机器学习应用**：包括线性回归和决策树的实现
2. **区块链应用**：包括基础区块链、挖矿和钱包功能
3. **物联网应用**：包括设备管理、数据收集和处理

这些应用展示了Haskell在实际场景中的强大能力，为复杂系统的开发提供了可靠的基础。
