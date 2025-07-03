# 物联网概述（IoT Overview）

## 概述

物联网（Internet of Things, IoT）是通过网络连接各种物理设备，实现数据采集、传输、处理和应用的技术体系。涵盖传感器网络、边缘计算、云平台、数据分析等多个技术领域。

## 理论基础

- **传感器网络**：节点部署、数据采集、网络拓扑
- **边缘计算**：本地处理、实时响应、资源优化
- **云平台**：数据存储、计算资源、服务管理
- **数据分析**：流处理、机器学习、预测分析

## 核心领域

### 1. 设备管理

- 设备注册与发现
- 固件更新
- 状态监控
- 配置管理

### 2. 数据采集与传输

- 传感器数据采集
- 协议转换
- 数据传输
- 数据压缩

### 3. 边缘计算

- 本地数据处理
- 实时分析
- 决策执行
- 资源管理

### 4. 云平台服务

- 数据存储
- 计算服务
- 应用部署
- 安全认证

## Haskell实现

### 设备管理系统

```haskell
import Data.Time
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Concurrent.STM

-- 设备类型
data DeviceType = Sensor | Actuator | Gateway | Controller deriving (Show, Eq)

-- 设备状态
data DeviceStatus = Online | Offline | Error | Maintenance deriving (Show, Eq)

-- 设备信息
data Device = Device {
  deviceId :: String,
  deviceType :: DeviceType,
  deviceName :: String,
  location :: String,
  status :: DeviceStatus,
  lastSeen :: UTCTime,
  properties :: Map String String
} deriving (Show)

-- 传感器数据
data SensorData = SensorData {
  deviceId :: String,
  timestamp :: UTCTime,
  sensorType :: String,
  value :: Double,
  unit :: String
} deriving (Show)

-- IoT系统
data IoTSystem = IoTSystem {
  devices :: TVar (Map String Device),
  sensorData :: TVar [SensorData],
  rules :: TVar [Rule]
} deriving (Show)

-- 规则引擎
data Rule = Rule {
  ruleId :: String,
  condition :: Condition,
  action :: Action,
  enabled :: Bool
} deriving (Show)

data Condition = Condition {
  deviceId :: String,
  sensorType :: String,
  operator :: Operator,
  threshold :: Double
} deriving (Show)

data Operator = GreaterThan | LessThan | Equals | NotEquals deriving (Show, Eq)

data Action = Action {
  targetDevice :: String,
  command :: String,
  parameters :: Map String String
} deriving (Show)

-- 创建设备
createDevice :: String -> DeviceType -> String -> String -> Device
createDevice id deviceType name location = Device {
  deviceId = id,
  deviceType = deviceType,
  deviceName = name,
  location = location,
  status = Online,
  lastSeen = undefined, -- 需要实际时间
  properties = Map.empty
}

-- 添加设备到系统
addDevice :: IoTSystem -> Device -> STM ()
addDevice system device = do
  devicesMap <- readTVar (devices system)
  writeTVar (devices system) (Map.insert (deviceId device) device devicesMap)

-- 更新设备状态
updateDeviceStatus :: IoTSystem -> String -> DeviceStatus -> STM ()
updateDeviceStatus system deviceId status = do
  devicesMap <- readTVar (devices system)
  case Map.lookup deviceId devicesMap of
    Just device -> do
      let updatedDevice = device { status = status, lastSeen = undefined }
      writeTVar (devices system) (Map.insert deviceId updatedDevice devicesMap)
    Nothing -> return ()

-- 添加传感器数据
addSensorData :: IoTSystem -> SensorData -> STM ()
addSensorData system data = do
  currentData <- readTVar (sensorData system)
  writeTVar (sensorData system) (data : currentData)

-- 规则评估
evaluateRules :: IoTSystem -> SensorData -> STM [Action]
evaluateRules system data = do
  rulesList <- readTVar (rules system)
  let applicableRules = filter (\rule -> 
        enabled rule && 
        deviceId (condition rule) == deviceId data &&
        sensorType (condition rule) == sensorType data) rulesList
  return [action rule | rule <- applicableRules, 
          evaluateCondition (condition rule) (value data)]

-- 条件评估
evaluateCondition :: Condition -> Double -> Bool
evaluateCondition condition value = 
  case operator condition of
    GreaterThan -> value > threshold condition
    LessThan -> value < threshold condition
    Equals -> value == threshold condition
    NotEquals -> value /= threshold condition

-- 使用示例
demoIoTSystem :: IO ()
demoIoTSystem = do
  system <- atomically $ do
    devices <- newTVar Map.empty
    sensorData <- newTVar []
    rules <- newTVar []
    return $ IoTSystem devices sensorData rules
  
  let tempSensor = createDevice "SENSOR001" Sensor "Temperature Sensor" "Room A"
  let heater = createDevice "ACTUATOR001" Actuator "Heater" "Room A"
  
  atomically $ do
    addDevice system tempSensor
    addDevice system heater
    
    -- 添加规则：温度低于20度时开启加热器
    let rule = Rule "RULE001" 
                   (Condition "SENSOR001" "temperature" LessThan 20.0)
                   (Action "ACTUATOR001" "turn_on" Map.empty)
                   True
    rulesList <- readTVar (rules system)
    writeTVar (rules system) (rule : rulesList)
  
  putStrLn "IoT system initialized"
```

### 数据流处理

```haskell
import Control.Concurrent
import Control.Monad
import Data.List

-- 数据流处理器
data StreamProcessor = StreamProcessor {
  inputQueue :: TVar [SensorData],
  outputQueue :: TVar [ProcessedData],
  filters :: [Filter],
  aggregators :: [Aggregator]
} deriving (Show)

-- 处理后的数据
data ProcessedData = ProcessedData {
  originalData :: SensorData,
  processedValue :: Double,
  confidence :: Double,
  timestamp :: UTCTime
} deriving (Show)

-- 数据过滤器
data Filter = Filter {
  filterId :: String,
  condition :: SensorData -> Bool,
  enabled :: Bool
} deriving (Show)

-- 数据聚合器
data Aggregator = Aggregator {
  aggregatorId :: String,
  windowSize :: Int,
  aggregationType :: AggregationType,
  targetSensor :: String
} deriving (Show)

data AggregationType = Average | Sum | Min | Max | Count deriving (Show)

-- 创建流处理器
createStreamProcessor :: StreamProcessor
createStreamProcessor = StreamProcessor {
  inputQueue = undefined, -- 需要TVar
  outputQueue = undefined, -- 需要TVar
  filters = [],
  aggregators = []
}

-- 添加过滤器
addFilter :: StreamProcessor -> Filter -> StreamProcessor
addFilter processor filter = 
  processor { filters = filter : filters processor }

-- 添加聚合器
addAggregator :: StreamProcessor -> Aggregator -> StreamProcessor
addAggregator processor aggregator = 
  processor { aggregators = aggregator : aggregators processor }

-- 处理数据流
processDataStream :: StreamProcessor -> SensorData -> STM [ProcessedData]
processDataStream processor data = do
  -- 应用过滤器
  let filteredData = filter (\d -> all (\f -> enabled f && condition f d) (filters processor)) [data]
  
  -- 应用聚合器
  processedData <- mapM (applyAggregators processor) filteredData
  
  return processedData

-- 应用聚合器
applyAggregators :: StreamProcessor -> SensorData -> STM ProcessedData
applyAggregators processor data = do
  -- 简化的聚合处理
  let processedValue = value data
  let confidence = 0.95 -- 假设的置信度
  return $ ProcessedData data processedValue confidence (timestamp data)

-- 数据流处理示例
demoStreamProcessing :: IO ()
demoStreamProcessing = do
  let processor = createStreamProcessor
  
  -- 添加温度过滤器
  let tempFilter = Filter "TEMP_FILTER" 
                        (\d -> sensorType d == "temperature" && value d >= -50 && value d <= 100)
                        True
  let processor' = addFilter processor tempFilter
  
  -- 添加平均值聚合器
  let avgAggregator = Aggregator "TEMP_AVG" 10 Average "temperature"
  let processor'' = addAggregator processor' avgAggregator
  
  putStrLn "Stream processor configured"
```

## Rust实现

### 边缘计算节点

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use serde::{Serialize, Deserialize};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, Serialize, Deserialize)]
struct EdgeNode {
    node_id: String,
    location: String,
    capabilities: Vec<String>,
    status: NodeStatus,
    resources: ResourceUsage,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum NodeStatus {
    Online,
    Offline,
    Maintenance,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ResourceUsage {
    cpu_usage: f64,
    memory_usage: f64,
    storage_usage: f64,
    network_usage: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SensorData {
    device_id: String,
    timestamp: u64,
    sensor_type: String,
    value: f64,
    unit: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProcessedData {
    original_data: SensorData,
    processed_value: f64,
    confidence: f64,
    processing_time: u64,
}

struct EdgeComputingNode {
    node: EdgeNode,
    data_queue: Arc<Mutex<Vec<SensorData>>>,
    processed_queue: Arc<Mutex<Vec<ProcessedData>>>,
    rules: Arc<Mutex<Vec<ProcessingRule>>>,
    tx: mpsc::Sender<ProcessedData>,
}

#[derive(Debug, Clone)]
struct ProcessingRule {
    rule_id: String,
    sensor_type: String,
    condition: Condition,
    action: ProcessingAction,
    enabled: bool,
}

#[derive(Debug, Clone)]
enum Condition {
    GreaterThan(f64),
    LessThan(f64),
    Equals(f64),
    InRange(f64, f64),
}

#[derive(Debug, Clone)]
enum ProcessingAction {
    Filter,
    Aggregate(AggregationType),
    Transform(TransformType),
    Alert(String),
}

#[derive(Debug, Clone)]
enum AggregationType {
    Average,
    Sum,
    Min,
    Max,
    Count,
}

#[derive(Debug, Clone)]
enum TransformType {
    Normalize,
    Scale(f64),
    Offset(f64),
    Log,
}

impl EdgeComputingNode {
    fn new(node_id: String, location: String, tx: mpsc::Sender<ProcessedData>) -> Self {
        let node = EdgeNode {
            node_id: node_id.clone(),
            location,
            capabilities: vec!["data_processing".to_string(), "local_storage".to_string()],
            status: NodeStatus::Online,
            resources: ResourceUsage {
                cpu_usage: 0.0,
                memory_usage: 0.0,
                storage_usage: 0.0,
                network_usage: 0.0,
            },
        };

        Self {
            node,
            data_queue: Arc::new(Mutex::new(Vec::new())),
            processed_queue: Arc::new(Mutex::new(Vec::new())),
            rules: Arc::new(Mutex::new(Vec::new())),
            tx,
        }
    }

    async fn add_sensor_data(&self, data: SensorData) {
        let mut queue = self.data_queue.lock().unwrap();
        queue.push(data);
    }

    async fn process_data(&self) {
        let mut queue = self.data_queue.lock().unwrap();
        let rules = self.rules.lock().unwrap();
        
        let data_to_process: Vec<SensorData> = queue.drain(..).collect();
        
        for data in data_to_process {
            let processed_data = self.apply_rules(&data, &rules);
            if let Some(processed) = processed_data {
                let _ = self.tx.send(processed).await;
            }
        }
    }

    fn apply_rules(&self, data: &SensorData, rules: &[ProcessingRule]) -> Option<ProcessedData> {
        for rule in rules {
            if !rule.enabled || rule.sensor_type != data.sensor_type {
                continue;
            }

            if self.evaluate_condition(&rule.condition, data.value) {
                return Some(self.execute_action(&rule.action, data));
            }
        }
        None
    }

    fn evaluate_condition(&self, condition: &Condition, value: f64) -> bool {
        match condition {
            Condition::GreaterThan(threshold) => value > *threshold,
            Condition::LessThan(threshold) => value < *threshold,
            Condition::Equals(target) => (value - target).abs() < f64::EPSILON,
            Condition::InRange(min, max) => value >= *min && value <= *max,
        }
    }

    fn execute_action(&self, action: &ProcessingAction, data: &SensorData) -> ProcessedData {
        let start_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64;

        let processed_value = match action {
            ProcessingAction::Filter => data.value,
            ProcessingAction::Aggregate(agg_type) => self.aggregate_data(agg_type, data),
            ProcessingAction::Transform(transform_type) => self.transform_data(transform_type, data.value),
            ProcessingAction::Alert(_) => data.value, // 警报不改变数值
        };

        let processing_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis() as u64 - start_time;

        ProcessedData {
            original_data: data.clone(),
            processed_value,
            confidence: 0.95, // 假设的置信度
            processing_time,
        }
    }

    fn aggregate_data(&self, agg_type: &AggregationType, data: &SensorData) -> f64 {
        // 简化的聚合实现
        match agg_type {
            AggregationType::Average => data.value,
            AggregationType::Sum => data.value,
            AggregationType::Min => data.value,
            AggregationType::Max => data.value,
            AggregationType::Count => 1.0,
        }
    }

    fn transform_data(&self, transform_type: &TransformType, value: f64) -> f64 {
        match transform_type {
            TransformType::Normalize => (value - 0.0) / 100.0, // 假设范围0-100
            TransformType::Scale(factor) => value * factor,
            TransformType::Offset(offset) => value + offset,
            TransformType::Log => value.ln(),
        }
    }

    async fn add_rule(&self, rule: ProcessingRule) {
        let mut rules = self.rules.lock().unwrap();
        rules.push(rule);
    }

    async fn update_status(&mut self, status: NodeStatus) {
        self.node.status = status;
    }

    async fn update_resources(&mut self, resources: ResourceUsage) {
        self.node.resources = resources;
    }
}

// 使用示例
#[tokio::main]
async fn demo_edge_computing() {
    let (tx, mut rx) = mpsc::channel(100);
    let mut edge_node = EdgeComputingNode::new(
        "EDGE001".to_string(),
        "Factory Floor A".to_string(),
        tx,
    );

    // 添加处理规则
    let rule = ProcessingRule {
        rule_id: "RULE001".to_string(),
        sensor_type: "temperature".to_string(),
        condition: Condition::GreaterThan(25.0),
        action: ProcessingAction::Alert("High temperature detected".to_string()),
        enabled: true,
    };

    edge_node.add_rule(rule).await;

    // 模拟数据输入
    let sensor_data = SensorData {
        device_id: "SENSOR001".to_string(),
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        sensor_type: "temperature".to_string(),
        value: 30.0,
        unit: "Celsius".to_string(),
    };

    edge_node.add_sensor_data(sensor_data).await;
    edge_node.process_data().await;

    // 接收处理结果
    while let Some(processed_data) = rx.recv().await {
        println!("Processed data: {:?}", processed_data);
    }
}
```

### 设备通信协议

```rust
use std::collections::HashMap;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
enum MessageType {
    Data,
    Command,
    Response,
    Heartbeat,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct IoTMessage {
    message_type: MessageType,
    device_id: String,
    timestamp: u64,
    payload: String,
    checksum: u32,
}

#[derive(Debug)]
struct ProtocolHandler {
    devices: HashMap<String, DeviceInfo>,
    message_handlers: HashMap<MessageType, Box<dyn MessageHandler>>,
}

#[derive(Debug)]
struct DeviceInfo {
    device_id: String,
    connection: TcpStream,
    last_heartbeat: u64,
    status: DeviceStatus,
}

#[derive(Debug)]
enum DeviceStatus {
    Connected,
    Disconnected,
    Error,
}

trait MessageHandler: Send + Sync {
    fn handle(&self, message: &IoTMessage) -> Result<IoTMessage, String>;
}

struct DataMessageHandler;
struct CommandMessageHandler;
struct HeartbeatMessageHandler;

impl MessageHandler for DataMessageHandler {
    fn handle(&self, message: &IoTMessage) -> Result<IoTMessage, String> {
        // 处理数据消息
        println!("Processing data message from device: {}", message.device_id);
        
        let response = IoTMessage {
            message_type: MessageType::Response,
            device_id: message.device_id.clone(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            payload: "Data received".to_string(),
            checksum: 0,
        };
        
        Ok(response)
    }
}

impl MessageHandler for CommandMessageHandler {
    fn handle(&self, message: &IoTMessage) -> Result<IoTMessage, String> {
        // 处理命令消息
        println!("Processing command message: {}", message.payload);
        
        let response = IoTMessage {
            message_type: MessageType::Response,
            device_id: message.device_id.clone(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            payload: "Command executed".to_string(),
            checksum: 0,
        };
        
        Ok(response)
    }
}

impl MessageHandler for HeartbeatMessageHandler {
    fn handle(&self, message: &IoTMessage) -> Result<IoTMessage, String> {
        // 处理心跳消息
        println!("Received heartbeat from device: {}", message.device_id);
        
        let response = IoTMessage {
            message_type: MessageType::Response,
            device_id: message.device_id.clone(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            payload: "Heartbeat acknowledged".to_string(),
            checksum: 0,
        };
        
        Ok(response)
    }
}

impl ProtocolHandler {
    fn new() -> Self {
        let mut handlers = HashMap::new();
        handlers.insert(MessageType::Data, Box::new(DataMessageHandler));
        handlers.insert(MessageType::Command, Box::new(CommandMessageHandler));
        handlers.insert(MessageType::Heartbeat, Box::new(HeartbeatMessageHandler));

        Self {
            devices: HashMap::new(),
            message_handlers: handlers,
        }
    }

    async fn handle_connection(&mut self, stream: TcpStream, device_id: String) {
        let mut buffer = [0; 1024];
        let mut stream = stream;

        loop {
            match stream.read(&mut buffer).await {
                Ok(n) if n == 0 => {
                    println!("Device {} disconnected", device_id);
                    break;
                }
                Ok(n) => {
                    let message_data = String::from_utf8_lossy(&buffer[..n]);
                    if let Ok(message) = serde_json::from_str::<IoTMessage>(&message_data) {
                        if let Err(e) = self.process_message(&message).await {
                            println!("Error processing message: {}", e);
                        }
                    }
                }
                Err(e) => {
                    println!("Error reading from device {}: {}", device_id, e);
                    break;
                }
            }
        }
    }

    async fn process_message(&self, message: &IoTMessage) -> Result<(), String> {
        if let Some(handler) = self.message_handlers.get(&message.message_type) {
            match handler.handle(message) {
                Ok(response) => {
                    println!("Message processed successfully");
                    // 发送响应
                }
                Err(e) => {
                    println!("Error handling message: {}", e);
                }
            }
        }
        Ok(())
    }
}
```

## Lean实现

### 形式化IoT模型

```lean
-- 设备类型
inductive DeviceType
| Sensor
| Actuator
| Gateway
| Controller
deriving Repr

-- 设备状态
inductive DeviceStatus
| Online
| Offline
| Error
| Maintenance
deriving Repr

-- 设备信息
structure Device where
  deviceId : String
  deviceType : DeviceType
  deviceName : String
  location : String
  status : DeviceStatus
  lastSeen : Nat
  deriving Repr

-- 传感器数据
structure SensorData where
  deviceId : String
  timestamp : Nat
  sensorType : String
  value : Float
  unit : String
  deriving Repr

-- IoT系统
structure IoTSystem where
  devices : List (String × Device)
  sensorData : List SensorData
  rules : List Rule
  deriving Repr

-- 规则定义
structure Rule where
  ruleId : String
  condition : Condition
  action : Action
  enabled : Bool
  deriving Repr

structure Condition where
  deviceId : String
  sensorType : String
  operator : Operator
  threshold : Float
  deriving Repr

inductive Operator
| GreaterThan
| LessThan
| Equals
| NotEquals
deriving Repr

structure Action where
  targetDevice : String
  command : String
  parameters : List (String × String)
  deriving Repr

-- 创建设备
def createDevice (id : String) (deviceType : DeviceType) (name : String) (location : String) : Device :=
  Device.mk id deviceType name location DeviceStatus.Online 0

-- 添加设备到系统
def addDevice (system : IoTSystem) (device : Device) : IoTSystem :=
  { system with devices := (device.deviceId, device) :: system.devices }

-- 更新设备状态
def updateDeviceStatus (system : IoTSystem) (deviceId : String) (status : DeviceStatus) : IoTSystem :=
  let updatedDevices := system.devices.map (λ (id, device) => 
    if id = deviceId then (id, { device with status := status }) else (id, device))
  { system with devices := updatedDevices }

-- 添加传感器数据
def addSensorData (system : IoTSystem) (data : SensorData) : IoTSystem :=
  { system with sensorData := data :: system.sensorData }

-- 规则评估
def evaluateRules (system : IoTSystem) (data : SensorData) : List Action :=
  let applicableRules := system.rules.filter (λ rule => 
    rule.enabled ∧ 
    rule.condition.deviceId = data.deviceId ∧
    rule.condition.sensorType = data.sensorType)
  
  applicableRules.map (λ rule => rule.action) |>.filter (λ action =>
    evaluateCondition rule.condition data.value)

-- 条件评估
def evaluateCondition (condition : Condition) (value : Float) : Bool :=
  match condition.operator with
  | Operator.GreaterThan => value > condition.threshold
  | Operator.LessThan => value < condition.threshold
  | Operator.Equals => value = condition.threshold
  | Operator.NotEquals => value ≠ condition.threshold

-- 数据流处理
structure StreamProcessor where
  inputQueue : List SensorData
  outputQueue : List ProcessedData
  filters : List Filter
  aggregators : List Aggregator
  deriving Repr

structure ProcessedData where
  originalData : SensorData
  processedValue : Float
  confidence : Float
  timestamp : Nat
  deriving Repr

structure Filter where
  filterId : String
  sensorType : String
  minValue : Float
  maxValue : Float
  enabled : Bool
  deriving Repr

structure Aggregator where
  aggregatorId : String
  windowSize : Nat
  aggregationType : AggregationType
  targetSensor : String
  deriving Repr

inductive AggregationType
| Average
| Sum
| Min
| Max
| Count
deriving Repr

-- 处理数据流
def processDataStream (processor : StreamProcessor) (data : SensorData) : StreamProcessor :=
  -- 应用过滤器
  let filteredData := if shouldFilter processor.filters data then [data] else []
  
  -- 应用聚合器
  let processedData := filteredData.map (λ d => applyAggregators processor.aggregators d)
  
  { processor with 
    inputQueue := data :: processor.inputQueue,
    outputQueue := processedData ++ processor.outputQueue }

-- 过滤器检查
def shouldFilter (filters : List Filter) (data : SensorData) : Bool :=
  filters.all (λ filter => 
    ¬filter.enabled ∨ 
    (filter.sensorType = data.sensorType ∧ 
     data.value ≥ filter.minValue ∧ 
     data.value ≤ filter.maxValue))

-- 应用聚合器
def applyAggregators (aggregators : List Aggregator) (data : SensorData) : ProcessedData :=
  let processedValue := data.value  -- 简化的聚合
  let confidence := 0.95  -- 假设的置信度
  ProcessedData.mk data processedValue confidence data.timestamp

-- 使用示例
def demoIoT : IO Unit := do
  let device := createDevice "SENSOR001" DeviceType.Sensor "Temperature Sensor" "Room A"
  let system := IoTSystem.mk [] [] []
  let system' := addDevice system device
  
  let sensorData := SensorData.mk "SENSOR001" 1000 "temperature" 25.5 "Celsius"
  let system'' := addSensorData system' sensorData
  
  IO.println s!"Device: {device}"
  IO.println s!"Sensor data: {sensorData}"
```

### 形式化验证

```lean
-- IoT系统不变量
def iotSystemInvariant (system : IoTSystem) : Prop :=
  system.devices.all (λ (id, device) => id = device.deviceId) ∧
  system.sensorData.all (λ data => 
    system.devices.any (λ (id, _) => id = data.deviceId))

-- 设备状态合理性
def deviceStatusReasonable (device : Device) : Prop :=
  device.deviceId.length > 0 ∧
  device.deviceName.length > 0 ∧
  device.location.length > 0

-- 传感器数据合理性
def sensorDataReasonable (data : SensorData) : Prop :=
  data.deviceId.length > 0 ∧
  data.sensorType.length > 0 ∧
  data.value ≥ -1000 ∧ data.value ≤ 1000  -- 合理范围

-- 规则系统性质
theorem rule_system_property (system : IoTSystem) (h : iotSystemInvariant system) :
  let enabledRules := system.rules.filter (λ rule => rule.enabled)
  enabledRules.all (λ rule => 
    rule.condition.deviceId.length > 0 ∧
    rule.condition.sensorType.length > 0) := by
  simp [iotSystemInvariant] at h
  -- 证明启用的规则都有有效的条件

-- 数据流处理性质
theorem stream_processing_property (processor : StreamProcessor) (data : SensorData) :
  let processed := processDataStream processor data
  processed.inputQueue.length = processor.inputQueue.length + 1 := by
  simp [processDataStream]
  -- 证明输入队列长度增加1

-- 使用示例
def demoFormalVerification : IO Unit := do
  let device := createDevice "SENSOR001" DeviceType.Sensor "Temperature Sensor" "Room A"
  let system := IoTSystem.mk [] [] []
  let system' := addDevice system device
  
  if deviceStatusReasonable device then
    IO.println "Device is reasonable"
    let sensorData := SensorData.mk "SENSOR001" 1000 "temperature" 25.5 "Celsius"
    if sensorDataReasonable sensorData then
      IO.println "Sensor data is reasonable"
      let system'' := addSensorData system' sensorData
      IO.println s!"System updated: {system''}"
    else
      IO.println "Sensor data is unreasonable"
  else
    IO.println "Device is unreasonable"
```

## 工程与形式化对比

| 维度 | Haskell | Rust | Lean |
|------|---------|------|------|
| 类型安全 | 强类型系统 | 所有权系统 | 依赖类型 |
| 性能 | 中等 | 高 | 中等 |
| 并发支持 | STM/Async | 多线程/异步 | 有限支持 |
| 形式化验证 | QuickCheck | 有限验证 | 完整证明 |
| IoT生态 | 有限 | 丰富 | 有限 |

## 最佳实践

### 1. 设备管理

- 设备注册与发现机制
- 固件更新策略
- 状态监控与告警
- 配置管理标准化

### 2. 数据安全

- 端到端加密
- 身份认证与授权
- 数据完整性验证
- 隐私保护措施

### 3. 系统可靠性

- 故障检测与恢复
- 负载均衡
- 数据备份策略
- 监控与日志

### 4. 性能优化

- 边缘计算优化
- 数据压缩传输
- 缓存策略
- 资源调度

## 应用场景

- **工业物联网**：设备监控、预测维护、质量控制
- **智能家居**：环境控制、安全监控、能源管理
- **智慧城市**：交通管理、环境监测、公共安全
- **农业物联网**：精准农业、环境监测、自动化管理
- **医疗物联网**：健康监测、设备管理、远程医疗

## 总结

物联网技术需要高可靠性、高安全性和高性能的系统。Haskell适合IoT数据流处理和规则引擎，Rust适合边缘计算节点和通信协议，Lean适合关键算法的形式化验证。实际应用中应根据具体需求选择合适的技术栈，并注重设备管理、数据安全和系统可靠性。
