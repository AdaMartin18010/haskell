# 服务发现模式（Service Discovery Pattern）

## 概述
服务发现模式是一种分布式系统设计模式，允许服务自动注册和发现其他服务的位置，实现动态的服务定位和负载均衡。

## 理论基础
- **服务注册**：服务启动时向注册中心注册
- **服务发现**：客户端通过注册中心查找服务
- **健康检查**：定期检查服务健康状态

## Rust实现示例
```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use uuid::Uuid;

// 服务信息
#[derive(Debug, Clone)]
struct ServiceInfo {
    id: String,
    name: String,
    host: String,
    port: u16,
    health_check_url: String,
    metadata: HashMap<String, String>,
    last_heartbeat: Instant,
    status: ServiceStatus,
}

#[derive(Debug, Clone, PartialEq)]
enum ServiceStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

// 服务注册中心
struct ServiceRegistry {
    services: Arc<Mutex<HashMap<String, ServiceInfo>>>,
    health_check_interval: Duration,
    heartbeat_timeout: Duration,
}

impl ServiceRegistry {
    fn new() -> Self {
        Self {
            services: Arc::new(Mutex::new(HashMap::new())),
            health_check_interval: Duration::from_secs(30),
            heartbeat_timeout: Duration::from_secs(90),
        }
    }
    
    async fn register_service(&self, service: ServiceInfo) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        services.insert(service.id.clone(), service);
        println!("服务已注册: {}", service.name);
        Ok(())
    }
    
    async fn deregister_service(&self, service_id: &str) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        if services.remove(service_id).is_some() {
            println!("服务已注销: {}", service_id);
            Ok(())
        } else {
            Err("服务不存在".to_string())
        }
    }
    
    async fn discover_service(&self, service_name: &str) -> Vec<ServiceInfo> {
        let services = self.services.lock().unwrap();
        services
            .values()
            .filter(|service| {
                service.name == service_name && service.status == ServiceStatus::Healthy
            })
            .cloned()
            .collect()
    }
    
    async fn update_heartbeat(&self, service_id: &str) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        if let Some(service) = services.get_mut(service_id) {
            service.last_heartbeat = Instant::now();
            Ok(())
        } else {
            Err("服务不存在".to_string())
        }
    }
    
    async fn start_health_checker(&self) {
        let services = Arc::clone(&self.services);
        let health_check_interval = self.health_check_interval;
        let heartbeat_timeout = self.heartbeat_timeout;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(health_check_interval);
            
            loop {
                interval.tick().await;
                
                let mut services_guard = services.lock().unwrap();
                let now = Instant::now();
                
                // 检查心跳超时
                services_guard.retain(|_, service| {
                    if now.duration_since(service.last_heartbeat) > heartbeat_timeout {
                        println!("服务 {} 心跳超时，标记为不健康", service.name);
                        service.status = ServiceStatus::Unhealthy;
                    }
                    service.status != ServiceStatus::Unhealthy
                });
            }
        });
    }
}

// 服务客户端
struct ServiceClient {
    registry: Arc<ServiceRegistry>,
}

impl ServiceClient {
    fn new(registry: Arc<ServiceRegistry>) -> Self {
        Self { registry }
    }
    
    async fn call_service(&self, service_name: &str, request: &str) -> Result<String, String> {
        let services = self.registry.discover_service(service_name).await;
        
        if services.is_empty() {
            return Err("没有找到可用的服务".to_string());
        }
        
        // 简单的负载均衡：选择第一个可用服务
        let service = &services[0];
        let url = format!("http://{}:{}/api", service.host, service.port);
        
        // 模拟服务调用
        println!("调用服务 {}: {}", service.name, url);
        Ok(format!("来自 {} 的响应: {}", service.name, request))
    }
}

// 服务实例
struct ServiceInstance {
    id: String,
    name: String,
    host: String,
    port: u16,
    registry: Arc<ServiceRegistry>,
    heartbeat_interval: Duration,
}

impl ServiceInstance {
    fn new(name: String, host: String, port: u16, registry: Arc<ServiceRegistry>) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            name,
            host,
            port,
            registry,
            heartbeat_interval: Duration::from_secs(30),
        }
    }
    
    async fn start(&self) {
        // 注册服务
        let service_info = ServiceInfo {
            id: self.id.clone(),
            name: self.name.clone(),
            host: self.host.clone(),
            port: self.port,
            health_check_url: format!("http://{}:{}/health", self.host, self.port),
            metadata: HashMap::new(),
            last_heartbeat: Instant::now(),
            status: ServiceStatus::Healthy,
        };
        
        if let Err(e) = self.registry.register_service(service_info).await {
            eprintln!("服务注册失败: {}", e);
            return;
        }
        
        // 启动心跳
        self.start_heartbeat().await;
    }
    
    async fn start_heartbeat(&self) {
        let registry = Arc::clone(&self.registry);
        let service_id = self.id.clone();
        let heartbeat_interval = self.heartbeat_interval;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(heartbeat_interval);
            
            loop {
                interval.tick().await;
                
                if let Err(e) = registry.update_heartbeat(&service_id).await {
                    eprintln!("心跳更新失败: {}", e);
                    break;
                }
            }
        });
    }
    
    async fn stop(&self) {
        if let Err(e) = self.registry.deregister_service(&self.id).await {
            eprintln!("服务注销失败: {}", e);
        }
    }
}

// 负载均衡器
struct LoadBalancer {
    registry: Arc<ServiceRegistry>,
    strategy: LoadBalancingStrategy,
}

#[derive(Clone)]
enum LoadBalancingStrategy {
    RoundRobin,
    Random,
    LeastConnections,
}

impl LoadBalancer {
    fn new(registry: Arc<ServiceRegistry>, strategy: LoadBalancingStrategy) -> Self {
        Self { registry, strategy }
    }
    
    async fn get_service(&self, service_name: &str) -> Result<ServiceInfo, String> {
        let services = self.registry.discover_service(service_name).await;
        
        if services.is_empty() {
            return Err("没有可用的服务".to_string());
        }
        
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                // 简化的轮询实现
                Ok(services[0].clone())
            }
            LoadBalancingStrategy::Random => {
                use rand::Rng;
                let mut rng = rand::thread_rng();
                let index = rng.gen_range(0..services.len());
                Ok(services[index].clone())
            }
            LoadBalancingStrategy::LeastConnections => {
                // 简化的最少连接实现
                Ok(services[0].clone())
            }
        }
    }
}

// 配置中心
struct ConfigCenter {
    configs: Arc<Mutex<HashMap<String, String>>>,
}

impl ConfigCenter {
    fn new() -> Self {
        Self {
            configs: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    async fn set_config(&self, key: String, value: String) {
        let mut configs = self.configs.lock().unwrap();
        configs.insert(key, value);
    }
    
    async fn get_config(&self, key: &str) -> Option<String> {
        let configs = self.configs.lock().unwrap();
        configs.get(key).cloned()
    }
}

#[tokio::main]
async fn main() {
    // 创建服务注册中心
    let registry = Arc::new(ServiceRegistry::new());
    registry.start_health_checker().await;
    
    // 启动多个服务实例
    let service1 = ServiceInstance::new(
        "user-service".to_string(),
        "localhost".to_string(),
        8081,
        Arc::clone(&registry),
    );
    
    let service2 = ServiceInstance::new(
        "user-service".to_string(),
        "localhost".to_string(),
        8082,
        Arc::clone(&registry),
    );
    
    let service3 = ServiceInstance::new(
        "order-service".to_string(),
        "localhost".to_string(),
        8083,
        Arc::clone(&registry),
    );
    
    // 启动服务
    service1.start().await;
    service2.start().await;
    service3.start().await;
    
    // 等待服务注册
    tokio::time::sleep(Duration::from_secs(1)).await;
    
    // 创建客户端
    let client = ServiceClient::new(Arc::clone(&registry));
    
    // 调用服务
    for i in 0..5 {
        match client.call_service("user-service", &format!("请求 {}", i)).await {
            Ok(response) => println!("{}", response),
            Err(error) => println!("调用失败: {}", error),
        }
    }
    
    // 负载均衡测试
    let load_balancer = LoadBalancer::new(
        Arc::clone(&registry),
        LoadBalancingStrategy::RoundRobin,
    );
    
    for i in 0..3 {
        match load_balancer.get_service("user-service").await {
            Ok(service) => println!("负载均衡选择服务: {}:{}", service.host, service.port),
            Err(error) => println!("负载均衡失败: {}", error),
        }
    }
    
    // 配置中心测试
    let config_center = ConfigCenter::new();
    config_center.set_config("database.url".to_string(), "localhost:5432".to_string()).await;
    config_center.set_config("redis.host".to_string(), "localhost:6379".to_string()).await;
    
    if let Some(db_url) = config_center.get_config("database.url").await {
        println!("数据库配置: {}", db_url);
    }
    
    // 清理
    service1.stop().await;
    service2.stop().await;
    service3.stop().await;
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Data.IORef
import Data.Map as M
import Data.Time
import System.Random
import Text.Printf

-- 服务状态
data ServiceStatus = Healthy | Unhealthy | Unknown deriving (Eq, Show)

-- 服务信息
data ServiceInfo = ServiceInfo
    { serviceId :: String
    , serviceName :: String
    , serviceHost :: String
    , servicePort :: Int
    , healthCheckUrl :: String
    , metadata :: M.Map String String
    , lastHeartbeat :: UTCTime
    , status :: ServiceStatus
    } deriving (Show)

-- 服务注册中心
data ServiceRegistry = ServiceRegistry
    { services :: TVar (M.Map String ServiceInfo)
    , healthCheckInterval :: Int
    , heartbeatTimeout :: Int
    }

newServiceRegistry :: IO ServiceRegistry
newServiceRegistry = do
    services <- newTVarIO M.empty
    return $ ServiceRegistry services 30 90

registerService :: ServiceRegistry -> ServiceInfo -> IO Bool
registerService registry service = do
    atomically $ do
        currentServices <- readTVar (services registry)
        writeTVar (services registry) (M.insert (serviceId service) service currentServices)
    putStrLn $ "服务已注册: " ++ serviceName service
    return True

deregisterService :: ServiceRegistry -> String -> IO Bool
deregisterService registry serviceId = do
    atomically $ do
        currentServices <- readTVar (services registry)
        writeTVar (services registry) (M.delete serviceId currentServices)
    putStrLn $ "服务已注销: " ++ serviceId
    return True

discoverService :: ServiceRegistry -> String -> IO [ServiceInfo]
discoverService registry serviceName = do
    atomically $ do
        currentServices <- readTVar (services registry)
        let healthyServices = M.elems $ M.filter (\service -> 
            serviceName service == serviceName && status service == Healthy) currentServices
        return healthyServices

updateHeartbeat :: ServiceRegistry -> String -> IO Bool
updateHeartbeat registry serviceId = do
    now <- getCurrentTime
    atomically $ do
        currentServices <- readTVar (services registry)
        case M.lookup serviceId currentServices of
            Just service -> do
                let updatedService = service { lastHeartbeat = now }
                writeTVar (services registry) (M.insert serviceId updatedService currentServices)
                return True
            Nothing -> return False

startHealthChecker :: ServiceRegistry -> IO ()
startHealthChecker registry = do
    forkIO $ healthCheckerLoop registry
    return ()

healthCheckerLoop :: ServiceRegistry -> IO ()
healthCheckerLoop registry = do
    threadDelay (healthCheckInterval registry * 1000000)
    
    now <- getCurrentTime
    atomically $ do
        currentServices <- readTVar (services registry)
        let timeoutSeconds = fromIntegral (heartbeatTimeout registry)
        let healthyServices = M.filter (\service -> 
            diffUTCTime now (lastHeartbeat service) < timeoutSeconds) currentServices
        writeTVar (services registry) healthyServices
    
    healthCheckerLoop registry

-- 服务客户端
data ServiceClient = ServiceClient
    { registry :: ServiceRegistry
    }

newServiceClient :: ServiceRegistry -> ServiceClient
newServiceClient registry = ServiceClient registry

callService :: ServiceClient -> String -> String -> IO (Either String String)
callService client serviceName request = do
    services <- discoverService (registry client) serviceName
    
    if null services
        then return $ Left "没有找到可用的服务"
        else do
            let service = head services
            let url = printf "http://%s:%d/api" (serviceHost service) (servicePort service)
            putStrLn $ "调用服务 " ++ serviceName service ++ ": " ++ url
            return $ Right $ "来自 " ++ serviceName service ++ " 的响应: " ++ request

-- 负载均衡器
data LoadBalancer = LoadBalancer
    { lbRegistry :: ServiceRegistry
    , lbStrategy :: LoadBalancingStrategy
    }

data LoadBalancingStrategy = RoundRobin | Random | LeastConnections

newLoadBalancer :: ServiceRegistry -> LoadBalancingStrategy -> LoadBalancer
newLoadBalancer registry strategy = LoadBalancer registry strategy

getService :: LoadBalancer -> String -> IO (Either String ServiceInfo)
getService lb serviceName = do
    services <- discoverService (lbRegistry lb) serviceName
    
    if null services
        then return $ Left "没有可用的服务"
        else do
            selectedService <- case lbStrategy lb of
                RoundRobin -> return $ head services
                Random -> do
                    index <- randomRIO (0, length services - 1)
                    return $ services !! index
                LeastConnections -> return $ head services
            return $ Right selectedService

-- 服务实例
data ServiceInstance = ServiceInstance
    { instanceId :: String
    , instanceName :: String
    , instanceHost :: String
    , instancePort :: Int
    , instanceRegistry :: ServiceRegistry
    , heartbeatInterval :: Int
    }

newServiceInstance :: String -> String -> Int -> ServiceRegistry -> ServiceInstance
newServiceInstance name host port registry = ServiceInstance
    { instanceId = show (randomRIO (0, 1000000) :: IO Int)
    , instanceName = name
    , instanceHost = host
    , instancePort = port
    , instanceRegistry = registry
    , heartbeatInterval = 30
    }

startService :: ServiceInstance -> IO ()
startService instance = do
    now <- getCurrentTime
    let serviceInfo = ServiceInfo
            { serviceId = instanceId instance
            , serviceName = instanceName instance
            , serviceHost = instanceHost instance
            , servicePort = instancePort instance
            , healthCheckUrl = printf "http://%s:%d/health" (instanceHost instance) (instancePort instance)
            , metadata = M.empty
            , lastHeartbeat = now
            , status = Healthy
            }
    
    registerService (instanceRegistry instance) serviceInfo
    startHeartbeat instance

startHeartbeat :: ServiceInstance -> IO ()
startHeartbeat instance = do
    forkIO $ heartbeatLoop instance
    return ()

heartbeatLoop :: ServiceInstance -> IO ()
heartbeatLoop instance = do
    threadDelay (heartbeatInterval instance * 1000000)
    updateHeartbeat (instanceRegistry instance) (instanceId instance)
    heartbeatLoop instance

stopService :: ServiceInstance -> IO ()
stopService instance = do
    deregisterService (instanceRegistry instance) (instanceId instance)

-- 配置中心
data ConfigCenter = ConfigCenter
    { configs :: TVar (M.Map String String)
    }

newConfigCenter :: IO ConfigCenter
newConfigCenter = do
    configs <- newTVarIO M.empty
    return $ ConfigCenter configs

setConfig :: ConfigCenter -> String -> String -> IO ()
setConfig center key value = do
    atomically $ do
        currentConfigs <- readTVar (configs center)
        writeTVar (configs center) (M.insert key value currentConfigs)

getConfig :: ConfigCenter -> String -> IO (Maybe String)
getConfig center key = do
    atomically $ do
        currentConfigs <- readTVar (configs center)
        return $ M.lookup key currentConfigs

-- 测试函数
testServiceDiscovery :: IO ()
testServiceDiscovery = do
    putStrLn "=== 服务发现测试 ==="
    
    registry <- newServiceRegistry
    startHealthChecker registry
    
    -- 创建服务实例
    service1 <- newServiceInstance "user-service" "localhost" 8081 registry
    service2 <- newServiceInstance "user-service" "localhost" 8082 registry
    service3 <- newServiceInstance "order-service" "localhost" 8083 registry
    
    -- 启动服务
    startService service1
    startService service2
    startService service3
    
    -- 等待服务注册
    threadDelay 1000000
    
    -- 创建客户端
    let client = newServiceClient registry
    
    -- 调用服务
    mapM_ (\i -> do
        result <- callService client "user-service" ("请求 " ++ show i)
        case result of
            Right response -> putStrLn response
            Left error -> putStrLn $ "调用失败: " ++ error
        ) [1..5]
    
    -- 负载均衡测试
    let loadBalancer = newLoadBalancer registry RoundRobin
    
    mapM_ (\i -> do
        result <- getService loadBalancer "user-service"
        case result of
            Right service -> putStrLn $ "负载均衡选择服务: " ++ serviceHost service ++ ":" ++ show (servicePort service)
            Left error -> putStrLn $ "负载均衡失败: " ++ error
        ) [1..3]
    
    -- 配置中心测试
    configCenter <- newConfigCenter
    setConfig configCenter "database.url" "localhost:5432"
    setConfig configCenter "redis.host" "localhost:6379"
    
    dbUrl <- getConfig configCenter "database.url"
    case dbUrl of
        Just url -> putStrLn $ "数据库配置: " ++ url
        Nothing -> putStrLn "未找到数据库配置"
    
    -- 清理
    stopService service1
    stopService service2
    stopService service3

main :: IO ()
main = do
    testServiceDiscovery
```

## Lean实现思路
```lean
-- 服务状态
inductive ServiceStatus where
  | Healthy
  | Unhealthy
  | Unknown

-- 服务信息
structure ServiceInfo where
  serviceId : String
  serviceName : String
  serviceHost : String
  servicePort : Nat
  healthCheckUrl : String
  metadata : Map String String
  lastHeartbeat : Nat -- 简化时间表示
  status : ServiceStatus

-- 服务注册中心
structure ServiceRegistry where
  services : Map String ServiceInfo
  healthCheckInterval : Nat
  heartbeatTimeout : Nat

def newServiceRegistry : ServiceRegistry :=
  { services := Map.empty
  , healthCheckInterval := 30
  , heartbeatTimeout := 90
  }

def registerService (registry : ServiceRegistry) (service : ServiceInfo) : ServiceRegistry :=
  { registry with services := registry.services.insert service.serviceId service }

def deregisterService (registry : ServiceRegistry) (serviceId : String) : ServiceRegistry :=
  { registry with services := registry.services.erase serviceId }

def discoverService (registry : ServiceRegistry) (serviceName : String) : List ServiceInfo :=
  registry.services.values.filter fun service =>
    service.serviceName = serviceName && service.status = ServiceStatus.Healthy

def updateHeartbeat (registry : ServiceRegistry) (serviceId : String) (timestamp : Nat) : ServiceRegistry :=
  match registry.services.find? serviceId with
  | some service => 
      let updatedService := { service with lastHeartbeat := timestamp }
      { registry with services := registry.services.insert serviceId updatedService }
  | none => registry

-- 服务客户端
structure ServiceClient where
  registry : ServiceRegistry

def newServiceClient (registry : ServiceRegistry) : ServiceClient :=
  { registry := registry }

def callService (client : ServiceClient) (serviceName : String) (request : String) : Sum String String :=
  let services := discoverService client.registry serviceName
  if services.isEmpty
    then Sum.inl "没有找到可用的服务"
    else 
      let service := services.head!
      let url := "http://" ++ service.serviceHost ++ ":" ++ toString service.servicePort ++ "/api"
      Sum.inr ("来自 " ++ service.serviceName ++ " 的响应: " ++ request)

-- 负载均衡器
structure LoadBalancer where
  registry : ServiceRegistry
  strategy : LoadBalancingStrategy

inductive LoadBalancingStrategy where
  | RoundRobin
  | Random
  | LeastConnections

def newLoadBalancer (registry : ServiceRegistry) (strategy : LoadBalancingStrategy) : LoadBalancer :=
  { registry := registry
  , strategy := strategy
  }

def getService (lb : LoadBalancer) (serviceName : String) : Sum String ServiceInfo :=
  let services := discoverService (lbRegistry lb) serviceName
  if services.isEmpty
    then Sum.inl "没有可用的服务"
    else 
      let selectedService := services.head! -- 简化实现
      Sum.inr selectedService

-- 配置中心
structure ConfigCenter where
  configs : Map String String

def newConfigCenter : ConfigCenter :=
  { configs := Map.empty }

def setConfig (center : ConfigCenter) (key value : String) : ConfigCenter :=
  { center with configs := center.configs.insert key value }

def getConfig (center : ConfigCenter) (key : String) : Option String :=
  center.configs.find? key
```

## 应用场景
- 微服务架构
- 容器编排
- 云原生应用
- 分布式系统

## 最佳实践
- 实现服务健康检查
- 支持服务版本管理
- 实现负载均衡策略
- 监控服务状态 