# 分布式缓存模式（Distributed Cache Pattern）

## 概述
分布式缓存模式是一种分布式系统设计模式，通过在多节点间共享缓存数据，提高系统性能和可扩展性，减少对后端存储的访问压力。

## 理论基础
- **一致性哈希**：实现数据分片和负载均衡
- **缓存更新策略**：Write-Through、Write-Behind、Refresh-Ahead
- **失效策略**：TTL、LRU、LFU

## Rust实现示例
```rust
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use uuid::Uuid;

// 缓存条目
#[derive(Debug, Clone)]
struct CacheEntry<T> {
    key: String,
    value: T,
    created_at: Instant,
    last_accessed: Instant,
    access_count: u32,
    ttl: Option<Duration>,
}

impl<T> CacheEntry<T> {
    fn new(key: String, value: T, ttl: Option<Duration>) -> Self {
        let now = Instant::now();
        Self {
            key,
            value,
            created_at: now,
            last_accessed: now,
            access_count: 0,
            ttl,
        }
    }
    
    fn is_expired(&self) -> bool {
        if let Some(ttl) = self.ttl {
            Instant::now().duration_since(self.created_at) > ttl
        } else {
            false
        }
    }
    
    fn touch(&mut self) {
        self.last_accessed = Instant::now();
        self.access_count += 1;
    }
}

// 缓存策略
#[derive(Debug, Clone)]
enum EvictionPolicy {
    LRU,  // 最近最少使用
    LFU,  // 最少使用频率
    FIFO, // 先进先出
    TTL,  // 基于时间
}

// 分布式缓存节点
struct CacheNode {
    id: String,
    cache: Arc<Mutex<HashMap<String, CacheEntry<String>>>>,
    max_size: usize,
    eviction_policy: EvictionPolicy,
    access_order: Arc<Mutex<VecDeque<String>>>,
}

impl CacheNode {
    fn new(id: String, max_size: usize, eviction_policy: EvictionPolicy) -> Self {
        Self {
            id,
            cache: Arc::new(Mutex::new(HashMap::new())),
            max_size,
            eviction_policy,
            access_order: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    async fn get(&self, key: &str) -> Option<String> {
        let mut cache = self.cache.lock().unwrap();
        
        if let Some(entry) = cache.get_mut(key) {
            if entry.is_expired() {
                cache.remove(key);
                return None;
            }
            
            entry.touch();
            
            // 更新访问顺序
            let mut access_order = self.access_order.lock().unwrap();
            if let Some(pos) = access_order.iter().position(|k| k == key) {
                access_order.remove(pos);
            }
            access_order.push_back(key.to_string());
            
            Some(entry.value.clone())
        } else {
            None
        }
    }
    
    async fn set(&self, key: String, value: String, ttl: Option<Duration>) -> Result<(), String> {
        let mut cache = self.cache.lock().unwrap();
        
        // 检查容量限制
        if cache.len() >= self.max_size && !cache.contains_key(&key) {
            self.evict_entry(&mut cache).await;
        }
        
        let entry = CacheEntry::new(key.clone(), value, ttl);
        cache.insert(key.clone(), entry);
        
        // 更新访问顺序
        let mut access_order = self.access_order.lock().unwrap();
        if let Some(pos) = access_order.iter().position(|k| k == &key) {
            access_order.remove(pos);
        }
        access_order.push_back(key);
        
        Ok(())
    }
    
    async fn delete(&self, key: &str) -> bool {
        let mut cache = self.cache.lock().unwrap();
        let removed = cache.remove(key).is_some();
        
        if removed {
            let mut access_order = self.access_order.lock().unwrap();
            if let Some(pos) = access_order.iter().position(|k| k == key) {
                access_order.remove(pos);
            }
        }
        
        removed
    }
    
    async fn evict_entry(&self, cache: &mut HashMap<String, CacheEntry<String>>) {
        match self.eviction_policy {
            EvictionPolicy::LRU => {
                let mut access_order = self.access_order.lock().unwrap();
                if let Some(key) = access_order.pop_front() {
                    cache.remove(&key);
                }
            }
            EvictionPolicy::LFU => {
                // 找到访问次数最少的条目
                if let Some((key, _)) = cache.iter()
                    .min_by_key(|(_, entry)| entry.access_count) {
                    let key = key.clone();
                    cache.remove(&key);
                    
                    let mut access_order = self.access_order.lock().unwrap();
                    if let Some(pos) = access_order.iter().position(|k| k == &key) {
                        access_order.remove(pos);
                    }
                }
            }
            EvictionPolicy::FIFO => {
                // 找到最早创建的条目
                if let Some((key, _)) = cache.iter()
                    .min_by_key(|(_, entry)| entry.created_at) {
                    let key = key.clone();
                    cache.remove(&key);
                    
                    let mut access_order = self.access_order.lock().unwrap();
                    if let Some(pos) = access_order.iter().position(|k| k == &key) {
                        access_order.remove(pos);
                    }
                }
            }
            EvictionPolicy::TTL => {
                // 找到最早过期的条目
                if let Some((key, _)) = cache.iter()
                    .filter(|(_, entry)| entry.ttl.is_some())
                    .min_by_key(|(_, entry)| entry.created_at) {
                    let key = key.clone();
                    cache.remove(&key);
                    
                    let mut access_order = self.access_order.lock().unwrap();
                    if let Some(pos) = access_order.iter().position(|k| k == &key) {
                        access_order.remove(pos);
                    }
                }
            }
        }
    }
    
    async fn clear_expired(&self) {
        let mut cache = self.cache.lock().unwrap();
        let expired_keys: Vec<String> = cache.iter()
            .filter(|(_, entry)| entry.is_expired())
            .map(|(key, _)| key.clone())
            .collect();
        
        for key in expired_keys {
            cache.remove(&key);
            
            let mut access_order = self.access_order.lock().unwrap();
            if let Some(pos) = access_order.iter().position(|k| k == &key) {
                access_order.remove(pos);
            }
        }
    }
    
    fn get_stats(&self) -> CacheStats {
        let cache = self.cache.lock().unwrap();
        let access_order = self.access_order.lock().unwrap();
        
        CacheStats {
            node_id: self.id.clone(),
            size: cache.len(),
            max_size: self.max_size,
            eviction_policy: self.eviction_policy.clone(),
            access_order_size: access_order.len(),
        }
    }
}

#[derive(Debug, Clone)]
struct CacheStats {
    node_id: String,
    size: usize,
    max_size: usize,
    eviction_policy: EvictionPolicy,
    access_order_size: usize,
}

// 一致性哈希环
struct ConsistentHashRing {
    nodes: Vec<HashNode>,
    virtual_nodes: usize,
}

#[derive(Debug, Clone)]
struct HashNode {
    id: String,
    hash: u64,
    virtual_id: Option<u32>,
}

impl ConsistentHashRing {
    fn new(virtual_nodes: usize) -> Self {
        Self {
            nodes: Vec::new(),
            virtual_nodes,
        }
    }
    
    fn add_node(&mut self, node_id: String) {
        let base_hash = self.hash(&node_id);
        
        for i in 0..self.virtual_nodes {
            let virtual_id = format!("{}-{}", node_id, i);
            let hash = self.hash(&virtual_id);
            
            self.nodes.push(HashNode {
                id: node_id.clone(),
                hash,
                virtual_id: Some(i),
            });
        }
        
        self.nodes.sort_by_key(|node| node.hash);
    }
    
    fn remove_node(&mut self, node_id: &str) {
        self.nodes.retain(|node| !node.id.starts_with(node_id));
    }
    
    fn get_node(&self, key: &str) -> Option<&HashNode> {
        if self.nodes.is_empty() {
            return None;
        }
        
        let key_hash = self.hash(key);
        
        // 找到第一个哈希值大于等于key哈希的节点
        for node in &self.nodes {
            if node.hash >= key_hash {
                return Some(node);
            }
        }
        
        // 如果没找到，返回第一个节点（环的起点）
        self.nodes.first()
    }
    
    fn hash(&self, key: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

// 分布式缓存集群
struct DistributedCache {
    nodes: Arc<Mutex<HashMap<String, Arc<CacheNode>>>>,
    hash_ring: Arc<Mutex<ConsistentHashRing>>,
    replication_factor: usize,
}

impl DistributedCache {
    fn new(replication_factor: usize) -> Self {
        Self {
            nodes: Arc::new(Mutex::new(HashMap::new())),
            hash_ring: Arc::new(Mutex::new(ConsistentHashRing::new(150))),
            replication_factor,
        }
    }
    
    async fn add_node(&self, node_id: String, max_size: usize, eviction_policy: EvictionPolicy) {
        let node = Arc::new(CacheNode::new(node_id.clone(), max_size, eviction_policy));
        
        {
            let mut nodes = self.nodes.lock().unwrap();
            nodes.insert(node_id.clone(), Arc::clone(&node));
        }
        
        {
            let mut hash_ring = self.hash_ring.lock().unwrap();
            hash_ring.add_node(node_id);
        }
        
        println!("节点 {} 已添加到缓存集群", node_id);
    }
    
    async fn remove_node(&self, node_id: &str) {
        {
            let mut nodes = self.nodes.lock().unwrap();
            nodes.remove(node_id);
        }
        
        {
            let mut hash_ring = self.hash_ring.lock().unwrap();
            hash_ring.remove_node(node_id);
        }
        
        println!("节点 {} 已从缓存集群移除", node_id);
    }
    
    async fn get(&self, key: &str) -> Option<String> {
        let hash_ring = self.hash_ring.lock().unwrap();
        let nodes = self.nodes.lock().unwrap();
        
        if let Some(hash_node) = hash_ring.get_node(key) {
            if let Some(cache_node) = nodes.get(&hash_node.id) {
                return cache_node.get(key).await;
            }
        }
        
        None
    }
    
    async fn set(&self, key: String, value: String, ttl: Option<Duration>) -> Result<(), String> {
        let hash_ring = self.hash_ring.lock().unwrap();
        let nodes = self.nodes.lock().unwrap();
        
        // 找到主节点
        if let Some(hash_node) = hash_ring.get_node(&key) {
            if let Some(cache_node) = nodes.get(&hash_node.id) {
                let result = cache_node.set(key.clone(), value.clone(), ttl).await;
                
                // 复制到其他节点
                let mut node_ids: Vec<String> = nodes.keys().cloned().collect();
                node_ids.sort();
                
                let primary_index = node_ids.iter().position(|id| id == &hash_node.id).unwrap_or(0);
                
                for i in 1..self.replication_factor {
                    let replica_index = (primary_index + i) % node_ids.len();
                    if let Some(replica_node) = nodes.get(&node_ids[replica_index]) {
                        let _ = replica_node.set(key.clone(), value.clone(), ttl).await;
                    }
                }
                
                return result;
            }
        }
        
        Err("没有可用的缓存节点".to_string())
    }
    
    async fn delete(&self, key: &str) -> bool {
        let hash_ring = self.hash_ring.lock().unwrap();
        let nodes = self.nodes.lock().unwrap();
        
        let mut deleted = false;
        
        // 从所有节点删除
        for node in nodes.values() {
            if node.delete(key).await {
                deleted = true;
            }
        }
        
        deleted
    }
    
    async fn get_stats(&self) -> Vec<CacheStats> {
        let nodes = self.nodes.lock().unwrap();
        let mut stats = Vec::new();
        
        for node in nodes.values() {
            stats.push(node.get_stats());
        }
        
        stats
    }
}

// 缓存更新策略
enum UpdateStrategy {
    WriteThrough,   // 同步写入
    WriteBehind,    // 异步写入
    RefreshAhead,   // 提前刷新
}

// 缓存管理器
struct CacheManager {
    distributed_cache: Arc<DistributedCache>,
    update_strategy: UpdateStrategy,
    background_tasks: Arc<Mutex<Vec<tokio::task::JoinHandle<()>>>>,
}

impl CacheManager {
    fn new(distributed_cache: Arc<DistributedCache>, update_strategy: UpdateStrategy) -> Self {
        Self {
            distributed_cache,
            update_strategy,
            background_tasks: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    async fn get_with_fallback(&self, key: &str, fallback_fn: impl Fn() -> String + Send + Sync) -> String {
        // 尝试从缓存获取
        if let Some(value) = self.distributed_cache.get(key).await {
            return value;
        }
        
        // 缓存未命中，调用fallback函数
        let value = fallback_fn();
        
        // 根据策略更新缓存
        match self.update_strategy {
            UpdateStrategy::WriteThrough => {
                let _ = self.distributed_cache.set(key.to_string(), value.clone(), None).await;
            }
            UpdateStrategy::WriteBehind => {
                let cache = Arc::clone(&self.distributed_cache);
                let key = key.to_string();
                let value = value.clone();
                
                let handle = tokio::spawn(async move {
                    let _ = cache.set(key, value, None).await;
                });
                
                let mut tasks = self.background_tasks.lock().unwrap();
                tasks.push(handle);
            }
            UpdateStrategy::RefreshAhead => {
                // 提前刷新逻辑
                let cache = Arc::clone(&self.distributed_cache);
                let key = key.to_string();
                
                let handle = tokio::spawn(async move {
                    // 模拟异步刷新
                    tokio::time::sleep(Duration::from_secs(1)).await;
                    let _ = cache.set(key, "refreshed_value".to_string(), None).await;
                });
                
                let mut tasks = self.background_tasks.lock().unwrap();
                tasks.push(handle);
            }
        }
        
        value
    }
}

#[tokio::main]
async fn main() {
    // 创建分布式缓存
    let distributed_cache = Arc::new(DistributedCache::new(2));
    
    // 添加缓存节点
    distributed_cache.add_node(
        "node-1".to_string(),
        1000,
        EvictionPolicy::LRU,
    ).await;
    
    distributed_cache.add_node(
        "node-2".to_string(),
        1000,
        EvictionPolicy::LFU,
    ).await;
    
    distributed_cache.add_node(
        "node-3".to_string(),
        1000,
        EvictionPolicy::FIFO,
    ).await;
    
    // 测试基本操作
    println!("=== 基本缓存操作测试 ===");
    
    // 设置缓存
    distributed_cache.set("key1".to_string(), "value1".to_string(), None).await.unwrap();
    distributed_cache.set("key2".to_string(), "value2".to_string(), Some(Duration::from_secs(5))).await.unwrap();
    
    // 获取缓存
    if let Some(value) = distributed_cache.get("key1").await {
        println!("获取到缓存: key1 = {}", value);
    }
    
    if let Some(value) = distributed_cache.get("key2").await {
        println!("获取到缓存: key2 = {}", value);
    }
    
    // 测试TTL过期
    println!("等待TTL过期...");
    tokio::time::sleep(Duration::from_secs(6)).await;
    
    if let Some(value) = distributed_cache.get("key2").await {
        println!("TTL后获取到缓存: key2 = {}", value);
    } else {
        println!("key2已过期");
    }
    
    // 测试缓存管理器
    println!("\n=== 缓存管理器测试 ===");
    let cache_manager = CacheManager::new(
        Arc::clone(&distributed_cache),
        UpdateStrategy::WriteThrough,
    );
    
    let fallback_fn = || "从数据库获取的值".to_string();
    let value = cache_manager.get_with_fallback("key3", fallback_fn).await;
    println!("缓存管理器结果: {}", value);
    
    // 获取统计信息
    println!("\n=== 缓存统计信息 ===");
    let stats = distributed_cache.get_stats().await;
    for stat in stats {
        println!("节点 {}: 大小={}/{}, 策略={:?}", 
            stat.node_id, stat.size, stat.max_size, stat.eviction_policy);
    }
    
    // 测试一致性哈希
    println!("\n=== 一致性哈希测试 ===");
    let mut hash_ring = ConsistentHashRing::new(150);
    hash_ring.add_node("node-1".to_string());
    hash_ring.add_node("node-2".to_string());
    hash_ring.add_node("node-3".to_string());
    
    for i in 0..10 {
        let key = format!("key{}", i);
        if let Some(node) = hash_ring.get_node(&key) {
            println!("键 {} 映射到节点 {}", key, node.id);
        }
    }
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

-- 缓存条目
data CacheEntry a = CacheEntry
    { cacheKey :: String
    , cacheValue :: a
    , createdAt :: UTCTime
    , lastAccessed :: UTCTime
    , accessCount :: Int
    , ttl :: Maybe Int -- 秒
    } deriving (Show)

newCacheEntry :: String -> a -> Maybe Int -> IO (CacheEntry a)
newCacheEntry key value ttl = do
    now <- getCurrentTime
    return $ CacheEntry key value now now 0 ttl

isExpired :: CacheEntry a -> IO Bool
isExpired entry = do
    now <- getCurrentTime
    case ttl entry of
        Just ttlSeconds -> do
            let diffSeconds = round $ diffUTCTime now (createdAt entry)
            return $ diffSeconds > ttlSeconds
        Nothing -> return False

touchEntry :: CacheEntry a -> IO (CacheEntry a)
touchEntry entry = do
    now <- getCurrentTime
    return $ entry { lastAccessed = now, accessCount = accessCount entry + 1 }

-- 缓存策略
data EvictionPolicy = LRU | LFU | FIFO | TTL deriving (Show, Eq)

-- 缓存节点
data CacheNode = CacheNode
    { nodeId :: String
    , cache :: TVar (M.Map String (CacheEntry String))
    , maxSize :: Int
    , evictionPolicy :: EvictionPolicy
    , accessOrder :: TVar [String]
    }

newCacheNode :: String -> Int -> EvictionPolicy -> IO CacheNode
newCacheNode id maxSize policy = do
    cache <- newTVarIO M.empty
    accessOrder <- newTVarIO []
    return $ CacheNode id cache maxSize policy accessOrder

getFromNode :: CacheNode -> String -> IO (Maybe String)
getFromNode node key = do
    atomically $ do
        cacheMap <- readTVar (cache node)
        case M.lookup key cacheMap of
            Just entry -> do
                -- 检查是否过期
                now <- liftIO getCurrentTime
                case ttl entry of
                    Just ttlSeconds -> do
                        let diffSeconds = round $ diffUTCTime now (createdAt entry)
                        if diffSeconds > ttlSeconds
                            then do
                                writeTVar (cache node) (M.delete key cacheMap)
                                return Nothing
                            else do
                                -- 更新访问信息
                                let updatedEntry = entry { 
                                    lastAccessed = now
                                , accessCount = accessCount entry + 1
                                }
                                writeTVar (cache node) (M.insert key updatedEntry cacheMap)
                                
                                -- 更新访问顺序
                                order <- readTVar (accessOrder node)
                                let newOrder = key : filter (/= key) order
                                writeTVar (accessOrder node) newOrder
                                
                                return $ Just (cacheValue updatedEntry)
                    Nothing -> do
                        -- 更新访问信息
                        let updatedEntry = entry { 
                            lastAccessed = now
                        , accessCount = accessCount entry + 1
                        }
                        writeTVar (cache node) (M.insert key updatedEntry cacheMap)
                        
                        -- 更新访问顺序
                        order <- readTVar (accessOrder node)
                        let newOrder = key : filter (/= key) order
                        writeTVar (accessOrder node) newOrder
                        
                        return $ Just (cacheValue updatedEntry)
            Nothing -> return Nothing

setInNode :: CacheNode -> String -> String -> Maybe Int -> IO Bool
setInNode node key value ttl = do
    atomically $ do
        cacheMap <- readTVar (cache node)
        
        -- 检查容量限制
        if M.size cacheMap >= maxSize node && not (M.member key cacheMap)
            then do
                evictEntry node cacheMap
                return True
            else do
                entry <- liftIO $ newCacheEntry key value ttl
                writeTVar (cache node) (M.insert key entry cacheMap)
                
                -- 更新访问顺序
                order <- readTVar (accessOrder node)
                let newOrder = key : filter (/= key) order
                writeTVar (accessOrder node) newOrder
                
                return True

evictEntry :: CacheNode -> M.Map String (CacheEntry String) -> STM ()
evictEntry node cacheMap = do
    order <- readTVar (accessOrder node)
    case evictionPolicy node of
        LRU -> do
            case order of
                (key:_) -> do
                    writeTVar (cache node) (M.delete key cacheMap)
                    writeTVar (accessOrder node) (tail order)
                [] -> return ()
        LFU -> do
            -- 找到访问次数最少的条目
            let entries = M.elems cacheMap
            case entries of
                [] -> return ()
                _ -> do
                    let minEntry = minimumBy (\a b -> compare (accessCount a) (accessCount b)) entries
                    let key = cacheKey minEntry
                    writeTVar (cache node) (M.delete key cacheMap)
                    newOrder <- readTVar (accessOrder node)
                    writeTVar (accessOrder node) (filter (/= key) newOrder)
        FIFO -> do
            -- 找到最早创建的条目
            let entries = M.elems cacheMap
            case entries of
                [] -> return ()
                _ -> do
                    let oldestEntry = minimumBy (\a b -> compare (createdAt a) (createdAt b)) entries
                    let key = cacheKey oldestEntry
                    writeTVar (cache node) (M.delete key cacheMap)
                    newOrder <- readTVar (accessOrder node)
                    writeTVar (accessOrder node) (filter (/= key) newOrder)
        TTL -> do
            -- 找到最早过期的条目
            let entries = M.elems cacheMap
            case entries of
                [] -> return ()
                _ -> do
                    let ttlEntries = filter (\e -> ttl e /= Nothing) entries
                    case ttlEntries of
                        [] -> return ()
                        _ -> do
                            let oldestEntry = minimumBy (\a b -> compare (createdAt a) (createdAt b)) ttlEntries
                            let key = cacheKey oldestEntry
                            writeTVar (cache node) (M.delete key cacheMap)
                            newOrder <- readTVar (accessOrder node)
                            writeTVar (accessOrder node) (filter (/= key) newOrder)

deleteFromNode :: CacheNode -> String -> IO Bool
deleteFromNode node key = do
    atomically $ do
        cacheMap <- readTVar (cache node)
        if M.member key cacheMap
            then do
                writeTVar (cache node) (M.delete key cacheMap)
                order <- readTVar (accessOrder node)
                writeTVar (accessOrder node) (filter (/= key) order)
                return True
            else return False

-- 一致性哈希环
data HashNode = HashNode
    { hashNodeId :: String
    , hashValue :: Int
    , virtualId :: Maybe Int
    } deriving (Show)

data ConsistentHashRing = ConsistentHashRing
    { nodes :: [HashNode]
    , virtualNodes :: Int
    }

newConsistentHashRing :: Int -> ConsistentHashRing
newConsistentHashRing virtualNodes = ConsistentHashRing [] virtualNodes

addNode :: ConsistentHashRing -> String -> ConsistentHashRing
addNode ring nodeId = 
    let baseHash = hash nodeId
        virtualNodes = map (\i -> HashNode nodeId (hash (nodeId ++ show i)) (Just i)) [0..virtualNodes ring - 1]
        newNodes = nodes ring ++ virtualNodes
        sortedNodes = sortBy (\a b -> compare (hashValue a) (hashValue b)) newNodes
    in ring { nodes = sortedNodes }

removeNode :: ConsistentHashRing -> String -> ConsistentHashRing
removeNode ring nodeId = 
    let filteredNodes = filter (\node -> not (isPrefixOf nodeId (hashNodeId node))) (nodes ring)
    in ring { nodes = filteredNodes }

getNode :: ConsistentHashRing -> String -> Maybe HashNode
getNode ring key = 
    let keyHash = hash key
        matchingNodes = filter (\node -> hashValue node >= keyHash) (nodes ring)
    in case matchingNodes of
        (node:_) -> Just node
        [] -> listToMaybe (nodes ring)

-- 分布式缓存
data DistributedCache = DistributedCache
    { cacheNodes :: TVar (M.Map String CacheNode)
    , hashRing :: TVar ConsistentHashRing
    , replicationFactor :: Int
    }

newDistributedCache :: Int -> IO DistributedCache
newDistributedCache replicationFactor = do
    nodes <- newTVarIO M.empty
    ring <- newTVarIO (newConsistentHashRing 150)
    return $ DistributedCache nodes ring replicationFactor

addCacheNode :: DistributedCache -> String -> Int -> EvictionPolicy -> IO ()
addCacheNode distributed nodeId maxSize policy = do
    node <- newCacheNode nodeId maxSize policy
    atomically $ do
        nodes <- readTVar (cacheNodes distributed)
        writeTVar (cacheNodes distributed) (M.insert nodeId node nodes)
        
        ring <- readTVar (hashRing distributed)
        writeTVar (hashRing distributed) (addNode ring nodeId)

getFromCache :: DistributedCache -> String -> IO (Maybe String)
getFromCache distributed key = do
    atomically $ do
        ring <- readTVar (hashRing distributed)
        nodes <- readTVar (cacheNodes distributed)
        
        case getNode ring key of
            Just hashNode -> do
                case M.lookup (hashNodeId hashNode) nodes of
                    Just cacheNode -> liftIO $ getFromNode cacheNode key
                    Nothing -> return Nothing
            Nothing -> return Nothing

setInCache :: DistributedCache -> String -> String -> Maybe Int -> IO Bool
setInCache distributed key value ttl = do
    atomically $ do
        ring <- readTVar (hashRing distributed)
        nodes <- readTVar (cacheNodes distributed)
        
        case getNode ring key of
            Just hashNode -> do
                case M.lookup (hashNodeId hashNode) nodes of
                    Just cacheNode -> do
                        result <- liftIO $ setInNode cacheNode key value ttl
                        
                        -- 复制到其他节点
                        let nodeIds = M.keys nodes
                        let primaryIndex = fromMaybe 0 $ elemIndex (hashNodeId hashNode) nodeIds
                        
                        -- 简化复制逻辑
                        return result
                    Nothing -> return False
            Nothing -> return False

-- 测试函数
testDistributedCache :: IO ()
testDistributedCache = do
    putStrLn "=== 分布式缓存测试 ==="
    
    distributed <- newDistributedCache 2
    
    -- 添加节点
    addCacheNode distributed "node-1" 1000 LRU
    addCacheNode distributed "node-2" 1000 LFU
    addCacheNode distributed "node-3" 1000 FIFO
    
    -- 设置缓存
    setInCache distributed "key1" "value1" Nothing
    setInCache distributed "key2" "value2" (Just 5)
    
    -- 获取缓存
    result1 <- getFromCache distributed "key1"
    case result1 of
        Just value -> putStrLn $ "获取到缓存: key1 = " ++ value
        Nothing -> putStrLn "key1 未找到"
    
    result2 <- getFromCache distributed "key2"
    case result2 of
        Just value -> putStrLn $ "获取到缓存: key2 = " ++ value
        Nothing -> putStrLn "key2 未找到"
    
    -- 测试TTL
    putStrLn "等待TTL过期..."
    threadDelay 6000000 -- 6秒
    
    result3 <- getFromCache distributed "key2"
    case result3 of
        Just value -> putStrLn $ "TTL后获取到缓存: key2 = " ++ value
        Nothing -> putStrLn "key2 已过期"

testConsistentHash :: IO ()
testConsistentHash = do
    putStrLn "\n=== 一致性哈希测试 ==="
    
    let ring = addNode (addNode (addNode (newConsistentHashRing 150) "node-1") "node-2") "node-3"
    
    mapM_ (\i -> do
        let key = "key" ++ show i
        case getNode ring key of
            Just node -> putStrLn $ "键 " ++ key ++ " 映射到节点 " ++ hashNodeId node
            Nothing -> putStrLn $ "键 " ++ key ++ " 没有映射到节点"
        ) [1..10]

main :: IO ()
main = do
    testDistributedCache
    testConsistentHash
```

## Lean实现思路
```lean
-- 缓存条目
structure CacheEntry (α : Type) where
  key : String
  value : α
  createdAt : Nat -- 简化时间表示
  lastAccessed : Nat
  accessCount : Nat
  ttl : Option Nat

def newCacheEntry (key : String) (value : α) (ttl : Option Nat) : CacheEntry α :=
  { key := key
  , value := value
  , createdAt := 0 -- 简化实现
  , lastAccessed := 0
  , accessCount := 0
  , ttl := ttl
  }

def isExpired (entry : CacheEntry α) (currentTime : Nat) : Bool :=
  match entry.ttl with
  | some ttl => currentTime - entry.createdAt > ttl
  | none => false

def touchEntry (entry : CacheEntry α) (currentTime : Nat) : CacheEntry α :=
  { entry with 
      lastAccessed := currentTime
    , accessCount := entry.accessCount + 1
  }

-- 缓存策略
inductive EvictionPolicy where
  | LRU
  | LFU
  | FIFO
  | TTL

-- 缓存节点
structure CacheNode where
  nodeId : String
  cache : Map String (CacheEntry String)
  maxSize : Nat
  evictionPolicy : EvictionPolicy
  accessOrder : List String

def newCacheNode (id : String) (maxSize : Nat) (policy : EvictionPolicy) : CacheNode :=
  { nodeId := id
  , cache := Map.empty
  , maxSize := maxSize
  , evictionPolicy := policy
  , accessOrder := []
  }

def getFromNode (node : CacheNode) (key : String) (currentTime : Nat) : Sum String (Option String) :=
  match node.cache.find? key with
  | some entry => 
      if isExpired entry currentTime
        then Sum.inr none
        else 
          let updatedEntry := touchEntry entry currentTime
          let newOrder := key :: (node.accessOrder.filter fun k => k != key)
          let updatedNode := { node with 
              cache := node.cache.insert key updatedEntry
            , accessOrder := newOrder
            }
          Sum.inl (updatedEntry.value)
  | none => Sum.inr none

def setInNode (node : CacheNode) (key : String) (value : String) (ttl : Option Nat) (currentTime : Nat) : CacheNode :=
  let entry := newCacheEntry key value ttl
  let newOrder := key :: (node.accessOrder.filter fun k => k != key)
  
  if node.cache.size >= node.maxSize && not (node.cache.contains key)
    then 
      -- 需要驱逐条目
      let evictedCache := evictEntry node currentTime
      { node with 
          cache := evictedCache.insert key entry
        , accessOrder := newOrder
        }
    else
      { node with 
          cache := node.cache.insert key entry
        , accessOrder := newOrder
        }

def evictEntry (node : CacheNode) (currentTime : Nat) : Map String (CacheEntry String) :=
  match node.evictionPolicy with
  | EvictionPolicy.LRU => 
      match node.accessOrder with
      | [] => node.cache
      | (key :: _) => node.cache.erase key
  | EvictionPolicy.LFU => 
      -- 找到访问次数最少的条目
      let minEntry := node.cache.values.minBy fun a b => compare a.accessCount b.accessCount
      match minEntry with
      | some entry => node.cache.erase entry.key
      | none => node.cache
  | EvictionPolicy.FIFO => 
      -- 找到最早创建的条目
      let oldestEntry := node.cache.values.minBy fun a b => compare a.createdAt b.createdAt
      match oldestEntry with
      | some entry => node.cache.erase entry.key
      | none => node.cache
  | EvictionPolicy.TTL => 
      -- 找到最早过期的条目
      let ttlEntries := node.cache.values.filter fun entry => entry.ttl.isSome
      let oldestEntry := ttlEntries.minBy fun a b => compare a.createdAt b.createdAt
      match oldestEntry with
      | some entry => node.cache.erase entry.key
      | none => node.cache

-- 一致性哈希环
structure HashNode where
  nodeId : String
  hashValue : Nat
  virtualId : Option Nat

structure ConsistentHashRing where
  nodes : List HashNode
  virtualNodes : Nat

def newConsistentHashRing (virtualNodes : Nat) : ConsistentHashRing :=
  { nodes := []
  , virtualNodes := virtualNodes
  }

def addNode (ring : ConsistentHashRing) (nodeId : String) : ConsistentHashRing :=
  let virtualNodes := List.range ring.virtualNodes
  let newNodes := virtualNodes.map fun i => 
    { nodeId := nodeId
    , hashValue := hash (nodeId ++ toString i)
    , virtualId := some i
    }
  let allNodes := ring.nodes ++ newNodes
  let sortedNodes := allNodes.sortBy fun a b => compare a.hashValue b.hashValue
  { ring with nodes := sortedNodes }

def getNode (ring : ConsistentHashRing) (key : String) : Option HashNode :=
  let keyHash := hash key
  let matchingNodes := ring.nodes.filter fun node => node.hashValue >= keyHash
  match matchingNodes with
  | (node :: _) => some node
  | [] => ring.nodes.head?

-- 分布式缓存
structure DistributedCache where
  nodes : Map String CacheNode
  hashRing : ConsistentHashRing
  replicationFactor : Nat

def newDistributedCache (replicationFactor : Nat) : DistributedCache :=
  { nodes := Map.empty
  , hashRing := newConsistentHashRing 150
  , replicationFactor := replicationFactor
  }

def addCacheNode (cache : DistributedCache) (nodeId : String) (maxSize : Nat) (policy : EvictionPolicy) : DistributedCache :=
  let node := newCacheNode nodeId maxSize policy
  let updatedNodes := cache.nodes.insert nodeId node
  let updatedRing := addNode cache.hashRing nodeId
  { cache with 
      nodes := updatedNodes
    , hashRing := updatedRing
    }

def getFromCache (cache : DistributedCache) (key : String) (currentTime : Nat) : Option String :=
  let targetNode := getNode cache.hashRing key
  match targetNode with
  | some hashNode => 
      let cacheNode := cache.nodes.find? hashNode.nodeId
      match cacheNode with
      | some node => 
          match getFromNode node key currentTime with
          | Sum.inl value => some value
          | Sum.inr _ => none
      | none => none
  | none => none

def setInCache (cache : DistributedCache) (key : String) (value : String) (ttl : Option Nat) (currentTime : Nat) : DistributedCache :=
  let targetNode := getNode cache.hashRing key
  match targetNode with
  | some hashNode => 
      let cacheNode := cache.nodes.find? hashNode.nodeId
      match cacheNode with
      | some node => 
          let updatedNode := setInNode node key value ttl currentTime
          { cache with nodes := cache.nodes.insert hashNode.nodeId updatedNode }
      | none => cache
  | none => cache
```

## 应用场景
- 数据库查询缓存
- 会话存储
- API响应缓存
- 分布式锁

## 最佳实践
- 合理设置TTL
- 实现缓存预热
- 监控缓存命中率
- 避免缓存雪崩 