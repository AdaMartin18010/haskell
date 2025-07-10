# 006 享元模式 (Flyweight Pattern)

## 1. 理论基础

### 1.1 模式定义
享元模式是一种结构型设计模式，通过共享技术有效支持大量细粒度对象的复用，节省内存和提升性能。享元模式将对象的状态分为内部状态（可共享）和外部状态（不可共享）。

### 1.2 核心概念
- **Flyweight（享元）**: 包含内部状态的共享对象
- **ConcreteFlyweight（具体享元）**: 实现享元接口，存储内部状态
- **UnsharedConcreteFlyweight（非共享具体享元）**: 不能被共享的享元子类
- **FlyweightFactory（享元工厂）**: 创建和管理享元对象，确保享元被正确共享
- **Client（客户端）**: 维护对享元的引用，计算或存储享元的外部状态

### 1.3 设计原则
- **单一职责**: 享元只负责内部状态，客户端负责外部状态
- **开闭原则**: 支持扩展新的享元类型
- **最小知识原则**: 享元对象之间相互独立

### 1.4 优缺点分析
**优点：**
- 大幅减少内存使用
- 提高系统性能
- 支持大量对象
- 对象复用效率高

**缺点：**
- 增加系统复杂性
- 外部状态管理复杂
- 可能影响线程安全
- 调试困难

## 2. 接口设计

### 2.1 核心接口
```haskell
-- Haskell接口设计
class Flyweight a where
  operation :: a -> String -> String
  getIntrinsicState :: a -> String

-- 享元工厂
class FlyweightFactory a where
  getFlyweight :: a -> String -> IO Flyweight
  getFlyweightCount :: a -> IO Int
  clearCache :: a -> IO ()
```

### 2.2 扩展接口
```haskell
-- 支持缓存的享元
class (Flyweight a) => CachedFlyweight a where
  getCache :: a -> Map String String
  setCache :: a -> String -> String -> a
  isCached :: a -> String -> Bool

-- 支持池化的享元
class (Flyweight a) => PooledFlyweight a where
  getPool :: a -> FlyweightPool
  returnToPool :: a -> Flyweight -> IO ()
  getPoolSize :: a -> IO Int
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import qualified Data.Map as Map
import Data.IORef
import Control.Concurrent.MVar

-- 享元接口
class Flyweight a where
  operation :: a -> String -> String
  getIntrinsicState :: a -> String

-- 具体享元
data ConcreteFlyweight = ConcreteFlyweight {
  intrinsicState :: String,
  sharedData :: String
} deriving Show

instance Flyweight ConcreteFlyweight where
  operation flyweight extrinsicState = 
    "享元操作: " ++ intrinsicState flyweight ++ " + " ++ extrinsicState
  
  getIntrinsicState = intrinsicState

-- 享元工厂
data FlyweightFactory = FlyweightFactory {
  pool :: MVar (Map.Map String ConcreteFlyweight),
  cache :: MVar (Map.Map String String)
} deriving Show

newFlyweightFactory :: IO FlyweightFactory
newFlyweightFactory = do
  poolRef <- newMVar Map.empty
  cacheRef <- newMVar Map.empty
  return $ FlyweightFactory poolRef cacheRef

-- 获取享元
getFlyweight :: FlyweightFactory -> String -> IO ConcreteFlyweight
getFlyweight factory key = do
  poolMap <- takeMVar (pool factory)
  case Map.lookup key poolMap of
    Just flyweight -> do
      putMVar (pool factory) poolMap
      putStrLn $ "复用享元: " ++ key
      return flyweight
    Nothing -> do
      let newFlyweight = ConcreteFlyweight key ("共享数据-" ++ key)
      putMVar (pool factory) (Map.insert key newFlyweight poolMap)
      putStrLn $ "创建新享元: " ++ key
      return newFlyweight

-- 获取享元数量
getFlyweightCount :: FlyweightFactory -> IO Int
getFlyweightCount factory = do
  poolMap <- readMVar (pool factory)
  return $ Map.size poolMap

-- 清空缓存
clearCache :: FlyweightFactory -> IO ()
clearCache factory = do
  putMVar (pool factory) Map.empty
  putMVar (cache factory) Map.empty
  putStrLn "清空享元缓存"

-- 字符享元
data CharacterFlyweight = CharacterFlyweight {
  character :: Char,
  font :: String,
  size :: Int
} deriving Show

instance Flyweight CharacterFlyweight where
  operation flyweight color = 
    "字符: " ++ [character flyweight] ++ 
    " 字体: " ++ font flyweight ++ 
    " 大小: " ++ show (size flyweight) ++ 
    " 颜色: " ++ color
  
  getIntrinsicState flyweight = 
    [character flyweight] ++ font flyweight ++ show (size flyweight)

-- 字符享元工厂
data CharacterFactory = CharacterFactory {
  characterPool :: MVar (Map.Map String CharacterFlyweight)
} deriving Show

newCharacterFactory :: IO CharacterFactory
newCharacterFactory = do
  poolRef <- newMVar Map.empty
  return $ CharacterFactory poolRef

getCharacter :: CharacterFactory -> Char -> String -> Int -> IO CharacterFlyweight
getCharacter factory char font size = do
  let key = [char] ++ font ++ show size
  poolMap <- takeMVar (characterPool factory)
  case Map.lookup key poolMap of
    Just character -> do
      putMVar (characterPool factory) poolMap
      putStrLn $ "复用字符享元: " ++ key
      return character
    Nothing -> do
      let newCharacter = CharacterFlyweight char font size
      putMVar (characterPool factory) (Map.insert key newCharacter poolMap)
      putStrLn $ "创建新字符享元: " ++ key
      return newCharacter

-- 图形享元
data ShapeFlyweight = ShapeFlyweight {
  shapeType :: String,
  color :: String
} deriving Show

instance Flyweight ShapeFlyweight where
  operation flyweight position = 
    "图形: " ++ shapeType flyweight ++ 
    " 颜色: " ++ color flyweight ++ 
    " 位置: " ++ position
  
  getIntrinsicState flyweight = 
    shapeType flyweight ++ color flyweight

-- 图形享元工厂
data ShapeFactory = ShapeFactory {
  shapePool :: MVar (Map.Map String ShapeFlyweight)
} deriving Show

newShapeFactory :: IO ShapeFactory
newShapeFactory = do
  poolRef <- newMVar Map.empty
  return $ ShapeFactory poolRef

getShape :: ShapeFactory -> String -> String -> IO ShapeFlyweight
getShape factory shapeType color = do
  let key = shapeType ++ color
  poolMap <- takeMVar (shapePool factory)
  case Map.lookup key poolMap of
    Just shape -> do
      putMVar (shapePool factory) poolMap
      putStrLn $ "复用图形享元: " ++ key
      return shape
    Nothing -> do
      let newShape = ShapeFlyweight shapeType color
      putMVar (shapePool factory) (Map.insert key newShape poolMap)
      putStrLn $ "创建新图形享元: " ++ key
      return newShape

-- 使用示例
main :: IO ()
main = do
  putStrLn "享元模式示例:"
  
  -- 基本享元工厂
  factory <- newFlyweightFactory
  
  putStrLn "\n=== 基本享元 ==="
  flyweight1 <- getFlyweight factory "A"
  flyweight2 <- getFlyweight factory "A"
  flyweight3 <- getFlyweight factory "B"
  
  putStrLn $ operation flyweight1 "红色"
  putStrLn $ operation flyweight2 "蓝色"
  putStrLn $ operation flyweight3 "绿色"
  
  count <- getFlyweightCount factory
  putStrLn $ "享元数量: " ++ show count
  
  -- 字符享元
  charFactory <- newCharacterFactory
  
  putStrLn "\n=== 字符享元 ==="
  char1 <- getCharacter charFactory 'A' "Arial" 12
  char2 <- getCharacter charFactory 'A' "Arial" 12
  char3 <- getCharacter charFactory 'B' "Times" 14
  
  putStrLn $ operation char1 "红色"
  putStrLn $ operation char2 "蓝色"
  putStrLn $ operation char3 "绿色"
  
  -- 图形享元
  shapeFactory <- newShapeFactory
  
  putStrLn "\n=== 图形享元 ==="
  shape1 <- getShape shapeFactory "圆形" "红色"
  shape2 <- getShape shapeFactory "圆形" "红色"
  shape3 <- getShape shapeFactory "方形" "蓝色"
  
  putStrLn $ operation shape1 "(100, 100)"
  putStrLn $ operation shape2 "(200, 200)"
  putStrLn $ operation shape3 "(300, 300)"
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 享元trait
trait Flyweight {
    fn operation(&self, extrinsic_state: &str) -> String;
    fn get_intrinsic_state(&self) -> &str;
}

// 具体享元
#[derive(Debug, Clone)]
struct ConcreteFlyweight {
    intrinsic_state: String,
    shared_data: String,
}

impl ConcreteFlyweight {
    fn new(intrinsic_state: String, shared_data: String) -> Self {
        ConcreteFlyweight {
            intrinsic_state,
            shared_data,
        }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) -> String {
        format!(
            "享元操作: {} + {}",
            self.intrinsic_state, extrinsic_state
        )
    }
    
    fn get_intrinsic_state(&self) -> &str {
        &self.intrinsic_state
    }
}

// 享元工厂
#[derive(Debug)]
struct FlyweightFactory {
    pool: Arc<Mutex<HashMap<String, Arc<ConcreteFlyweight>>>>,
    cache: Arc<Mutex<HashMap<String, String>>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        FlyweightFactory {
            pool: Arc::new(Mutex::new(HashMap::new())),
            cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn get_flyweight(&self, key: &str) -> Arc<ConcreteFlyweight> {
        let mut pool = self.pool.lock().unwrap();
        pool.entry(key.to_string())
            .or_insert_with(|| {
                println!("创建新享元: {}", key);
                Arc::new(ConcreteFlyweight::new(
                    key.to_string(),
                    format!("共享数据-{}", key),
                ))
            })
            .clone()
    }
    
    fn get_flyweight_count(&self) -> usize {
        let pool = self.pool.lock().unwrap();
        pool.len()
    }
    
    fn clear_cache(&self) {
        let mut pool = self.pool.lock().unwrap();
        let mut cache = self.cache.lock().unwrap();
        pool.clear();
        cache.clear();
        println!("清空享元缓存");
    }
}

// 字符享元
#[derive(Debug, Clone)]
struct CharacterFlyweight {
    character: char,
    font: String,
    size: u32,
}

impl CharacterFlyweight {
    fn new(character: char, font: String, size: u32) -> Self {
        CharacterFlyweight {
            character,
            font,
            size,
        }
    }
}

impl Flyweight for CharacterFlyweight {
    fn operation(&self, color: &str) -> String {
        format!(
            "字符: {} 字体: {} 大小: {} 颜色: {}",
            self.character, self.font, self.size, color
        )
    }
    
    fn get_intrinsic_state(&self) -> &str {
        // 简化实现
        "character"
    }
}

// 字符享元工厂
#[derive(Debug)]
struct CharacterFactory {
    character_pool: Arc<Mutex<HashMap<String, Arc<CharacterFlyweight>>>>,
}

impl CharacterFactory {
    fn new() -> Self {
        CharacterFactory {
            character_pool: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn get_character(&self, character: char, font: &str, size: u32) -> Arc<CharacterFlyweight> {
        let key = format!("{}{}{}", character, font, size);
        let mut pool = self.character_pool.lock().unwrap();
        pool.entry(key.clone())
            .or_insert_with(|| {
                println!("创建新字符享元: {}", key);
                Arc::new(CharacterFlyweight::new(character, font.to_string(), size))
            })
            .clone()
    }
}

// 图形享元
#[derive(Debug, Clone)]
struct ShapeFlyweight {
    shape_type: String,
    color: String,
}

impl ShapeFlyweight {
    fn new(shape_type: String, color: String) -> Self {
        ShapeFlyweight {
            shape_type,
            color,
        }
    }
}

impl Flyweight for ShapeFlyweight {
    fn operation(&self, position: &str) -> String {
        format!(
            "图形: {} 颜色: {} 位置: {}",
            self.shape_type, self.color, position
        )
    }
    
    fn get_intrinsic_state(&self) -> &str {
        &self.shape_type
    }
}

// 图形享元工厂
#[derive(Debug)]
struct ShapeFactory {
    shape_pool: Arc<Mutex<HashMap<String, Arc<ShapeFlyweight>>>>,
}

impl ShapeFactory {
    fn new() -> Self {
        ShapeFactory {
            shape_pool: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn get_shape(&self, shape_type: &str, color: &str) -> Arc<ShapeFlyweight> {
        let key = format!("{}{}", shape_type, color);
        let mut pool = self.shape_pool.lock().unwrap();
        pool.entry(key.clone())
            .or_insert_with(|| {
                println!("创建新图形享元: {}", key);
                Arc::new(ShapeFlyweight::new(shape_type.to_string(), color.to_string()))
            })
            .clone()
    }
}

// 使用示例
fn main() {
    println!("享元模式示例:");
    
    // 基本享元工厂
    let factory = FlyweightFactory::new();
    
    println!("\n=== 基本享元 ===");
    let flyweight1 = factory.get_flyweight("A");
    let flyweight2 = factory.get_flyweight("A");
    let flyweight3 = factory.get_flyweight("B");
    
    println!("{}", flyweight1.operation("红色"));
    println!("{}", flyweight2.operation("蓝色"));
    println!("{}", flyweight3.operation("绿色"));
    
    println!("享元数量: {}", factory.get_flyweight_count());
    
    // 字符享元
    let char_factory = CharacterFactory::new();
    
    println!("\n=== 字符享元 ===");
    let char1 = char_factory.get_character('A', "Arial", 12);
    let char2 = char_factory.get_character('A', "Arial", 12);
    let char3 = char_factory.get_character('B', "Times", 14);
    
    println!("{}", char1.operation("红色"));
    println!("{}", char2.operation("蓝色"));
    println!("{}", char3.operation("绿色"));
    
    // 图形享元
    let shape_factory = ShapeFactory::new();
    
    println!("\n=== 图形享元 ===");
    let shape1 = shape_factory.get_shape("圆形", "红色");
    let shape2 = shape_factory.get_shape("圆形", "红色");
    let shape3 = shape_factory.get_shape("方形", "蓝色");
    
    println!("{}", shape1.operation("(100, 100)"));
    println!("{}", shape2.operation("(200, 200)"));
    println!("{}", shape3.operation("(300, 300)"));
}
```

### 3.3 Lean实现

```lean
-- 享元类型类
class Flyweight (α : Type) where
  operation : α → String → String
  getIntrinsicState : α → String

-- 具体享元
structure ConcreteFlyweight where
  intrinsicState : String
  sharedData : String

def newConcreteFlyweight (intrinsic : String) (shared : String) : ConcreteFlyweight := {
  intrinsicState := intrinsic,
  sharedData := shared
}

instance : Flyweight ConcreteFlyweight where
  operation flyweight extrinsicState := 
    "享元操作: " ++ flyweight.intrinsicState ++ " + " ++ extrinsicState
  
  getIntrinsicState flyweight := flyweight.intrinsicState

-- 享元工厂
structure FlyweightFactory where
  pool : List (String × ConcreteFlyweight)
  cache : List (String × String)

def newFlyweightFactory : FlyweightFactory := {
  pool := [],
  cache := []
}

def getFlyweight (factory : FlyweightFactory) (key : String) : (ConcreteFlyweight × FlyweightFactory) :=
  match factory.pool.find? (fun (k, _) => k = key) with
  | some (_, flyweight) => 
    (flyweight, { factory with pool := factory.pool })
  | none =>
    let newFlyweight := newConcreteFlyweight key ("共享数据-" ++ key)
    (newFlyweight, { factory with pool := (key, newFlyweight) :: factory.pool })

def getFlyweightCount (factory : FlyweightFactory) : Nat :=
  factory.pool.length

def clearCache (factory : FlyweightFactory) : FlyweightFactory := {
  pool := [],
  cache := []
}

-- 字符享元
structure CharacterFlyweight where
  character : Char
  font : String
  size : Nat

def newCharacterFlyweight (char : Char) (font : String) (size : Nat) : CharacterFlyweight := {
  character := char,
  font := font,
  size := size
}

instance : Flyweight CharacterFlyweight where
  operation flyweight color := 
    "字符: " ++ toString flyweight.character ++ 
    " 字体: " ++ flyweight.font ++ 
    " 大小: " ++ toString flyweight.size ++ 
    " 颜色: " ++ color
  
  getIntrinsicState flyweight := 
    toString flyweight.character ++ flyweight.font ++ toString flyweight.size

-- 字符享元工厂
structure CharacterFactory where
  characterPool : List (String × CharacterFlyweight)

def newCharacterFactory : CharacterFactory := {
  characterPool := []
}

def getCharacter (factory : CharacterFactory) (char : Char) (font : String) (size : Nat) : (CharacterFlyweight × CharacterFactory) :=
  let key := toString char ++ font ++ toString size
  match factory.characterPool.find? (fun (k, _) => k = key) with
  | some (_, character) => 
    (character, { factory with characterPool := factory.characterPool })
  | none =>
    let newCharacter := newCharacterFlyweight char font size
    (newCharacter, { factory with characterPool := (key, newCharacter) :: factory.characterPool })

-- 使用示例
def main : IO Unit := do
  IO.println "享元模式示例:"
  
  -- 基本享元工厂
  let factory := newFlyweightFactory
  let (flyweight1, factory1) := getFlyweight factory "A"
  let (flyweight2, factory2) := getFlyweight factory1 "A"
  let (flyweight3, factory3) := getFlyweight factory2 "B"
  
  IO.println ("=== 基本享元 ===")
  IO.println (operation flyweight1 "红色")
  IO.println (operation flyweight2 "蓝色")
  IO.println (operation flyweight3 "绿色")
  
  IO.println ("享元数量: " ++ toString (getFlyweightCount factory3))
  
  -- 字符享元
  let charFactory := newCharacterFactory
  let (char1, charFactory1) := getCharacter charFactory 'A' "Arial" 12
  let (char2, charFactory2) := getCharacter charFactory1 'A' "Arial" 12
  let (char3, charFactory3) := getCharacter charFactory2 'B' "Times" 14
  
  IO.println ("=== 字符享元 ===")
  IO.println (operation char1 "红色")
  IO.println (operation char2 "蓝色")
  IO.println (operation char3 "绿色")
```

## 4. 工程实践

### 4.1 设计考虑
- **状态分离**: 明确区分内部状态和外部状态
- **线程安全**: 确保享元工厂的线程安全
- **内存管理**: 合理管理享元对象的生命周期
- **性能优化**: 避免享元成为性能瓶颈

### 4.2 实现模式
```haskell
-- 线程安全享元工厂
data ThreadSafeFlyweightFactory = ThreadSafeFlyweightFactory {
  factory :: MVar FlyweightFactory,
  lock :: MVar ()
}

-- 带缓存的享元
data CachedFlyweight = CachedFlyweight {
  flyweight :: Flyweight,
  cache :: MVar (Map String String)
}

-- 带监控的享元
data MonitoredFlyweight = MonitoredFlyweight {
  flyweight :: Flyweight,
  metrics :: MVar FlyweightMetrics
}
```

### 4.3 错误处理
```haskell
-- 错误类型
data FlyweightError = 
  PoolFull String
  | InvalidKey String
  | CacheMiss String

-- 安全享元获取
safeGetFlyweight :: FlyweightFactory -> String -> IO (Either FlyweightError Flyweight)
safeGetFlyweight factory key = 
  try (getFlyweight factory key) >>= \case
    Left e -> return $ Left $ InvalidKey (show e)
    Right flyweight -> return $ Right flyweight
```

## 5. 性能优化

### 5.1 内存优化
- **对象池**: 复用享元对象
- **弱引用**: 自动回收未使用的享元
- **内存对齐**: 优化访问性能

### 5.2 缓存策略
```haskell
-- LRU缓存享元
data LRUFlyweightCache = LRUFlyweightCache {
  cache :: MVar (Map String (Flyweight, UTCTime)),
  maxSize :: Int
}

-- TTL缓存享元
data TTLFlyweightCache = TTLFlyweightCache {
  cache :: MVar (Map String (Flyweight, UTCTime)),
  ttl :: NominalDiffTime
}
```

### 5.3 并发优化
- **读写锁**: 支持并发读取
- **分片缓存**: 减少锁竞争
- **异步加载**: 非阻塞享元创建

## 6. 应用场景

### 6.1 字符串常量池
```haskell
-- 字符串享元
data StringFlyweight = StringFlyweight {
  content :: String,
  hash :: Int
} deriving Show

-- 字符串工厂
data StringFactory = StringFactory {
  stringPool :: MVar (Map.Map String StringFlyweight)
}

-- 获取字符串享元
getString :: StringFactory -> String -> IO StringFlyweight
getString factory content = do
  let hash = hash content
  poolMap <- takeMVar (stringPool factory)
  case Map.lookup content poolMap of
    Just string -> do
      putMVar (stringPool factory) poolMap
      return string
    Nothing -> do
      let newString = StringFlyweight content hash
      putMVar (stringPool factory) (Map.insert content newString poolMap)
      return newString
```

### 6.2 图形对象复用
```haskell
-- 图形享元
data GraphicsFlyweight = GraphicsFlyweight {
  shapeType :: String,
  color :: String,
  style :: String
} deriving Show

-- 图形工厂
data GraphicsFactory = GraphicsFactory {
  graphicsPool :: MVar (Map.Map String GraphicsFlyweight)
}

-- 获取图形享元
getGraphics :: GraphicsFactory -> String -> String -> String -> IO GraphicsFlyweight
getGraphics factory shapeType color style = do
  let key = shapeType ++ color ++ style
  poolMap <- takeMVar (graphicsPool factory)
  case Map.lookup key poolMap of
    Just graphics -> do
      putMVar (graphicsPool factory) poolMap
      return graphics
    Nothing -> do
      let newGraphics = GraphicsFlyweight shapeType color style
      putMVar (graphicsPool factory) (Map.insert key newGraphics poolMap)
      return newGraphics
```

### 6.3 数据库连接池
```haskell
-- 连接享元
data ConnectionFlyweight = ConnectionFlyweight {
  connectionString :: String,
  connection :: Connection,
  lastUsed :: UTCTime
} deriving Show

-- 连接池
data ConnectionPool = ConnectionPool {
  connections :: MVar [ConnectionFlyweight],
  maxConnections :: Int,
  timeout :: NominalDiffTime
}

-- 获取连接
getConnection :: ConnectionPool -> String -> IO (Either String ConnectionFlyweight)
getConnection pool connectionString = do
  connections <- takeMVar (connections pool)
  let available = filter (\c -> connectionString c == connectionString) connections
  case available of
    (conn:_) -> do
      putMVar (connections pool) connections
      return $ Right conn
    [] -> do
      if length connections < maxConnections pool
      then do
        newConn <- createConnection connectionString
        let flyweight = ConnectionFlyweight connectionString newConn (getCurrentTime)
        putMVar (connections pool) (flyweight : connections)
        return $ Right flyweight
      else do
        putMVar (connections pool) connections
        return $ Left "连接池已满"
```

### 6.4 字体对象复用
```haskell
-- 字体享元
data FontFlyweight = FontFlyweight {
  fontName :: String,
  fontSize :: Int,
  fontStyle :: String
} deriving Show

-- 字体工厂
data FontFactory = FontFactory {
  fontPool :: MVar (Map.Map String FontFlyweight)
}

-- 获取字体享元
getFont :: FontFactory -> String -> Int -> String -> IO FontFlyweight
getFont factory name size style = do
  let key = name ++ show size ++ style
  poolMap <- takeMVar (fontPool factory)
  case Map.lookup key poolMap of
    Just font -> do
      putMVar (fontPool factory) poolMap
      return font
    Nothing -> do
      let newFont = FontFlyweight name size style
      putMVar (fontPool factory) (Map.insert key newFont poolMap)
      return newFont
```

## 7. 最佳实践

### 7.1 设计原则
- **状态分离**: 明确区分内部状态和外部状态
- **对象复用**: 最大化对象复用，减少内存使用
- **线程安全**: 确保享元工厂的线程安全
- **性能考虑**: 避免享元成为性能瓶颈

### 7.2 实现建议
```haskell
-- 享元工厂
class FlyweightFactory a where
  createFlyweight :: a -> String -> IO Flyweight
  listFlyweights :: a -> [String]
  validateFlyweight :: a -> Flyweight -> Bool

-- 享元注册表
data FlyweightRegistry = FlyweightRegistry {
  flyweights :: Map String (forall a. Flyweight a => a),
  metadata :: Map String String
}

-- 线程安全享元管理器
data ThreadSafeFlyweightManager = ThreadSafeFlyweightManager {
  manager :: MVar FlyweightManager,
  lock :: MVar ()
}
```

### 7.3 测试策略
```haskell
-- 享元测试
testFlyweight :: Flyweight a => a -> Bool
testFlyweight flyweight = 
  -- 测试享元的基本功能
  True

-- 性能测试
benchmarkFlyweight :: Flyweight a => a -> IO Double
benchmarkFlyweight flyweight = do
  start <- getCurrentTime
  replicateM_ 1000 $ operation flyweight "test"
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑
- **插件系统**: 支持动态加载新的享元类型
- **序列化**: 支持享元的序列化和反序列化
- **版本控制**: 支持享元接口的版本管理
- **分布式**: 支持跨网络的享元共享

## 8. 总结

享元模式是内存优化的重要工具，通过共享技术有效支持大量细粒度对象的复用。在实现时需要注意状态分离、线程安全和性能优化。该模式在字符串常量池、图形对象复用、数据库连接池、字体对象复用等场景中有广泛应用。
