# 006 备忘录模式 (Memento Pattern)

## 1. 理论基础

### 1.1 模式定义

备忘录模式是一种行为型设计模式，在不破坏封装的前提下，捕获并外部化对象的内部状态，这样以后就可以将该对象恢复到原先保存的状态。

### 1.2 核心概念

- **Originator（发起人）**: 创建备忘录，记录当前状态，使用备忘录恢复状态
- **Memento（备忘录）**: 存储发起人对象的内部状态
- **Caretaker（管理者）**: 负责保存备忘录，但不能对备忘录内容进行操作或检查
- **Client（客户端）**: 使用备忘录模式的对象

### 1.3 设计原则

- **封装保护**: 不破坏对象的封装性
- **单一职责**: 备忘录只负责状态存储
- **开闭原则**: 支持扩展新的状态类型

### 1.4 优缺点分析

**优点：**

- 保持对象封装性
- 简化发起人职责
- 支持状态回滚
- 易于实现撤销/重做

**缺点：**

- 可能消耗大量内存
- 状态恢复可能复杂
- 影响性能
- 可能导致内存泄漏

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Originator a where
  saveToMemento :: a -> Memento
  restoreFromMemento :: a -> Memento -> a
  getState :: a -> String
  setState :: a -> String -> a

class Memento a where
  getMementoState :: a -> String
  getTimestamp :: a -> UTCTime
  getVersion :: a -> Int

class Caretaker a where
  addMemento :: a -> Memento -> a
  getMemento :: a -> Int -> Maybe Memento
  removeMemento :: a -> Int -> a
  clearMementos :: a -> a
```

### 2.2 扩展接口

```haskell
-- 支持压缩的备忘录
class (Memento a) => CompressedMemento a where
  compress :: a -> CompressedData
  decompress :: CompressedData -> a

-- 支持增量保存的备忘录
class (Memento a) => IncrementalMemento a where
  getDiff :: a -> Memento -> Diff
  applyDiff :: a -> Diff -> a
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Data.Time.Clock
import Data.Map as Map

-- 备忘录类型
data MementoType = 
  FullMemento
  | IncrementalMemento
  | CompressedMemento
  deriving (Show, Eq)

-- 备忘录接口
class Memento a where
  getMementoState :: a -> String
  getTimestamp :: a -> UTCTime
  getVersion :: a -> Int
  getType :: a -> MementoType

-- 发起人接口
class Originator a where
  saveToMemento :: a -> IO Memento
  restoreFromMemento :: a -> Memento -> a
  getState :: a -> String
  setState :: a -> String -> a

-- 管理者接口
class Caretaker a where
  addMemento :: a -> Memento -> a
  getMemento :: a -> Int -> Maybe Memento
  removeMemento :: a -> Int -> a
  clearMementos :: a -> a
  getMementoCount :: a -> Int

-- 具体发起人
data ConcreteOriginator = ConcreteOriginator {
  state :: String,
  version :: Int,
  metadata :: Map String String
} deriving Show

instance Originator ConcreteOriginator where
  saveToMemento originator = do
    timestamp <- getCurrentTime
    return $ ConcreteMemento {
      mementoState = state originator,
      mementoTimestamp = timestamp,
      mementoVersion = version originator,
      mementoType = FullMemento,
      mementoMetadata = metadata originator
    }
  
  restoreFromMemento _ memento = ConcreteOriginator {
    state = getMementoState memento,
    version = getVersion memento + 1,
    metadata = getMementoMetadata memento
  }
  
  getState = state
  setState originator newState = originator { state = newState }

-- 具体备忘录
data ConcreteMemento = ConcreteMemento {
  mementoState :: String,
  mementoTimestamp :: UTCTime,
  mementoVersion :: Int,
  mementoType :: MementoType,
  mementoMetadata :: Map String String
} deriving Show

instance Memento ConcreteMemento where
  getMementoState = mementoState
  getTimestamp = mementoTimestamp
  getVersion = mementoVersion
  getType = mementoType

getMementoMetadata :: ConcreteMemento -> Map String String
getMementoMetadata = mementoMetadata

-- 压缩备忘录
data CompressedMemento = CompressedMemento {
  compressed_data: String,
  original_size: Int,
  compression_ratio: Double,
  memento_info: ConcreteMemento
} deriving Show

instance Memento CompressedMemento where
  getMementoState = mementoState . mementoInfo
  getTimestamp = mementoTimestamp . mementoInfo
  getVersion = mementoVersion . mementoInfo
  getType _ = CompressedMemento

instance CompressedMemento CompressedMemento where
  compress memento = 
    let originalData = mementoState (mementoInfo memento)
        compressedData = compressData originalData
        originalSize = length originalData
        compressedSize = length compressedData
        ratio = fromIntegral compressedSize / fromIntegral originalSize
    in memento { 
      compressedData = compressedData,
      originalSize = originalSize,
      compressionRatio = ratio
    }
  
  decompress memento = 
    let decompressedData = decompressData (compressedData memento)
    in (mementoInfo memento) { mementoState = decompressedData }

-- 增量备忘录
data IncrementalMemento = IncrementalMemento {
  baseMemento :: ConcreteMemento,
  diffData :: Diff,
  diffSize :: Int
} deriving Show

instance Memento IncrementalMemento where
  getMementoState = mementoState . baseMemento
  getTimestamp = mementoTimestamp . baseMemento
  getVersion = mementoVersion . baseMemento
  getType _ = IncrementalMemento

instance IncrementalMemento IncrementalMemento where
  getDiff baseMemento targetMemento = 
    let baseState = mementoState baseMemento
        targetState = mementoState targetMemento
        diff = calculateDiff baseState targetState
    in IncrementalMemento {
      baseMemento = baseMemento,
      diffData = diff,
      diffSize = length (show diff)
    }
  
  applyDiff memento diff = 
    let baseState = mementoState (baseMemento memento)
        newState = applyDiffToState baseState (diffData memento)
    in (baseMemento memento) { mementoState = newState }

-- 具体管理者
data ConcreteCaretaker = ConcreteCaretaker {
  mementos :: [Memento],
  max_mementos :: Int,
  autoCleanup :: Bool
} deriving Show

instance Caretaker ConcreteCaretaker where
  addMemento caretaker memento = 
    let newMementos = memento : mementos caretaker
        limitedMementos = if autoCleanup caretaker && length newMementos > maxMementos caretaker
                          then take (maxMementos caretaker) newMementos
                          else newMementos
    in caretaker { mementos = limitedMementos }
  
  getMemento caretaker index = 
    if index >= 0 && index < length (mementos caretaker)
    then Just (mementos caretaker !! index)
    else Nothing
  
  removeMemento caretaker index = 
    let currentMementos = mementos caretaker
        newMementos = take index currentMementos ++ drop (index + 1) currentMementos
    in caretaker { mementos = newMementos }
  
  clearMementos caretaker = caretaker { mementos = [] }
  
  getMementoCount caretaker = length (mementos caretaker)

-- 高级管理者
data AdvancedCaretaker = AdvancedCaretaker {
  mementos :: Map Int Memento,
  currentIndex :: Int,
  maxHistory :: Int,
  compressionEnabled :: Bool
} deriving Show

instance Caretaker AdvancedCaretaker where
  addMemento caretaker memento = 
    let newIndex = currentIndex caretaker + 1
        compressedMemento = if compressionEnabled caretaker
                           then compressMemento memento
                           else memento
        newMementos = Map.insert newIndex compressedMemento (mementos caretaker)
        limitedMementos = if Map.size newMementos > maxHistory caretaker
                          then Map.delete (minimum (Map.keys newMementos)) newMementos
                          else newMementos
    in caretaker { 
      mementos = limitedMementos,
      currentIndex = newIndex
    }
  
  getMemento caretaker index = Map.lookup index (mementos caretaker)
  
  removeMemento caretaker index = 
    caretaker { mementos = Map.delete index (mementos caretaker) }
  
  clearMementos caretaker = 
    caretaker { mementos = Map.empty, currentIndex = 0 }
  
  getMementoCount caretaker = Map.size (mementos caretaker)

-- 辅助函数
compressData :: String -> String
compressData = id -- 简化实现

decompressData :: String -> String
decompressData = id -- 简化实现

calculateDiff :: String -> String -> Diff
calculateDiff base target = Diff { -- 简化实现
  diffOperations = [],
  diffSize = abs (length target - length base)
}

applyDiffToState :: String -> Diff -> String
applyDiffToState state _ = state -- 简化实现

compressMemento :: Memento -> Memento
compressMemento memento = CompressedMemento {
  compressedData = compressData (getMementoState memento),
  originalSize = length (getMementoState memento),
  compressionRatio = 0.5,
  mementoInfo = ConcreteMemento {
    mementoState = getMementoState memento,
    mementoTimestamp = getTimestamp memento,
    mementoVersion = getVersion memento,
    mementoType = CompressedMemento,
    mementoMetadata = Map.empty
  }
}

-- 使用示例
main :: IO ()
main = do
  -- 创建发起人
  let originator = ConcreteOriginator "初始状态" 1 Map.empty
  
  putStrLn "备忘录模式示例:"
  
  -- 创建管理者
  let caretaker = ConcreteCaretaker [] 10 True
  let advancedCaretaker = AdvancedCaretaker Map.empty 0 5 True
  
  -- 保存初始状态
  memento1 <- saveToMemento originator
  let caretaker' = addMemento caretaker memento1
  let advancedCaretaker' = addMemento advancedCaretaker memento1
  
  putStrLn $ "初始状态: " ++ getState originator
  
  -- 修改状态
  let originator' = setState originator "修改后的状态"
  memento2 <- saveToMemento originator'
  let caretaker'' = addMemento caretaker' memento2
  let advancedCaretaker'' = addMemento advancedCaretaker' memento2
  
  putStrLn $ "修改后状态: " ++ getState originator'
  
  -- 再次修改状态
  let originator'' = setState originator' "最终状态"
  memento3 <- saveToMemento originator''
  let caretaker''' = addMemento caretaker'' memento3
  let advancedCaretaker''' = addMemento advancedCaretaker'' memento3
  
  putStrLn $ "最终状态: " ++ getState originator''
  
  -- 恢复到第一个状态
  case getMemento caretaker''' 0 of
    Just memento -> do
      let restored = restoreFromMemento originator'' memento
      putStrLn $ "恢复到第一个状态: " ++ getState restored
    Nothing -> putStrLn "无法恢复状态"
  
  -- 恢复到第二个状态
  case getMemento caretaker''' 1 of
    Just memento -> do
      let restored = restoreFromMemento originator'' memento
      putStrLn $ "恢复到第二个状态: " ++ getState restored
    Nothing -> putStrLn "无法恢复状态"
  
  putStrLn $ "管理者中的备忘录数量: " ++ show (getMementoCount caretaker''')
  putStrLn $ "高级管理者中的备忘录数量: " ++ show (getMementoCount advancedCaretaker''')
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

// 备忘录类型
#[derive(Debug, Clone, PartialEq)]
enum MementoType {
    Full,
    Incremental,
    Compressed,
}

// 备忘录trait
trait Memento {
    fn get_state(&self) -> &str;
    fn get_timestamp(&self) -> u64;
    fn get_version(&self) -> u32;
    fn get_type(&self) -> MementoType;
}

// 发起人trait
trait Originator {
    type MementoType: Memento;
    fn save_to_memento(&self) -> Self::MementoType;
    fn restore_from_memento(&mut self, memento: &Self::MementoType);
    fn get_state(&self) -> &str;
    fn set_state(&mut self, state: String);
}

// 管理者trait
trait Caretaker {
    type MementoType: Memento;
    fn add_memento(&mut self, memento: Self::MementoType);
    fn get_memento(&self, index: usize) -> Option<&Self::MementoType>;
    fn remove_memento(&mut self, index: usize);
    fn clear_mementos(&mut self);
    fn get_memento_count(&self) -> usize;
}

// 具体发起人
#[derive(Debug)]
struct ConcreteOriginator {
    state: String,
    version: u32,
    metadata: HashMap<String, String>,
}

impl ConcreteOriginator {
    fn new(state: String) -> Self {
        ConcreteOriginator {
            state,
            version: 1,
            metadata: HashMap::new(),
        }
    }
}

impl Originator for ConcreteOriginator {
    type MementoType = ConcreteMemento;
    
    fn save_to_memento(&self) -> Self::MementoType {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        ConcreteMemento {
            state: self.state.clone(),
            timestamp,
            version: self.version,
            memento_type: MementoType::Full,
            metadata: self.metadata.clone(),
        }
    }
    
    fn restore_from_memento(&mut self, memento: &Self::MementoType) {
        self.state = memento.get_state().to_string();
        self.version = memento.get_version() + 1;
        self.metadata = memento.get_metadata().clone();
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
    
    fn set_state(&mut self, state: String) {
        self.state = state;
    }
}

// 具体备忘录
#[derive(Debug)]
struct ConcreteMemento {
    state: String,
    timestamp: u64,
    version: u32,
    memento_type: MementoType,
    metadata: HashMap<String, String>,
}

impl Memento for ConcreteMemento {
    fn get_state(&self) -> &str {
        &self.state
    }
    
    fn get_timestamp(&self) -> u64 {
        self.timestamp
    }
    
    fn get_version(&self) -> u32 {
        self.version
    }
    
    fn get_type(&self) -> MementoType {
        self.memento_type.clone()
    }
}

impl ConcreteMemento {
    fn get_metadata(&self) -> &HashMap<String, String> {
        &self.metadata
    }
}

// 压缩备忘录
#[derive(Debug)]
struct CompressedMemento {
    compressed_data: String,
    original_size: usize,
    compression_ratio: f64,
    memento_info: ConcreteMemento,
}

impl Memento for CompressedMemento {
    fn get_state(&self) -> &str {
        self.memento_info.get_state()
    }
    
    fn get_timestamp(&self) -> u64 {
        self.memento_info.get_timestamp()
    }
    
    fn get_version(&self) -> u32 {
        self.memento_info.get_version()
    }
    
    fn get_type(&self) -> MementoType {
        MementoType::Compressed
    }
}

impl CompressedMemento {
    fn compress(memento: ConcreteMemento) -> Self {
        let original_data = memento.get_state();
        let compressed_data = compress_data(original_data);
        let original_size = original_data.len();
        let compressed_size = compressed_data.len();
        let ratio = compressed_size as f64 / original_size as f64;
        
        CompressedMemento {
            compressed_data,
            original_size,
            compression_ratio: ratio,
            memento_info: memento,
        }
    }
    
    fn decompress(&self) -> ConcreteMemento {
        let decompressed_data = decompress_data(&self.compressed_data);
        ConcreteMemento {
            state: decompressed_data,
            timestamp: self.memento_info.get_timestamp(),
            version: self.memento_info.get_version(),
            memento_type: MementoType::Full,
            metadata: self.memento_info.get_metadata().clone(),
        }
    }
}

// 具体管理者
#[derive(Debug)]
struct ConcreteCaretaker {
    mementos: Vec<Box<dyn Memento>>,
    max_mementos: usize,
    auto_cleanup: bool,
}

impl ConcreteCaretaker {
    fn new(max_mementos: usize) -> Self {
        ConcreteCaretaker {
            mementos: Vec::new(),
            max_mementos,
            auto_cleanup: true,
        }
    }
}

impl Caretaker for ConcreteCaretaker {
    type MementoType = Box<dyn Memento>;
    
    fn add_memento(&mut self, memento: Self::MementoType) {
        self.mementos.push(memento);
        
        if self.auto_cleanup && self.mementos.len() > self.max_mementos {
            self.mementos.remove(0);
        }
    }
    
    fn get_memento(&self, index: usize) -> Option<&Self::MementoType> {
        self.mementos.get(index)
    }
    
    fn remove_memento(&mut self, index: usize) {
        if index < self.mementos.len() {
            self.mementos.remove(index);
        }
    }
    
    fn clear_mementos(&mut self) {
        self.mementos.clear();
    }
    
    fn get_memento_count(&self) -> usize {
        self.mementos.len()
    }
}

// 高级管理者
#[derive(Debug)]
struct AdvancedCaretaker {
    mementos: HashMap<u32, Box<dyn Memento>>,
    current_index: u32,
    max_history: usize,
    compression_enabled: bool,
}

impl AdvancedCaretaker {
    fn new(max_history: usize) -> Self {
        AdvancedCaretaker {
            mementos: HashMap::new(),
            current_index: 0,
            max_history,
            compression_enabled: true,
        }
    }
}

impl Caretaker for AdvancedCaretaker {
    type MementoType = Box<dyn Memento>;
    
    fn add_memento(&mut self, memento: Self::MementoType) {
        self.current_index += 1;
        self.mementos.insert(self.current_index, memento);
        
        if self.mementos.len() > self.max_history {
            let oldest_key = self.mementos.keys().min().cloned();
            if let Some(key) = oldest_key {
                self.mementos.remove(&key);
            }
        }
    }
    
    fn get_memento(&self, index: usize) -> Option<&Self::MementoType> {
        self.mementos.get(&(index as u32))
    }
    
    fn remove_memento(&mut self, index: usize) {
        self.mementos.remove(&(index as u32));
    }
    
    fn clear_mementos(&mut self) {
        self.mementos.clear();
        self.current_index = 0;
    }
    
    fn get_memento_count(&self) -> usize {
        self.mementos.len()
    }
}

// 辅助函数
fn compress_data(data: &str) -> String {
    data.to_string() // 简化实现
}

fn decompress_data(data: &str) -> String {
    data.to_string() // 简化实现
}

// 使用示例
fn main() {
    let mut originator = ConcreteOriginator::new("初始状态".to_string());
    let mut caretaker = ConcreteCaretaker::new(10);
    let mut advanced_caretaker = AdvancedCaretaker::new(5);
    
    println!("备忘录模式示例:");
    
    // 保存初始状态
    let memento1 = originator.save_to_memento();
    caretaker.add_memento(Box::new(memento1.clone()));
    advanced_caretaker.add_memento(Box::new(memento1));
    
    println!("初始状态: {}", originator.get_state());
    
    // 修改状态
    originator.set_state("修改后的状态".to_string());
    let memento2 = originator.save_to_memento();
    caretaker.add_memento(Box::new(memento2.clone()));
    advanced_caretaker.add_memento(Box::new(memento2));
    
    println!("修改后状态: {}", originator.get_state());
    
    // 再次修改状态
    originator.set_state("最终状态".to_string());
    let memento3 = originator.save_to_memento();
    caretaker.add_memento(Box::new(memento3.clone()));
    advanced_caretaker.add_memento(Box::new(memento3));
    
    println!("最终状态: {}", originator.get_state());
    
    // 恢复到第一个状态
    if let Some(memento) = caretaker.get_memento(0) {
        originator.restore_from_memento(&ConcreteMemento {
            state: memento.get_state().to_string(),
            timestamp: memento.get_timestamp(),
            version: memento.get_version(),
            memento_type: memento.get_type(),
            metadata: HashMap::new(),
        });
        println!("恢复到第一个状态: {}", originator.get_state());
    }
    
    // 恢复到第二个状态
    if let Some(memento) = caretaker.get_memento(1) {
        originator.restore_from_memento(&ConcreteMemento {
            state: memento.get_state().to_string(),
            timestamp: memento.get_timestamp(),
            version: memento.get_version(),
            memento_type: memento.get_type(),
            metadata: HashMap::new(),
        });
        println!("恢复到第二个状态: {}", originator.get_state());
    }
    
    println!("管理者中的备忘录数量: {}", caretaker.get_memento_count());
    println!("高级管理者中的备忘录数量: {}", advanced_caretaker.get_memento_count());
}
```

### 3.3 Lean实现

```lean
-- 备忘录类型
inductive MementoType where
  | Full : MementoType
  | Incremental : MementoType
  | Compressed : MementoType

-- 备忘录类型类
class Memento (α : Type) where
  getMementoState : α → String
  getTimestamp : α → Nat
  getVersion : α → Nat
  getType : α → MementoType

-- 发起人类型类
class Originator (α : Type) where
  saveToMemento : α → Memento
  restoreFromMemento : α → Memento → α
  getState : α → String
  setState : α → String → α

-- 管理者类型类
class Caretaker (α : Type) where
  addMemento : α → Memento → α
  getMemento : α → Nat → Option Memento
  removeMemento : α → Nat → α
  clearMementos : α → α
  getMementoCount : α → Nat

-- 具体发起人
structure ConcreteOriginator where
  state : String
  version : Nat
  metadata : List (String × String)

def newOriginator (state : String) : ConcreteOriginator := {
  state := state,
  version := 1,
  metadata := []
}

instance : Originator ConcreteOriginator where
  saveToMemento originator := ConcreteMemento.mk
    originator.state
    (System.currentTimeMillis)
    originator.version
    MementoType.Full
    originator.metadata
  
  restoreFromMemento _ memento := {
    state := getMementoState memento,
    version := getVersion memento + 1,
    metadata := getMementoMetadata memento
  }
  
  getState originator := originator.state
  
  setState originator newState := { originator with state := newState }

-- 具体备忘录
structure ConcreteMemento where
  state : String
  timestamp : Nat
  version : Nat
  mementoType : MementoType
  metadata : List (String × String)

instance : Memento ConcreteMemento where
  getMementoState memento := memento.state
  getTimestamp memento := memento.timestamp
  getVersion memento := memento.version
  getType memento := memento.mementoType

def getMementoMetadata (memento : ConcreteMemento) : List (String × String) :=
  memento.metadata

-- 压缩备忘录
structure CompressedMemento where
  compressedData : String
  originalSize : Nat
  compressionRatio : Float
  mementoInfo : ConcreteMemento

instance : Memento CompressedMemento where
  getMementoState memento := getMementoState memento.mementoInfo
  getTimestamp memento := getTimestamp memento.mementoInfo
  getVersion memento := getVersion memento.mementoInfo
  getType _ := MementoType.Compressed

instance : CompressedMemento CompressedMemento where
  compress memento := {
    compressedData := compressData (getMementoState memento.mementoInfo),
    originalSize := (getMementoState memento.mementoInfo).length,
    compressionRatio := 0.5,
    mementoInfo := memento.mementoInfo
  }
  
  decompress memento := {
    mementoInfo with state := decompressData memento.compressedData
  }

-- 具体管理者
structure ConcreteCaretaker where
  mementos : List Memento
  maxMementos : Nat
  autoCleanup : Bool

def newCaretaker (maxMementos : Nat) : ConcreteCaretaker := {
  mementos := [],
  maxMementos := maxMementos,
  autoCleanup := true
}

instance : Caretaker ConcreteCaretaker where
  addMemento caretaker memento := {
    mementos := memento :: caretaker.mementos,
    maxMementos := caretaker.maxMementos,
    autoCleanup := caretaker.autoCleanup
  }
  
  getMemento caretaker index := 
    if index < caretaker.mementos.length
    then some (caretaker.mementos.get! index)
    else none
  
  removeMemento caretaker index := {
    mementos := caretaker.mementos.erase index,
    maxMementos := caretaker.maxMementos,
    autoCleanup := caretaker.autoCleanup
  }
  
  clearMementos caretaker := {
    mementos := [],
    maxMementos := caretaker.maxMementos,
    autoCleanup := caretaker.autoCleanup
  }
  
  getMementoCount caretaker := caretaker.mementos.length

-- 高级管理者
structure AdvancedCaretaker where
  mementos : List (Nat × Memento)
  currentIndex : Nat
  maxHistory : Nat
  compressionEnabled : Bool

def newAdvancedCaretaker (maxHistory : Nat) : AdvancedCaretaker := {
  mementos := [],
  currentIndex := 0,
  maxHistory := maxHistory,
  compressionEnabled := true
}

instance : Caretaker AdvancedCaretaker where
  addMemento caretaker memento := {
    mementos := (caretaker.currentIndex + 1, memento) :: caretaker.mementos,
    currentIndex := caretaker.currentIndex + 1,
    maxHistory := caretaker.maxHistory,
    compressionEnabled := caretaker.compressionEnabled
  }
  
  getMemento caretaker index := 
    caretaker.mementos.find? (fun (i, _) => i = index) |>.map Prod.snd
  
  removeMemento caretaker index := {
    mementos := caretaker.mementos.filter (fun (i, _) => i ≠ index),
    currentIndex := caretaker.currentIndex,
    maxHistory := caretaker.maxHistory,
    compressionEnabled := caretaker.compressionEnabled
  }
  
  clearMementos caretaker := {
    mementos := [],
    currentIndex := 0,
    maxHistory := caretaker.maxHistory,
    compressionEnabled := caretaker.compressionEnabled
  }
  
  getMementoCount caretaker := caretaker.mementos.length

-- 辅助函数
def compressData (data : String) : String := data -- 简化实现
def decompressData (data : String) : String := data -- 简化实现

-- 使用示例
def main : IO Unit := do
  let originator := newOriginator "初始状态"
  let caretaker := newCaretaker 10
  let advancedCaretaker := newAdvancedCaretaker 5
  
  IO.println "备忘录模式示例:"
  
  let memento1 := saveToMemento originator
  let caretaker' := addMemento caretaker memento1
  let advancedCaretaker' := addMemento advancedCaretaker memento1
  
  IO.println ("初始状态: " ++ getState originator)
  
  let originator' := setState originator "修改后的状态"
  let memento2 := saveToMemento originator'
  let caretaker'' := addMemento caretaker' memento2
  let advancedCaretaker'' := addMemento advancedCaretaker' memento2
  
  IO.println ("修改后状态: " ++ getState originator')
  
  let originator'' := setState originator' "最终状态"
  let memento3 := saveToMemento originator''
  let caretaker''' := addMemento caretaker'' memento3
  let advancedCaretaker''' := addMemento advancedCaretaker'' memento3
  
  IO.println ("最终状态: " ++ getState originator'')
  
  match getMemento caretaker''' 0 with
  | some memento => do
    let restored := restoreFromMemento originator'' memento
    IO.println ("恢复到第一个状态: " ++ getState restored)
  | none => IO.println "无法恢复状态"
  
  match getMemento caretaker''' 1 with
  | some memento => do
    let restored := restoreFromMemento originator'' memento
    IO.println ("恢复到第二个状态: " ++ getState restored)
  | none => IO.println "无法恢复状态"
  
  IO.println ("管理者中的备忘录数量: " ++ toString (getMementoCount caretaker'''))
  IO.println ("高级管理者中的备忘录数量: " ++ toString (getMementoCount advancedCaretaker'''))
```

## 4. 工程实践

### 4.1 设计考虑

- **内存管理**: 避免备忘录占用过多内存
- **性能优化**: 优化备忘录的创建和恢复
- **错误处理**: 处理备忘录损坏、版本不兼容等
- **并发安全**: 支持多线程环境下的备忘录操作

### 4.2 实现模式

```haskell
-- 带缓存的管理者
data CachedCaretaker = CachedCaretaker {
  caretaker :: Caretaker,
  cache :: MVar (Map String Memento)
}

-- 异步备忘录管理器
data AsyncCaretaker = AsyncCaretaker {
  caretaker :: Caretaker,
  executor :: ThreadPool
}

-- 带监控的管理者
data MonitoredCaretaker = MonitoredCaretaker {
  caretaker :: Caretaker,
  metrics :: MVar CaretakerMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data MementoError = 
  MementoCorrupted String
  | VersionIncompatible Int Int
  | MemoryExceeded
  | RestoreFailed String

-- 安全恢复
safeRestore :: Originator a => a -> Memento -> IO (Either MementoError a)
safeRestore originator memento = 
  try (return $ restoreFromMemento originator memento) >>= \case
    Left e -> return $ Left $ RestoreFailed (show e)
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 内存优化

- **增量保存**: 只保存状态变化的部分
- **压缩存储**: 压缩备忘录数据
- **分页管理**: 将备忘录分页存储
- **垃圾回收**: 定期清理过期备忘录

### 5.2 性能优化

```haskell
-- 增量备忘录
data IncrementalMemento = IncrementalMemento {
  baseMemento :: Memento,
  diffData :: Diff,
  diffSize :: Int
}

-- 压缩备忘录
data CompressedMemento = CompressedMemento {
  compressedData :: ByteString,
  originalSize :: Int,
  compressionRatio :: Double
}

-- 分页备忘录管理器
data PagedCaretaker = PagedCaretaker {
  pages :: [MementoPage],
  currentPage :: Int,
  pageSize :: Int
}
```

## 6. 应用场景

### 6.1 撤销/重做系统

```haskell
-- 撤销重做管理器
data UndoRedoManager = UndoRedoManager {
  undoStack :: [Memento],
  redoStack :: [Memento],
  maxHistory :: Int
}

-- 撤销操作
undo :: UndoRedoManager -> Originator -> IO (Maybe Originator)
undo manager originator = do
  case undoStack manager of
    (memento:rest) -> do
      let restored = restoreFromMemento originator memento
      return $ Just restored
    [] -> return Nothing

-- 重做操作
redo :: UndoRedoManager -> Originator -> IO (Maybe Originator)
redo manager originator = do
  case redoStack manager of
    (memento:rest) -> do
      let restored = restoreFromMemento originator memento
      return $ Just restored
    [] -> return Nothing
```

### 6.2 游戏存档系统

```haskell
-- 游戏存档管理器
data GameSaveManager = GameSaveManager {
  saveSlots :: Map Int GameSave,
  autoSave :: Bool,
  saveInterval :: Int
}

-- 游戏存档
data GameSave = GameSave {
  playerState :: PlayerState,
  worldState :: WorldState,
  timestamp :: UTCTime,
  version :: String
}

-- 保存游戏
saveGame :: GameSaveManager -> GameState -> IO ()
saveGame manager gameState = do
  let save = createGameSave gameState
  let slot = getNextSaveSlot manager
  updateSaveSlot manager slot save
```

### 6.3 数据库事务

```haskell
-- 数据库事务管理器
data TransactionManager = TransactionManager {
  activeTransactions :: [Transaction],
  checkpointInterval :: Int
}

-- 数据库事务
data Transaction = Transaction {
  transactionId :: String,
  operations :: [DatabaseOperation],
  rollbackData :: [Memento]
}

-- 事务回滚
rollbackTransaction :: TransactionManager -> String -> IO Bool
rollbackTransaction manager transactionId = do
  case findTransaction manager transactionId of
    Just transaction -> do
      mapM_ restoreMemento (rollbackData transaction)
      return True
    Nothing -> return False
```

### 6.4 配置管理

```haskell
-- 配置管理器
data ConfigManager = ConfigManager {
  currentConfig :: Config,
  configHistory :: [ConfigMemento],
  maxHistorySize :: Int
}

-- 配置备忘录
data ConfigMemento = ConfigMemento {
  configData :: Config,
  changeDescription :: String,
  timestamp :: UTCTime
}

-- 配置回滚
rollbackConfig :: ConfigManager -> Int -> IO Bool
rollbackConfig manager index = do
  case getConfigMemento manager index of
    Just memento -> do
      let restored = restoreFromMemento (currentConfig manager) memento
      updateCurrentConfig manager restored
      return True
    Nothing -> return False
```

## 7. 最佳实践

### 7.1 设计原则

- **保持备忘录简单**: 避免在备忘录中存储复杂逻辑
- **合理控制内存**: 限制备忘录数量和大小
- **版本兼容**: 支持备忘录版本升级
- **性能考虑**: 优化备忘录的创建和恢复性能

### 7.2 实现建议

```haskell
-- 备忘录工厂
class MementoFactory a where
  createMemento :: String -> Maybe a
  listMementoTypes :: [String]
  validateMemento :: a -> Bool

-- 备忘录注册表
data MementoRegistry = MementoRegistry {
  mementos :: Map String (forall a. Memento a => a),
  metadata :: Map String String
}

-- 线程安全备忘录管理器
data ThreadSafeMementoManager = ThreadSafeMementoManager {
  manager :: MVar MementoManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 备忘录测试
testMemento :: Memento a => a -> Bool
testMemento memento = 
  let state = getMementoState memento
  in not (null state) && isValidState state

-- 性能测试
benchmarkMemento :: Memento a => a -> IO Double
benchmarkMemento memento = do
  start <- getCurrentTime
  replicateM_ 1000 $ getMementoState memento
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的备忘录类型
- **序列化**: 支持备忘录的序列化和反序列化
- **版本控制**: 支持备忘录的版本管理
- **分布式**: 支持跨网络的备忘录存储

## 8. 总结

备忘录模式是保存和恢复对象状态的重要工具，通过封装对象状态提供了良好的封装性和可扩展性。在实现时需要注意内存管理、性能优化和版本兼容性。该模式在撤销/重做、游戏存档、数据库事务、配置管理等场景中都有广泛应用。
