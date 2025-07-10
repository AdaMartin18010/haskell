# 004 迭代器模式 (Iterator Pattern)

## 1. 理论基础

### 1.1 模式定义

迭代器模式是一种行为型设计模式，提供一种方法顺序访问聚合对象中的元素，而不暴露其内部表示。该模式将遍历逻辑从聚合对象中分离出来，使得聚合对象和遍历逻辑可以独立变化。

### 1.2 核心概念

- **Iterator（迭代器）**: 定义访问和遍历元素的接口
- **ConcreteIterator（具体迭代器）**: 实现迭代器接口，跟踪当前遍历位置
- **Aggregate（聚合）**: 定义创建迭代器对象的接口
- **ConcreteAggregate（具体聚合）**: 实现创建迭代器的接口，返回具体迭代器的实例
- **Client（客户端）**: 使用迭代器遍历聚合对象

### 1.3 设计原则

- **单一职责**: 将遍历逻辑从聚合对象中分离
- **开闭原则**: 对扩展开放，对修改封闭
- **依赖倒置**: 依赖于抽象而非具体实现

### 1.4 优缺点分析

**优点:**

- 简化聚合对象的接口
- 支持多种遍历方式
- 支持并行遍历
- 隐藏聚合对象的内部结构

**缺点:**

- 增加系统复杂性
- 可能影响性能
- 迭代器状态管理复杂
- 可能导致内存泄漏

## 2. 接口设计

### 2.1 核心接口

```haskell
-- Haskell接口设计
class Iterator a where
  next :: a -> Maybe (Item, a)
  hasNext :: a -> Bool
  current :: a -> Maybe Item
  reset :: a -> a

-- 聚合接口
class Aggregate a where
  createIterator :: a -> Iterator
  size :: a -> Int
  isEmpty :: a -> Bool
```

### 2.2 扩展接口

```haskell
-- 支持双向迭代的迭代器
class (Iterator a) => BidirectionalIterator a where
  previous :: a -> Maybe (Item, a)
  hasPrevious :: a -> Bool
  
-- 支持随机访问的迭代器
class (Iterator a) => RandomAccessIterator a where
  seek :: a -> Int -> a
  getIndex :: a -> Int
  getSize :: a -> Int
```

## 3. 多语言实现

### 3.1 Haskell实现

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- 迭代器类型
data IteratorType = 
  ForwardIterator
  | BidirectionalIterator
  | RandomAccessIterator
  deriving (Show, Eq)

-- 迭代器接口
class Iterator a where
  next :: a -> Maybe (String, a)
  hasNext :: a -> Bool
  current :: a -> Maybe String
  reset :: a -> a
  getType :: a -> IteratorType

-- 聚合接口
class Aggregate a where
  createIterator :: a -> Iterator
  size :: a -> Int
  isEmpty :: a -> Bool
  addItem :: a -> String -> a
  removeItem :: a -> String -> a

-- 具体聚合
data ConcreteAggregate = ConcreteAggregate {
  items :: [String],
  metadata :: Map String String
} deriving Show

instance Aggregate ConcreteAggregate where
  createIterator (ConcreteAggregate items _) = 
    ConcreteIterator items 0 ForwardIterator
  
  size (ConcreteAggregate items _) = length items
  
  isEmpty (ConcreteAggregate items _) = null items
  
  addItem (ConcreteAggregate items metadata) item = 
    ConcreteAggregate (item : items) metadata
  
  removeItem (ConcreteAggregate items metadata) item = 
    ConcreteAggregate (filter (/= item) items) metadata

-- 具体迭代器
data ConcreteIterator = ConcreteIterator {
  items :: [String],
  currentIndex :: Int,
  iteratorType :: IteratorType
} deriving Show

instance Iterator ConcreteIterator where
  next (ConcreteIterator [] _ _) = Nothing
  next (ConcreteIterator (x:xs) index _) = 
    Just (x, ConcreteIterator xs (index + 1) ForwardIterator)
  
  hasNext (ConcreteIterator [] _ _) = False
  hasNext (ConcreteIterator (_:_) _ _) = True
  
  current (ConcreteIterator [] _ _) = Nothing
  current (ConcreteIterator (x:_) _ _) = Just x
  
  reset iterator = iterator { currentIndex = 0 }
  
  getType iterator = iteratorType iterator

-- 双向迭代器
data BidirectionalIterator = BidirectionalIterator {
  items :: [String],
  currentIndex :: Int,
  direction :: Direction
} deriving Show

data Direction = Forward | Backward deriving Show

instance Iterator BidirectionalIterator where
  next (BidirectionalIterator items index Forward) = 
    if index < length items
    then Just (items !! index, BidirectionalIterator items (index + 1) Forward)
    else Nothing
  
  next (BidirectionalIterator items index Backward) = 
    if index > 0
    then Just (items !! (index - 1), BidirectionalIterator items (index - 1) Backward)
    else Nothing
  
  hasNext (BidirectionalIterator items index Forward) = index < length items
  hasNext (BidirectionalIterator items index Backward) = index > 0
  
  current (BidirectionalIterator items index _) = 
    if index >= 0 && index < length items
    then Just (items !! index)
    else Nothing
  
  reset iterator = iterator { currentIndex = 0, direction = Forward }
  
  getType _ = BidirectionalIterator

instance BidirectionalIterator BidirectionalIterator where
  previous (BidirectionalIterator items index Forward) = 
    if index > 0
    then Just (items !! (index - 1), BidirectionalIterator items (index - 1) Forward)
    else Nothing
  
  previous (BidirectionalIterator items index Backward) = 
    if index < length items - 1
    then Just (items !! (index + 1), BidirectionalIterator items (index + 1) Backward)
    else Nothing
  
  hasPrevious (BidirectionalIterator items index Forward) = index > 0
  hasPrevious (BidirectionalIterator items index Backward) = index < length items - 1

-- 随机访问迭代器
data RandomAccessIterator = RandomAccessIterator {
  items :: [String],
  currentIndex :: Int
} deriving Show

instance Iterator RandomAccessIterator where
  next (RandomAccessIterator items index) = 
    if index < length items
    then Just (items !! index, RandomAccessIterator items (index + 1))
    else Nothing
  
  hasNext (RandomAccessIterator items index) = index < length items
  
  current (RandomAccessIterator items index) = 
    if index >= 0 && index < length items
    then Just (items !! index)
    else Nothing
  
  reset iterator = iterator { currentIndex = 0 }
  
  getType _ = RandomAccessIterator

instance RandomAccessIterator RandomAccessIterator where
  seek (RandomAccessIterator items _) newIndex = 
    RandomAccessIterator items (max 0 (min newIndex (length items - 1)))
  
  getIndex (RandomAccessIterator _ index) = index
  
  getSize (RandomAccessIterator items _) = length items

-- 过滤迭代器
data FilterIterator = FilterIterator {
  baseIterator :: ConcreteIterator,
  predicate :: String -> Bool
} deriving Show

instance Iterator FilterIterator where
  next (FilterIterator iterator predicate) = 
    case next iterator of
      Just (item, nextIterator) -> 
        if predicate item
        then Just (item, FilterIterator nextIterator predicate)
        else next (FilterIterator nextIterator predicate)
      Nothing -> Nothing
  
  hasNext (FilterIterator iterator predicate) = 
    case next iterator of
      Just (item, _) -> predicate item || hasNext (FilterIterator iterator predicate)
      Nothing -> False
  
  current (FilterIterator iterator predicate) = 
    case current iterator of
      Just item -> if predicate item then Just item else Nothing
      Nothing -> Nothing
  
  reset (FilterIterator iterator predicate) = 
    FilterIterator (reset iterator) predicate
  
  getType _ = ForwardIterator

-- 映射迭代器
data MapIterator = MapIterator {
  baseIterator :: ConcreteIterator,
  mapper :: String -> String
} deriving Show

instance Iterator MapIterator where
  next (MapIterator iterator mapper) = 
    case next iterator of
      Just (item, nextIterator) -> 
        Just (mapper item, MapIterator nextIterator mapper)
      Nothing -> Nothing
  
  hasNext (MapIterator iterator _) = hasNext iterator
  
  current (MapIterator iterator mapper) = 
    case current iterator of
      Just item -> Just (mapper item)
      Nothing -> Nothing
  
  reset (MapIterator iterator mapper) = 
    MapIterator (reset iterator) mapper
  
  getType _ = ForwardIterator

-- 使用示例
main :: IO ()
main = do
  -- 创建聚合对象
  let aggregate = ConcreteAggregate ["Item1", "Item2", "Item3", "Item4"] Map.empty
  
  putStrLn "迭代器模式示例:"
  
  -- 基本迭代器
  let iterator = createIterator aggregate
  putStrLn "\n基本迭代器执行:"
  iterateWithIterator iterator
  
  -- 双向迭代器
  let bidirectionalIterator = BidirectionalIterator (items aggregate) 0 Forward
  putStrLn "\n双向迭代器执行:"
  iterateBidirectional bidirectionalIterator
  
  -- 随机访问迭代器
  let randomIterator = RandomAccessIterator (items aggregate) 0
  putStrLn "\n随机访问迭代器执行:"
  iterateRandomAccess randomIterator
  
  -- 过滤迭代器
  let filterIterator = FilterIterator iterator (\item -> length item > 4)
  putStrLn "\n过滤迭代器执行 (长度>4):"
  iterateWithIterator filterIterator
  
  -- 映射迭代器
  let mapIterator = MapIterator iterator (\item -> "Processed: " ++ item)
  putStrLn "\n映射迭代器执行:"
  iterateWithIterator mapIterator

-- 辅助函数
iterateWithIterator :: Iterator a => a -> IO ()
iterateWithIterator iterator = 
  if hasNext iterator
  then do
    case next iterator of
      Just (item, nextIterator) -> do
        putStrLn $ "当前项: " ++ item
        iterateWithIterator nextIterator
      Nothing -> return ()
  else return ()

iterateBidirectional :: BidirectionalIterator -> IO ()
iterateBidirectional iterator = do
  putStrLn "正向遍历:"
  iterateForward iterator
  putStrLn "反向遍历:"
  iterateBackward iterator

iterateForward :: BidirectionalIterator -> IO ()
iterateForward iterator = 
  if hasNext iterator
  then do
    case next iterator of
      Just (item, nextIterator) -> do
        putStrLn $ "正向: " ++ item
        iterateForward nextIterator
      Nothing -> return ()
  else return ()

iterateBackward :: BidirectionalIterator -> IO ()
iterateBackward iterator = 
  if hasPrevious iterator
  then do
    case previous iterator of
      Just (item, nextIterator) -> do
        putStrLn $ "反向: " ++ item
        iterateBackward nextIterator
      Nothing -> return ()
  else return ()

iterateRandomAccess :: RandomAccessIterator -> IO ()
iterateRandomAccess iterator = do
  putStrLn $ "总大小: " ++ show (getSize iterator)
  putStrLn $ "当前索引: " ++ show (getIndex iterator)
  
  -- 跳转到索引2
  let seekIterator = seek iterator 2
  putStrLn $ "跳转到索引2后: " ++ show (getIndex seekIterator)
  
  case current seekIterator of
    Just item -> putStrLn $ "当前项: " ++ item
    Nothing -> putStrLn "无当前项"
```

### 3.2 Rust实现

```rust
use std::collections::HashMap;

// 迭代器类型
#[derive(Debug, Clone, PartialEq)]
enum IteratorType {
    Forward,
    Bidirectional,
    RandomAccess,
}

// 迭代器trait
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
    fn has_next(&self) -> bool;
    fn current(&self) -> Option<Self::Item>;
    fn reset(&mut self);
    fn get_type(&self) -> IteratorType;
}

// 双向迭代器trait
trait BidirectionalIterator: Iterator {
    fn previous(&mut self) -> Option<Self::Item>;
    fn has_previous(&self) -> bool;
}

// 随机访问迭代器trait
trait RandomAccessIterator: Iterator {
    fn seek(&mut self, index: usize);
    fn get_index(&self) -> usize;
    fn get_size(&self) -> usize;
}

// 聚合trait
trait Aggregate {
    type IteratorType: Iterator;
    fn create_iterator(&self) -> Self::IteratorType;
    fn size(&self) -> usize;
    fn is_empty(&self) -> bool;
}

// 具体聚合
#[derive(Debug)]
struct ConcreteAggregate {
    items: Vec<String>,
    metadata: HashMap<String, String>,
}

impl ConcreteAggregate {
    fn new() -> Self {
        ConcreteAggregate {
            items: Vec::new(),
            metadata: HashMap::new(),
        }
    }
    
    fn add_item(&mut self, item: String) {
        self.items.push(item);
    }
    
    fn remove_item(&mut self, item: &str) {
        self.items.retain(|x| x != item);
    }
}

impl Aggregate for ConcreteAggregate {
    type IteratorType = ConcreteIterator;
    
    fn create_iterator(&self) -> Self::IteratorType {
        ConcreteIterator {
            items: self.items.clone(),
            current_index: 0,
            iterator_type: IteratorType::Forward,
        }
    }
    
    fn size(&self) -> usize {
        self.items.len()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// 具体迭代器
#[derive(Debug)]
struct ConcreteIterator {
    items: Vec<String>,
    current_index: usize,
    iterator_type: IteratorType,
}

impl Iterator for ConcreteIterator {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index < self.items.len() {
            let item = self.items[self.current_index].clone();
            self.current_index += 1;
            Some(item)
        } else {
            None
        }
    }
    
    fn has_next(&self) -> bool {
        self.current_index < self.items.len()
    }
    
    fn current(&self) -> Option<Self::Item> {
        if self.current_index < self.items.len() {
            Some(self.items[self.current_index].clone())
        } else {
            None
        }
    }
    
    fn reset(&mut self) {
        self.current_index = 0;
    }
    
    fn get_type(&self) -> IteratorType {
        self.iterator_type.clone()
    }
}

// 双向迭代器
#[derive(Debug)]
struct BidirectionalIterator {
    items: Vec<String>,
    current_index: usize,
    direction: Direction,
}

#[derive(Debug, Clone)]
enum Direction {
    Forward,
    Backward,
}

impl Iterator for BidirectionalIterator {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        match self.direction {
            Direction::Forward => {
                if self.current_index < self.items.len() {
                    let item = self.items[self.current_index].clone();
                    self.current_index += 1;
                    Some(item)
                } else {
                    None
                }
            }
            Direction::Backward => {
                if self.current_index > 0 {
                    let item = self.items[self.current_index - 1].clone();
                    self.current_index -= 1;
                    Some(item)
                } else {
                    None
                }
            }
        }
    }
    
    fn has_next(&self) -> bool {
        match self.direction {
            Direction::Forward => self.current_index < self.items.len(),
            Direction::Backward => self.current_index > 0,
        }
    }
    
    fn current(&self) -> Option<Self::Item> {
        if self.current_index < self.items.len() {
            Some(self.items[self.current_index].clone())
        } else {
            None
        }
    }
    
    fn reset(&mut self) {
        self.current_index = 0;
        self.direction = Direction::Forward;
    }
    
    fn get_type(&self) -> IteratorType {
        IteratorType::Bidirectional
    }
}

impl BidirectionalIterator for BidirectionalIterator {
    fn previous(&mut self) -> Option<Self::Item> {
        match self.direction {
            Direction::Forward => {
                if self.current_index > 0 {
                    let item = self.items[self.current_index - 1].clone();
                    self.current_index -= 1;
                    Some(item)
                } else {
                    None
                }
            }
            Direction::Backward => {
                if self.current_index < self.items.len() - 1 {
                    let item = self.items[self.current_index + 1].clone();
                    self.current_index += 1;
                    Some(item)
                } else {
                    None
                }
            }
        }
    }
    
    fn has_previous(&self) -> bool {
        match self.direction {
            Direction::Forward => self.current_index > 0,
            Direction::Backward => self.current_index < self.items.len() - 1,
        }
    }
}

// 随机访问迭代器
#[derive(Debug)]
struct RandomAccessIterator {
    items: Vec<String>,
    current_index: usize,
}

impl Iterator for RandomAccessIterator {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index < self.items.len() {
            let item = self.items[self.current_index].clone();
            self.current_index += 1;
            Some(item)
        } else {
            None
        }
    }
    
    fn has_next(&self) -> bool {
        self.current_index < self.items.len()
    }
    
    fn current(&self) -> Option<Self::Item> {
        if self.current_index < self.items.len() {
            Some(self.items[self.current_index].clone())
        } else {
            None
        }
    }
    
    fn reset(&mut self) {
        self.current_index = 0;
    }
    
    fn get_type(&self) -> IteratorType {
        IteratorType::RandomAccess
    }
}

impl RandomAccessIterator for RandomAccessIterator {
    fn seek(&mut self, index: usize) {
        self.current_index = index.min(self.items.len());
    }
    
    fn get_index(&self) -> usize {
        self.current_index
    }
    
    fn get_size(&self) -> usize {
        self.items.len()
    }
}

// 过滤迭代器
#[derive(Debug)]
struct FilterIterator<I> {
    base_iterator: I,
    predicate: Box<dyn Fn(&String) -> bool>,
}

impl<I: Iterator<Item = String>> Iterator for FilterIterator<I> {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.base_iterator.next() {
            if (self.predicate)(&item) {
                return Some(item);
            }
        }
        None
    }
    
    fn has_next(&self) -> bool {
        // 简化实现，实际需要检查下一个元素
        true
    }
    
    fn current(&self) -> Option<Self::Item> {
        self.base_iterator.current()
    }
    
    fn reset(&mut self) {
        self.base_iterator.reset();
    }
    
    fn get_type(&self) -> IteratorType {
        IteratorType::Forward
    }
}

// 映射迭代器
#[derive(Debug)]
struct MapIterator<I> {
    base_iterator: I,
    mapper: Box<dyn Fn(String) -> String>,
}

impl<I: Iterator<Item = String>> Iterator for MapIterator<I> {
    type Item = String;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.base_iterator.next().map(|item| (self.mapper)(item))
    }
    
    fn has_next(&self) -> bool {
        self.base_iterator.has_next()
    }
    
    fn current(&self) -> Option<Self::Item> {
        self.base_iterator.current().map(|item| (self.mapper)(item))
    }
    
    fn reset(&mut self) {
        self.base_iterator.reset();
    }
    
    fn get_type(&self) -> IteratorType {
        IteratorType::Forward
    }
}

// 使用示例
fn main() {
    // 创建聚合对象
    let mut aggregate = ConcreteAggregate::new();
    aggregate.add_item("Item1".to_string());
    aggregate.add_item("Item2".to_string());
    aggregate.add_item("Item3".to_string());
    aggregate.add_item("Item4".to_string());
    
    println!("迭代器模式示例:");
    
    // 基本迭代器
    let mut iterator = aggregate.create_iterator();
    println!("\n基本迭代器执行:");
    iterate_with_iterator(&mut iterator);
    
    // 双向迭代器
    let mut bidirectional_iterator = BidirectionalIterator {
        items: vec!["Item1".to_string(), "Item2".to_string(), "Item3".to_string()],
        current_index: 0,
        direction: Direction::Forward,
    };
    println!("\n双向迭代器执行:");
    iterate_bidirectional(&mut bidirectional_iterator);
    
    // 随机访问迭代器
    let mut random_iterator = RandomAccessIterator {
        items: vec!["Item1".to_string(), "Item2".to_string(), "Item3".to_string()],
        current_index: 0,
    };
    println!("\n随机访问迭代器执行:");
    iterate_random_access(&mut random_iterator);
    
    // 过滤迭代器
    let filter_iterator = FilterIterator {
        base_iterator: aggregate.create_iterator(),
        predicate: Box::new(|item| item.len() > 4),
    };
    println!("\n过滤迭代器执行 (长度>4):");
    // iterate_with_iterator(&mut filter_iterator);
    
    // 映射迭代器
    let map_iterator = MapIterator {
        base_iterator: aggregate.create_iterator(),
        mapper: Box::new(|item| format!("Processed: {}", item)),
    };
    println!("\n映射迭代器执行:");
    // iterate_with_iterator(&mut map_iterator);
}

// 辅助函数
fn iterate_with_iterator<I: Iterator<Item = String>>(iterator: &mut I) {
    while iterator.has_next() {
        if let Some(item) = iterator.next() {
            println!("当前项: {}", item);
        }
    }
}

fn iterate_bidirectional(iterator: &mut BidirectionalIterator) {
    println!("正向遍历:");
    iterate_forward(iterator);
    println!("反向遍历:");
    iterate_backward(iterator);
}

fn iterate_forward(iterator: &mut BidirectionalIterator) {
    while iterator.has_next() {
        if let Some(item) = iterator.next() {
            println!("正向: {}", item);
        }
    }
}

fn iterate_backward(iterator: &mut BidirectionalIterator) {
    while iterator.has_previous() {
        if let Some(item) = iterator.previous() {
            println!("反向: {}", item);
        }
    }
}

fn iterate_random_access(iterator: &mut RandomAccessIterator) {
    println!("总大小: {}", iterator.get_size());
    println!("当前索引: {}", iterator.get_index());
    
    // 跳转到索引2
    iterator.seek(2);
    println!("跳转到索引2后: {}", iterator.get_index());
    
    if let Some(item) = iterator.current() {
        println!("当前项: {}", item);
    } else {
        println!("无当前项");
    }
}
```

### 3.3 Lean实现

```lean
-- 迭代器类型
inductive IteratorType where
  | Forward : IteratorType
  | Bidirectional : IteratorType
  | RandomAccess : IteratorType

-- 迭代器类型类
class Iterator (α : Type) where
  next : α → Option (String × α)
  hasNext : α → Bool
  current : α → Option String
  reset : α → α
  getType : α → IteratorType

-- 双向迭代器类型类
class (Iterator α) => BidirectionalIterator (α : Type) where
  previous : α → Option (String × α)
  hasPrevious : α → Bool

-- 随机访问迭代器类型类
class (Iterator α) => RandomAccessIterator (α : Type) where
  seek : α → Nat → α
  getIndex : α → Nat
  getSize : α → Nat

-- 聚合类型类
class Aggregate (α : Type) where
  createIterator : α → Iterator
  size : α → Nat
  isEmpty : α → Bool

-- 具体聚合
structure ConcreteAggregate where
  items : List String
  metadata : List (String × String)

def newAggregate : ConcreteAggregate := { 
  items := [], 
  metadata := [] 
}

def addItem (agg : ConcreteAggregate) (item : String) : ConcreteAggregate :=
  { agg with items := item :: agg.items }

def removeItem (agg : ConcreteAggregate) (item : String) : ConcreteAggregate :=
  { agg with items := agg.items.filter (fun x => x ≠ item) }

instance : Aggregate ConcreteAggregate where
  createIterator agg := ConcreteIterator.mk agg.items 0 IteratorType.Forward
  size agg := agg.items.length
  isEmpty agg := agg.items.isEmpty

-- 具体迭代器
structure ConcreteIterator where
  items : List String
  currentIndex : Nat
  iteratorType : IteratorType

instance : Iterator ConcreteIterator where
  next iterator := match iterator.items with
    | [] => none
    | x :: xs => some (x, { iterator with items := xs, currentIndex := iterator.currentIndex + 1 })
  
  hasNext iterator := not iterator.items.isEmpty
  
  current iterator := match iterator.items with
    | [] => none
    | x :: _ => some x
  
  reset iterator := { iterator with currentIndex := 0 }
  
  getType iterator := iterator.iteratorType

-- 双向迭代器
structure BidirectionalIterator where
  items : List String
  currentIndex : Nat
  direction : Direction

inductive Direction where
  | Forward : Direction
  | Backward : Direction

instance : Iterator BidirectionalIterator where
  next iterator := match iterator.direction with
    | Direction.Forward => match iterator.items with
      | [] => none
      | x :: xs => some (x, { iterator with items := xs, currentIndex := iterator.currentIndex + 1 })
    | Direction.Backward => if iterator.currentIndex > 0
      then some (iterator.items.get! (iterator.currentIndex - 1), { iterator with currentIndex := iterator.currentIndex - 1 })
      else none
  
  hasNext iterator := match iterator.direction with
    | Direction.Forward => not iterator.items.isEmpty
    | Direction.Backward => iterator.currentIndex > 0
  
  current iterator := if iterator.currentIndex < iterator.items.length
    then some (iterator.items.get! iterator.currentIndex)
    else none
  
  reset iterator := { iterator with currentIndex := 0, direction := Direction.Forward }
  
  getType _ := IteratorType.Bidirectional

instance : BidirectionalIterator BidirectionalIterator where
  previous iterator := match iterator.direction with
    | Direction.Forward => if iterator.currentIndex > 0
      then some (iterator.items.get! (iterator.currentIndex - 1), { iterator with currentIndex := iterator.currentIndex - 1 })
      else none
    | Direction.Backward => if iterator.currentIndex < iterator.items.length - 1
      then some (iterator.items.get! (iterator.currentIndex + 1), { iterator with currentIndex := iterator.currentIndex + 1 })
      else none
  
  hasPrevious iterator := match iterator.direction with
    | Direction.Forward => iterator.currentIndex > 0
    | Direction.Backward => iterator.currentIndex < iterator.items.length - 1

-- 随机访问迭代器
structure RandomAccessIterator where
  items : List String
  currentIndex : Nat

instance : Iterator RandomAccessIterator where
  next iterator := if iterator.currentIndex < iterator.items.length
    then some (iterator.items.get! iterator.currentIndex, { iterator with currentIndex := iterator.currentIndex + 1 })
    else none
  
  hasNext iterator := iterator.currentIndex < iterator.items.length
  
  current iterator := if iterator.currentIndex < iterator.items.length
    then some (iterator.items.get! iterator.currentIndex)
    else none
  
  reset iterator := { iterator with currentIndex := 0 }
  
  getType _ := IteratorType.RandomAccess

instance : RandomAccessIterator RandomAccessIterator where
  seek iterator newIndex := { 
    iterator with currentIndex := max 0 (min newIndex (iterator.items.length - 1)) 
  }
  
  getIndex iterator := iterator.currentIndex
  
  getSize iterator := iterator.items.length

-- 过滤迭代器
structure FilterIterator where
  baseIterator : ConcreteIterator
  predicate : String → Bool

instance : Iterator FilterIterator where
  next iterator := match next iterator.baseIterator with
    | some (item, nextIterator) => 
      if iterator.predicate item
      then some (item, { iterator with baseIterator := nextIterator })
      then some (item, { iterator with baseIterator := nextIterator })
    | none => none
  
  hasNext iterator := match next iterator.baseIterator with
    | some (item, _) => iterator.predicate item || hasNext { iterator with baseIterator := iterator.baseIterator }
    | none => false
  
  current iterator := match current iterator.baseIterator with
    | some item => if iterator.predicate item then some item else none
    | none => none
  
  reset iterator := { iterator with baseIterator := reset iterator.baseIterator }
  
  getType _ := IteratorType.Forward

-- 映射迭代器
structure MapIterator where
  baseIterator : ConcreteIterator
  mapper : String → String

instance : Iterator MapIterator where
  next iterator := match next iterator.baseIterator with
    | some (item, nextIterator) => 
      some (iterator.mapper item, { iterator with baseIterator := nextIterator })
    | none => none
  
  hasNext iterator := hasNext iterator.baseIterator
  
  current iterator := match current iterator.baseIterator with
    | some item => some (iterator.mapper item)
    | none => none
  
  reset iterator := { iterator with baseIterator := reset iterator.baseIterator }
  
  getType _ := IteratorType.Forward

-- 使用示例
def main : IO Unit := do
  let aggregate := addItem (addItem (addItem newAggregate "Item1") "Item2") "Item3"
  
  IO.println "迭代器模式示例:"
  
  let iterator := createIterator aggregate
  IO.println "\n基本迭代器执行:"
  iterateWithIterator iterator
  
  let bidirectionalIterator := BidirectionalIterator.mk (items aggregate) 0 Direction.Forward
  IO.println "\n双向迭代器执行:"
  iterateBidirectional bidirectionalIterator
  
  let randomIterator := RandomAccessIterator.mk (items aggregate) 0
  IO.println "\n随机访问迭代器执行:"
  iterateRandomAccess randomIterator

-- 辅助函数
def iterateWithIterator (iterator : ConcreteIterator) : IO Unit := do
  if hasNext iterator
  then do
    match next iterator with
    | some (item, nextIterator) => do
      IO.println ("当前项: " ++ item)
      iterateWithIterator nextIterator
    | none => return ()
  else return ()

def iterateBidirectional (iterator : BidirectionalIterator) : IO Unit := do
  IO.println "正向遍历:"
  iterateForward iterator
  IO.println "反向遍历:"
  iterateBackward iterator

def iterateForward (iterator : BidirectionalIterator) : IO Unit := do
  if hasNext iterator
  then do
    match next iterator with
    | some (item, nextIterator) => do
      IO.println ("正向: " ++ item)
      iterateForward nextIterator
    | none => return ()
  else return ()

def iterateBackward (iterator : BidirectionalIterator) : IO Unit := do
  if hasPrevious iterator
  then do
    match previous iterator with
    | some (item, nextIterator) => do
      IO.println ("反向: " ++ item)
      iterateBackward nextIterator
    | none => return ()
  else return ()

def iterateRandomAccess (iterator : RandomAccessIterator) : IO Unit := do
  IO.println ("总大小: " ++ toString (getSize iterator))
  IO.println ("当前索引: " ++ toString (getIndex iterator))
  
  let seekIterator := seek iterator 2
  IO.println ("跳转到索引2后: " ++ toString (getIndex seekIterator))
  
  match current seekIterator with
  | some item => IO.println ("当前项: " ++ item)
  | none => IO.println "无当前项"
```

## 4. 工程实践

### 4.1 设计考虑

- **性能优化**: 避免不必要的对象创建
- **内存管理**: 正确处理迭代器生命周期
- **并发安全**: 支持多线程环境下的迭代
- **错误处理**: 处理迭代过程中的异常

### 4.2 实现模式

```haskell
-- 带缓存的迭代器
data CachedIterator a = CachedIterator {
  iterator :: a,
  cache :: MVar (Map Int String)
}

-- 异步迭代器
data AsyncIterator = AsyncIterator {
  iterator :: Iterator,
  executor :: ThreadPool
}

-- 带监控的迭代器
data MonitoredIterator a = MonitoredIterator {
  iterator :: a,
  metrics :: MVar IteratorMetrics
}
```

### 4.3 错误处理

```haskell
-- 错误类型
data IteratorError = 
  IteratorExhausted
  | InvalidIndex Int
  | ConcurrentModification
  | IteratorClosed

-- 安全迭代
safeIterate :: Iterator a => a -> IO (Either IteratorError [String])
safeIterate iterator = 
  try (iterateAll iterator) >>= \case
    Left e -> return $ Left $ IteratorExhausted
    Right result -> return $ Right result
```

## 5. 性能优化

### 5.1 缓存策略

- **迭代结果缓存**: 缓存迭代结果避免重复计算
- **索引缓存**: 缓存索引信息提高访问速度
- **预取机制**: 预取下一个元素减少延迟

### 5.2 迭代优化

```haskell
-- 优化的迭代器
data OptimizedIterator a = OptimizedIterator {
  iterator :: a,
  optimizations :: Map String String
}

-- 并行迭代
data ParallelIterator = ParallelIterator {
  iterators :: [Iterator],
  executor :: ThreadPool
}

executeParallel :: ParallelIterator -> IO [[String]]
executeParallel iterator = 
  mapConcurrently iterateAll (iterators iterator)
```

### 5.3 内存优化

```haskell
-- 流式迭代器
data StreamingIterator = StreamingIterator {
  iterator :: Iterator,
  buffer :: StreamBuffer
}

-- 延迟迭代器
data LazyIterator = LazyIterator {
  iterator :: Iterator,
  generator :: LazyGenerator
}
```

## 6. 应用场景

### 6.1 集合遍历

```haskell
-- 集合迭代器
data CollectionIterator = CollectionIterator {
  collection :: Collection,
  traversalStrategy :: TraversalStrategy
}

-- 遍历策略
data TraversalStrategy = 
  DepthFirst
  | BreadthFirst
  | InOrder
  | PostOrder

-- 集合遍历
traverseCollection :: CollectionIterator -> IO [String]
traverseCollection iterator = do
  -- 1. 初始化遍历
  initializeTraversal iterator
  -- 2. 执行遍历
  results <- executeTraversal iterator
  -- 3. 清理资源
  cleanupTraversal iterator
  return results
```

### 6.2 数据库查询结果遍历

```haskell
-- 数据库迭代器
data DatabaseIterator = DatabaseIterator {
  query :: DatabaseQuery,
  connection :: DatabaseConnection,
  cursor :: DatabaseCursor
}

-- 查询结果遍历
traverseQueryResults :: DatabaseIterator -> IO [DatabaseRow]
traverseQueryResults iterator = do
  -- 1. 执行查询
  executeQuery (query iterator) (connection iterator)
  -- 2. 获取游标
  cursor <- getCursor (connection iterator)
  -- 3. 遍历结果
  results <- iterateCursor cursor
  return results
```

### 6.3 文件系统遍历

```haskell
-- 文件系统迭代器
data FileSystemIterator = FileSystemIterator {
  rootPath :: FilePath,
  traversalMode :: TraversalMode,
  filterPattern :: FilePattern
}

-- 遍历模式
data TraversalMode = 
  Recursive
  | NonRecursive
  | SymlinkFollow
  | SymlinkSkip

-- 文件系统遍历
traverseFileSystem :: FileSystemIterator -> IO [FilePath]
traverseFileSystem iterator = do
  -- 1. 验证路径
  validatePath (rootPath iterator)
  -- 2. 开始遍历
  startTraversal iterator
  -- 3. 收集文件
  files <- collectFiles iterator
  -- 4. 应用过滤
  filteredFiles <- applyFilter (filterPattern iterator) files
  return filteredFiles
```

### 6.4 网络数据流处理

```haskell
-- 网络流迭代器
data NetworkStreamIterator = NetworkStreamIterator {
  stream :: NetworkStream,
  bufferSize :: Int,
  timeout :: Timeout
}

-- 网络流处理
processNetworkStream :: NetworkStreamIterator -> IO [DataPacket]
processNetworkStream iterator = do
  -- 1. 建立连接
  establishConnection (stream iterator)
  -- 2. 设置缓冲区
  setupBuffer (bufferSize iterator)
  -- 3. 处理数据流
  packets <- processStream (stream iterator)
  -- 4. 关闭连接
  closeConnection (stream iterator)
  return packets
```

## 7. 最佳实践

### 7.1 设计原则

- **保持迭代器简单**: 避免复杂的迭代逻辑
- **支持多种遍历**: 提供不同的遍历策略
- **性能考虑**: 考虑迭代器的性能影响
- **资源管理**: 正确管理迭代器资源

### 7.2 实现建议

```haskell
-- 迭代器工厂
class IteratorFactory a where
  createIterator :: String -> Maybe a
  listIterators :: [String]
  validateIterator :: a -> Bool

-- 迭代器注册表
data IteratorRegistry = IteratorRegistry {
  iterators :: Map String (forall a. Iterator a => a),
  metadata :: Map String String
}

-- 线程安全迭代器管理器
data ThreadSafeIteratorManager = ThreadSafeIteratorManager {
  manager :: MVar IteratorManager,
  lock :: MVar ()
}
```

### 7.3 测试策略

```haskell
-- 迭代器测试
testIterator :: Iterator a => a -> Bool
testIterator iterator = 
  let result = iterateAll iterator
  in not (null result) && isValidResult result

-- 性能测试
benchmarkIterator :: Iterator a => a -> IO Double
benchmarkIterator iterator = do
  start <- getCurrentTime
  replicateM_ 1000 $ iterateAll iterator
  end <- getCurrentTime
  return $ diffUTCTime end start
```

### 7.4 扩展性考虑

- **插件系统**: 支持动态加载新的迭代器类型
- **序列化**: 支持迭代器状态的序列化和反序列化
- **版本控制**: 支持迭代器接口的版本管理
- **分布式**: 支持跨网络的迭代器执行

## 8. 总结

迭代器模式是遍历聚合对象的强大工具，通过将遍历逻辑从聚合对象中分离提供了良好的封装性和扩展性。在实现时需要注意迭代器的性能优化、资源管理和并发安全性。该模式在集合遍历、数据库查询、文件系统遍历、网络流处理等场景中都有广泛应用。
