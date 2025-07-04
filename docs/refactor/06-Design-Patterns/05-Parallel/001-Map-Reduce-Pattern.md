# Map-Reduce模式（Map-Reduce Pattern）

## 概述
Map-Reduce模式是一种并行编程模式，将大规模数据处理分解为两个阶段：Map阶段将数据分解为键值对，Reduce阶段将相同键的值进行聚合处理。

## 理论基础
- **数据并行**：将数据分割到多个处理单元
- **函数式编程**：使用纯函数进行数据处理
- **容错性**：支持节点失败和数据重新分配

## Rust实现示例
```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use rayon::prelude::*;

// Map函数特征
trait MapFunction<T, K, V> {
    fn map(&self, item: T) -> Vec<(K, V)>;
}

// Reduce函数特征
trait ReduceFunction<K, V, R> {
    fn reduce(&self, key: K, values: Vec<V>) -> R;
}

// Map-Reduce框架
struct MapReduce<T, K, V, R> {
    map_fn: Box<dyn MapFunction<T, K, V> + Send + Sync>,
    reduce_fn: Box<dyn ReduceFunction<K, V, R> + Send + Sync>,
}

impl<T, K, V, R> MapReduce<T, K, V, R>
where
    T: Send + Sync,
    K: Send + Sync + Clone + Eq + std::hash::Hash,
    V: Send + Sync + Clone,
    R: Send + Sync,
{
    fn new(
        map_fn: Box<dyn MapFunction<T, K, V> + Send + Sync>,
        reduce_fn: Box<dyn ReduceFunction<K, V, R> + Send + Sync>,
    ) -> Self {
        Self { map_fn, reduce_fn }
    }
    
    fn execute(&self, data: Vec<T>) -> HashMap<K, R> {
        // Map阶段
        let mapped_data: Vec<(K, V)> = data
            .par_iter()
            .flat_map(|item| self.map_fn.map(item.clone()))
            .collect();
        
        // 按键分组
        let mut grouped_data: HashMap<K, Vec<V>> = HashMap::new();
        for (key, value) in mapped_data {
            grouped_data.entry(key).or_insert_with(Vec::new).push(value);
        }
        
        // Reduce阶段
        grouped_data
            .into_par_iter()
            .map(|(key, values)| {
                let result = self.reduce_fn.reduce(key.clone(), values);
                (key, result)
            })
            .collect()
    }
}

// 单词计数示例
struct WordCountMapper;

impl MapFunction<String, String, u32> for WordCountMapper {
    fn map(&self, line: String) -> Vec<(String, u32)> {
        line.split_whitespace()
            .map(|word| (word.to_lowercase(), 1))
            .collect()
    }
}

struct WordCountReducer;

impl ReduceFunction<String, u32, u32> for WordCountReducer {
    fn reduce(&self, _key: String, values: Vec<u32>) -> u32 {
        values.iter().sum()
    }
}

// 并行排序示例
struct SortMapper;

impl MapFunction<i32, i32, i32> for SortMapper {
    fn map(&self, item: i32) -> Vec<(i32, i32)> {
        vec![(item, item)]
    }
}

struct SortReducer;

impl ReduceFunction<i32, i32, Vec<i32>> for SortReducer {
    fn reduce(&self, _key: i32, values: Vec<i32>) -> Vec<i32> {
        let mut sorted_values = values;
        sorted_values.sort();
        sorted_values
    }
}

// 分布式Map-Reduce
struct DistributedMapReduce<T, K, V, R> {
    map_fn: Box<dyn MapFunction<T, K, V> + Send + Sync>,
    reduce_fn: Box<dyn ReduceFunction<K, V, R> + Send + Sync>,
    num_workers: usize,
}

impl<T, K, V, R> DistributedMapReduce<T, K, V, R>
where
    T: Send + Sync + Clone,
    K: Send + Sync + Clone + Eq + std::hash::Hash,
    V: Send + Sync + Clone,
    R: Send + Sync,
{
    fn new(
        map_fn: Box<dyn MapFunction<T, K, V> + Send + Sync>,
        reduce_fn: Box<dyn ReduceFunction<K, V, R> + Send + Sync>,
        num_workers: usize,
    ) -> Self {
        Self {
            map_fn,
            reduce_fn,
            num_workers,
        }
    }
    
    fn execute(&self, data: Vec<T>) -> HashMap<K, R> {
        // 数据分片
        let chunk_size = (data.len() + self.num_workers - 1) / self.num_workers;
        let chunks: Vec<Vec<T>> = data
            .chunks(chunk_size)
            .map(|chunk| chunk.to_vec())
            .collect();
        
        // 并行Map阶段
        let mapped_chunks: Vec<Vec<(K, V)>> = chunks
            .into_par_iter()
            .map(|chunk| {
                chunk
                    .iter()
                    .flat_map(|item| self.map_fn.map(item.clone()))
                    .collect()
            })
            .collect();
        
        // 合并所有Map结果
        let mut all_mapped: Vec<(K, V)> = Vec::new();
        for chunk in mapped_chunks {
            all_mapped.extend(chunk);
        }
        
        // 按键分组
        let mut grouped_data: HashMap<K, Vec<V>> = HashMap::new();
        for (key, value) in all_mapped {
            grouped_data.entry(key).or_insert_with(Vec::new).push(value);
        }
        
        // 并行Reduce阶段
        grouped_data
            .into_par_iter()
            .map(|(key, values)| {
                let result = self.reduce_fn.reduce(key.clone(), values);
                (key, result)
            })
            .collect()
    }
}

fn main() {
    // 单词计数示例
    let text_data = vec![
        "hello world".to_string(),
        "hello rust".to_string(),
        "world programming".to_string(),
        "rust programming".to_string(),
    ];
    
    let word_count = MapReduce::new(
        Box::new(WordCountMapper),
        Box::new(WordCountReducer),
    );
    
    let result = word_count.execute(text_data);
    println!("单词计数结果: {:?}", result);
    
    // 排序示例
    let numbers = vec![5, 2, 8, 1, 9, 3, 7, 4, 6];
    let sort_mr = MapReduce::new(
        Box::new(SortMapper),
        Box::new(SortReducer),
    );
    
    let sorted_result = sort_mr.execute(numbers);
    println!("排序结果: {:?}", sorted_result);
    
    // 分布式处理示例
    let large_data: Vec<i32> = (1..1000).collect();
    let distributed_mr = DistributedMapReduce::new(
        Box::new(SortMapper),
        Box::new(SortReducer),
        4, // 4个工作线程
    );
    
    let distributed_result = distributed_mr.execute(large_data);
    println!("分布式处理完成，结果数量: {}", distributed_result.len());
}
```

## Haskell实现示例
```haskell
import Control.Parallel
import Control.Parallel.Strategies
import Data.List
import qualified Data.Map as M

-- Map函数类型
type MapFunction a k v = a -> [(k, v)]

-- Reduce函数类型
type ReduceFunction k v r = k -> [v] -> r

-- Map-Reduce框架
data MapReduce a k v r = MapReduce
    { mapFn :: MapFunction a k v
    , reduceFn :: ReduceFunction k v r
    }

-- 执行Map-Reduce
executeMapReduce :: (Ord k) => MapReduce a k v r -> [a] -> M.Map k r
executeMapReduce mr data = 
    let
        -- Map阶段
        mappedData = concatMap (mapFn mr) data
        -- 按键分组
        groupedData = M.fromListWith (++) [(k, [v]) | (k, v) <- mappedData]
        -- Reduce阶段
        reducedData = M.mapWithKey (reduceFn mr) groupedData
    in reducedData

-- 并行执行Map-Reduce
executeParallelMapReduce :: (Ord k) => MapReduce a k v r -> [a] -> M.Map k r
executeParallelMapReduce mr data = 
    let
        -- 并行Map阶段
        mappedData = concatMap (mapFn mr) data `using` parList rdeepseq
        -- 按键分组
        groupedData = M.fromListWith (++) [(k, [v]) | (k, v) <- mappedData]
        -- 并行Reduce阶段
        reducedData = M.mapWithKey (reduceFn mr) groupedData `using` parMap rdeepseq
    in reducedData

-- 单词计数示例
wordCountMap :: MapFunction String String Int
wordCountMap line = [(word, 1) | word <- words (map toLower line)]

wordCountReduce :: ReduceFunction String Int Int
wordCountReduce _ values = sum values

wordCountMR :: MapReduce String String Int Int
wordCountMR = MapReduce wordCountMap wordCountReduce

-- 排序示例
sortMap :: MapFunction Int Int Int
sortMap item = [(item, item)]

sortReduce :: ReduceFunction Int Int [Int]
sortReduce _ values = sort values

sortMR :: MapReduce Int Int Int [Int]
sortMR = MapReduce sortMap sortReduce

-- 分布式Map-Reduce
data DistributedMapReduce a k v r = DistributedMapReduce
    { dmrMapFn :: MapFunction a k v
    , dmrReduceFn :: ReduceFunction k v r
    , numWorkers :: Int
    }

executeDistributedMR :: (Ord k) => DistributedMapReduce a k v r -> [a] -> M.Map k r
executeDistributedMR dmr data = 
    let
        -- 数据分片
        chunkSize = (length data + numWorkers dmr - 1) `div` numWorkers dmr
        chunks = chunksOf chunkSize data
        -- 并行处理每个分片
        mappedChunks = map (concatMap (dmrMapFn dmr)) chunks `using` parList rdeepseq
        -- 合并所有Map结果
        allMapped = concat mappedChunks
        -- 按键分组
        groupedData = M.fromListWith (++) [(k, [v]) | (k, v) <- allMapped]
        -- 并行Reduce
        reducedData = M.mapWithKey (dmrReduceFn dmr) groupedData `using` parMap rdeepseq
    in reducedData

-- 辅助函数
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

-- 测试函数
testWordCount :: IO ()
testWordCount = do
    let textData = ["hello world", "hello haskell", "world programming", "haskell programming"]
    let result = executeMapReduce wordCountMR textData
    putStrLn $ "单词计数结果: " ++ show result

testSort :: IO ()
testSort = do
    let numbers = [5, 2, 8, 1, 9, 3, 7, 4, 6]
    let result = executeMapReduce sortMR numbers
    putStrLn $ "排序结果: " ++ show result

testDistributed :: IO ()
testDistributed = do
    let largeData = [1..1000]
    let distributedMR = DistributedMapReduce wordCountMap wordCountReduce 4
    let result = executeDistributedMR distributedMR (map show largeData)
    putStrLn $ "分布式处理完成，结果数量: " ++ show (M.size result)

main :: IO ()
main = do
    testWordCount
    testSort
    testDistributed
```

## Lean实现思路
```lean
-- Map函数类型
def MapFunction (α κ ν : Type) := α → List (κ × ν)

-- Reduce函数类型
def ReduceFunction (κ ν ρ : Type) := κ → List ν → ρ

-- Map-Reduce框架
structure MapReduce (α κ ν ρ : Type) where
  mapFn : MapFunction α κ ν
  reduceFn : ReduceFunction κ ν ρ

-- 执行Map-Reduce
def executeMapReduce [Ord κ] (mr : MapReduce α κ ν ρ) (data : List α) : Map κ ρ :=
  let
    -- Map阶段
    mappedData := data.bind mr.mapFn
    -- 按键分组
    groupedData := mappedData.foldl (fun acc (k, v) => 
      acc.insert k (v :: acc.find? k |>.getD [])) Map.empty
    -- Reduce阶段
    reducedData := groupedData.map (fun k vs => (k, mr.reduceFn k vs))
  in Map.fromList reducedData

-- 单词计数示例
def wordCountMap : MapFunction String String Nat :=
  fun line => line.split " " |>.map (fun word => (word, 1))

def wordCountReduce : ReduceFunction String Nat Nat :=
  fun _ values => values.sum

def wordCountMR : MapReduce String String Nat Nat :=
  { mapFn := wordCountMap
  , reduceFn := wordCountReduce
  }

-- 排序示例
def sortMap : MapFunction Nat Nat Nat :=
  fun item => [(item, item)]

def sortReduce : ReduceFunction Nat Nat (List Nat) :=
  fun _ values => values.sort

def sortMR : MapReduce Nat Nat Nat (List Nat) :=
  { mapFn := sortMap
  , reduceFn := sortReduce
  }

-- 分布式Map-Reduce
structure DistributedMapReduce (α κ ν ρ : Type) where
  mapFn : MapFunction α κ ν
  reduceFn : ReduceFunction κ ν ρ
  numWorkers : Nat

def executeDistributedMR [Ord κ] (dmr : DistributedMapReduce α κ ν ρ) (data : List α) : Map κ ρ :=
  let
    -- 数据分片
    chunkSize := (data.length + dmr.numWorkers - 1) / dmr.numWorkers
    chunks := data.chunks chunkSize
    -- 并行处理每个分片
    mappedChunks := chunks.map (fun chunk => chunk.bind dmr.mapFn)
    -- 合并所有Map结果
    allMapped := mappedChunks.join
    -- 按键分组
    groupedData := allMapped.foldl (fun acc (k, v) => 
      acc.insert k (v :: acc.find? k |>.getD [])) Map.empty
    -- 并行Reduce
    reducedData := groupedData.map (fun k vs => (k, dmr.reduceFn k vs))
  in Map.fromList reducedData
```

## 应用场景
- 大数据处理
- 日志分析
- 搜索引擎
- 机器学习

## 最佳实践
- 合理选择分片大小
- 优化数据本地性
- 实现容错机制
- 监控处理进度 