# 管道模式（Pipeline Pattern）

## 概述
管道模式是一种并行设计模式，将复杂任务分解为一系列独立的处理阶段，数据在阶段间流动，每个阶段可以并行处理不同的数据项。

## 理论基础
- **阶段分解**：将任务分解为独立处理阶段
- **数据流**：数据在阶段间顺序流动
- **并行处理**：不同阶段可以并行执行

## Rust实现示例
```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

// 管道阶段特征
trait PipelineStage<T, U> {
    fn process(&self, input: T) -> U;
}

// 管道框架
struct Pipeline<T, U, V> {
    stage1: Box<dyn PipelineStage<T, U> + Send>,
    stage2: Box<dyn PipelineStage<U, V> + Send>,
}

impl<T, U, V> Pipeline<T, U, V>
where
    T: Send + 'static,
    U: Send + 'static,
    V: Send + 'static,
{
    fn new(
        stage1: Box<dyn PipelineStage<T, U> + Send>,
        stage2: Box<dyn PipelineStage<U, V> + Send>,
    ) -> Self {
        Self { stage1, stage2 }
    }
    
    fn execute(&self, inputs: Vec<T>) -> Vec<V> {
        let (tx1, rx1) = mpsc::channel();
        let (tx2, rx2) = mpsc::channel();
        
        // 启动第一阶段
        let stage1 = self.stage1.clone();
        let handle1 = thread::spawn(move || {
            for input in inputs {
                let output = stage1.process(input);
                tx1.send(output).unwrap();
            }
        });
        
        // 启动第二阶段
        let stage2 = self.stage2.clone();
        let handle2 = thread::spawn(move || {
            for input in rx1 {
                let output = stage2.process(input);
                tx2.send(output).unwrap();
            }
        });
        
        // 收集结果
        let mut results = Vec::new();
        for result in rx2 {
            results.push(result);
        }
        
        handle1.join().unwrap();
        handle2.join().unwrap();
        
        results
    }
}

// 具体处理阶段
struct DataFilter;
impl PipelineStage<i32, i32> for DataFilter {
    fn process(&self, input: i32) -> i32 {
        if input > 0 {
            input * 2
        } else {
            0
        }
    }
}

struct DataTransformer;
impl PipelineStage<i32, String> for DataTransformer {
    fn process(&self, input: i32) -> String {
        format!("处理结果: {}", input)
    }
}

// 多阶段管道
struct MultiStagePipeline<T> {
    stages: Vec<Box<dyn PipelineStage<T, T> + Send>>,
}

impl<T> MultiStagePipeline<T>
where
    T: Send + Clone + 'static,
{
    fn new() -> Self {
        Self { stages: Vec::new() }
    }
    
    fn add_stage(&mut self, stage: Box<dyn PipelineStage<T, T> + Send>) {
        self.stages.push(stage);
    }
    
    fn execute(&self, inputs: Vec<T>) -> Vec<T> {
        let mut current_data = inputs;
        
        for stage in &self.stages {
            let (tx, rx) = mpsc::channel();
            let stage_clone = stage.clone();
            
            let handle = thread::spawn(move || {
                for input in current_data {
                    let output = stage_clone.process(input);
                    tx.send(output).unwrap();
                }
            });
            
            current_data = rx.into_iter().collect();
            handle.join().unwrap();
        }
        
        current_data
    }
}

// 并行管道
struct ParallelPipeline<T, U> {
    stage: Box<dyn PipelineStage<T, U> + Send + Sync>,
    num_workers: usize,
}

impl<T, U> ParallelPipeline<T, U>
where
    T: Send + Clone + 'static,
    U: Send + 'static,
{
    fn new(stage: Box<dyn PipelineStage<T, U> + Send + Sync>, num_workers: usize) -> Self {
        Self { stage, num_workers }
    }
    
    fn execute(&self, inputs: Vec<T>) -> Vec<U> {
        let chunk_size = (inputs.len() + self.num_workers - 1) / self.num_workers;
        let chunks: Vec<Vec<T>> = inputs
            .chunks(chunk_size)
            .map(|chunk| chunk.to_vec())
            .collect();
        
        let mut handles = Vec::new();
        let (tx, rx) = mpsc::channel();
        
        for chunk in chunks {
            let stage = self.stage.clone();
            let tx_clone = tx.clone();
            
            let handle = thread::spawn(move || {
                for input in chunk {
                    let output = stage.process(input);
                    tx_clone.send(output).unwrap();
                }
            });
            
            handles.push(handle);
        }
        
        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }
        
        rx.into_iter().collect()
    }
}

fn main() {
    // 基本管道示例
    let pipeline = Pipeline::new(
        Box::new(DataFilter),
        Box::new(DataTransformer),
    );
    
    let inputs = vec![1, -2, 3, -4, 5];
    let results = pipeline.execute(inputs);
    
    for result in results {
        println!("{}", result);
    }
    
    // 多阶段管道示例
    let mut multi_pipeline = MultiStagePipeline::new();
    multi_pipeline.add_stage(Box::new(DataFilter));
    multi_pipeline.add_stage(Box::new(DataFilter));
    
    let inputs = vec![1, 2, 3, 4, 5];
    let results = multi_pipeline.execute(inputs);
    
    println!("多阶段结果: {:?}", results);
    
    // 并行管道示例
    let parallel_pipeline = ParallelPipeline::new(
        Box::new(DataFilter),
        4, // 4个工作线程
    );
    
    let large_inputs: Vec<i32> = (1..1000).collect();
    let parallel_results = parallel_pipeline.execute(large_inputs);
    
    println!("并行处理完成，结果数量: {}", parallel_results.len());
}
```

## Haskell实现示例
```haskell
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import Data.List

-- 管道阶段类型
type PipelineStage a b = a -> b

-- 管道框架
data Pipeline a b c = Pipeline
    { stage1 :: PipelineStage a b
    , stage2 :: PipelineStage b c
    }

-- 执行管道
executePipeline :: Pipeline a b c -> [a] -> [c]
executePipeline pipeline inputs = 
    let
        stage1Results = map (stage1 pipeline) inputs
        stage2Results = map (stage2 pipeline) stage1Results
    in stage2Results

-- 具体处理阶段
dataFilter :: PipelineStage Int Int
dataFilter input = if input > 0 then input * 2 else 0

dataTransformer :: PipelineStage Int String
dataTransformer input = "处理结果: " ++ show input

-- 多阶段管道
data MultiStagePipeline a = MultiStagePipeline [PipelineStage a a]

newMultiStagePipeline :: MultiStagePipeline a
newMultiStagePipeline = MultiStagePipeline []

addStage :: MultiStagePipeline a -> PipelineStage a a -> MultiStagePipeline a
addStage (MultiStagePipeline stages) stage = MultiStagePipeline (stages ++ [stage])

executeMultiStage :: MultiStagePipeline a -> [a] -> [a]
executeMultiStage (MultiStagePipeline stages) inputs = 
    foldl (\data stage -> map stage data) inputs stages

-- 并行管道
data ParallelPipeline a b = ParallelPipeline
    { stage :: PipelineStage a b
    , numWorkers :: Int
    }

executeParallelPipeline :: ParallelPipeline a b -> [a] -> IO [b]
executeParallelPipeline (ParallelPipeline stage numWorkers) inputs = do
    let chunkSize = (length inputs + numWorkers - 1) `div` numWorkers
    let chunks = chunksOf chunkSize inputs
    
    -- 并行处理每个分片
    results <- mapM (processChunk stage) chunks
    return $ concat results

processChunk :: PipelineStage a b -> [a] -> IO [b]
processChunk stage chunk = do
    return $ map stage chunk

-- 辅助函数
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

-- 测试函数
testBasicPipeline :: IO ()
testBasicPipeline = do
    let pipeline = Pipeline dataFilter dataTransformer
    let inputs = [1, -2, 3, -4, 5]
    let results = executePipeline pipeline inputs
    mapM_ putStrLn results

testMultiStagePipeline :: IO ()
testMultiStagePipeline = do
    let pipeline = addStage (addStage newMultiStagePipeline dataFilter) dataFilter
    let inputs = [1, 2, 3, 4, 5]
    let results = executeMultiStage pipeline inputs
    putStrLn $ "多阶段结果: " ++ show results

testParallelPipeline :: IO ()
testParallelPipeline = do
    let pipeline = ParallelPipeline dataFilter 4
    let largeInputs = [1..1000]
    results <- executeParallelPipeline pipeline largeInputs
    putStrLn $ "并行处理完成，结果数量: " ++ show (length results)

main :: IO ()
main = do
    testBasicPipeline
    testMultiStagePipeline
    testParallelPipeline
```

## Lean实现思路
```lean
-- 管道阶段类型
def PipelineStage (α β : Type) := α → β

-- 管道框架
structure Pipeline (α β γ : Type) where
  stage1 : PipelineStage α β
  stage2 : PipelineStage β γ

-- 执行管道
def executePipeline (pipeline : Pipeline α β γ) (inputs : List α) : List γ :=
  let stage1Results := inputs.map pipeline.stage1
  let stage2Results := stage1Results.map pipeline.stage2
  stage2Results

-- 具体处理阶段
def dataFilter : PipelineStage Nat Nat :=
  fun input => if input > 0 then input * 2 else 0

def dataTransformer : PipelineStage Nat String :=
  fun input => "处理结果: " ++ toString input

-- 多阶段管道
structure MultiStagePipeline (α : Type) where
  stages : List (PipelineStage α α)

def newMultiStagePipeline : MultiStagePipeline α :=
  { stages := [] }

def addStage (pipeline : MultiStagePipeline α) (stage : PipelineStage α α) : MultiStagePipeline α :=
  { pipeline with stages := pipeline.stages ++ [stage] }

def executeMultiStage (pipeline : MultiStagePipeline α) (inputs : List α) : List α :=
  pipeline.stages.foldl (fun data stage => data.map stage) inputs

-- 并行管道
structure ParallelPipeline (α β : Type) where
  stage : PipelineStage α β
  numWorkers : Nat

def executeParallelPipeline (pipeline : ParallelPipeline α β) (inputs : List α) : List β :=
  let chunkSize := (inputs.length + pipeline.numWorkers - 1) / pipeline.numWorkers
  let chunks := inputs.chunks chunkSize
  let processedChunks := chunks.map (fun chunk => chunk.map pipeline.stage)
  processedChunks.join
```

## 应用场景
- 数据处理流水线
- 图像处理管道
- 编译器优化
- 网络协议处理

## 最佳实践
- 合理划分处理阶段
- 平衡并行度和开销
- 实现错误处理
- 监控管道性能
