# 科学计算

## 概述

科学计算是使用数学模型和量化分析技术解决科学和工程问题的学科。本文档探讨函数式编程在科学计算中的应用，特别是Haskell、Rust和Lean在数值计算、并行计算和科学数据处理中的优势。

## 数值计算基础

### 1. 高精度算术

```haskell
-- 高精度数值计算
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import qualified Data.Number.Fixed as Fixed
import qualified Data.Ratio as Ratio

-- 任意精度有理数
newtype HighPrecision = HighPrecision Rational
  deriving (Show, Eq, Ord, Num, Fractional)

-- 高精度常数
piHighPrecision :: HighPrecision
piHighPrecision = HighPrecision $ 
  fromIntegral (22) / fromIntegral (7) -- 简化示例

eHighPrecision :: HighPrecision  
eHighPrecision = HighPrecision $
  sum $ take 50 $ map (\n -> 1 / fromIntegral (factorial n)) [0..]
  where factorial n = product [1..n]

-- 区间算术
data Interval a = Interval a a deriving (Show, Eq)

instance (Num a, Ord a) => Num (Interval a) where
  Interval a b + Interval c d = Interval (a + c) (b + d)
  Interval a b - Interval c d = Interval (a - d) (b - c)
  Interval a b * Interval c d = 
    let products = [a*c, a*d, b*c, b*d]
    in Interval (minimum products) (maximum products)

-- 数值稳定性检查
numericalStability :: (Floating a, Ord a) => [a] -> a
numericalStability xs = 
  let mean = sum xs / fromIntegral (length xs)
      variance = sum (map (\x -> (x - mean)^2) xs) / fromIntegral (length xs)
      stdDev = sqrt variance
  in stdDev / abs mean  -- 变异系数
```

### 2. 线性代数

```rust
// 高性能线性代数运算
use nalgebra::{DMatrix, DVector, Matrix, Vector};
use rayon::prelude::*;

// 矩阵运算
pub struct Matrix<T> {
    data: Vec<T>,
    rows: usize,
    cols: usize,
}

impl<T> Matrix<T> 
where
    T: Clone + Copy + std::ops::Add<Output = T> + std::ops::Mul<Output = T> + Default + Send + Sync,
{
    pub fn new(rows: usize, cols: usize) -> Self {
        Self {
            data: vec![T::default(); rows * cols],
            rows,
            cols,
        }
    }
    
    pub fn from_vec(data: Vec<T>, rows: usize, cols: usize) -> Result<Self, String> {
        if data.len() != rows * cols {
            return Err("Data length doesn't match matrix dimensions".to_string());
        }
        Ok(Self { data, rows, cols })
    }
    
    // 并行矩阵乘法
    pub fn multiply(&self, other: &Matrix<T>) -> Result<Matrix<T>, String> {
        if self.cols != other.rows {
            return Err("Matrix dimensions incompatible for multiplication".to_string());
        }
        
        let mut result = Matrix::new(self.rows, other.cols);
        
        // 并行计算
        result.data.par_chunks_mut(other.cols)
            .enumerate()
            .for_each(|(i, row)| {
                for j in 0..other.cols {
                    row[j] = (0..self.cols)
                        .map(|k| self.get(i, k) * other.get(k, j))
                        .fold(T::default(), |acc, x| acc + x);
                }
            });
        
        Ok(result)
    }
    
    pub fn get(&self, row: usize, col: usize) -> T {
        self.data[row * self.cols + col]
    }
    
    pub fn set(&mut self, row: usize, col: usize, value: T) {
        self.data[row * self.cols + col] = value;
    }
    
    // LU分解
    pub fn lu_decomposition(&self) -> Result<(Matrix<T>, Matrix<T>), String> 
    where
        T: std::ops::Sub<Output = T> + std::ops::Div<Output = T> + PartialEq,
    {
        if self.rows != self.cols {
            return Err("Matrix must be square for LU decomposition".to_string());
        }
        
        let n = self.rows;
        let mut l = Matrix::new(n, n);
        let mut u = *self;
        
        // 高斯消元法
        for i in 0..n {
            // 设置L矩阵对角线元素为1
            l.set(i, i, T::default() + T::default()); // 假设1可以这样表示
            
            for k in i..n {
                // 计算U矩阵元素
                let mut sum = T::default();
                for j in 0..i {
                    sum = sum + l.get(i, j) * u.get(j, k);
                }
                u.set(i, k, self.get(i, k) - sum);
            }
            
            for k in (i + 1)..n {
                // 计算L矩阵元素
                let mut sum = T::default();
                for j in 0..i {
                    sum = sum + l.get(k, j) * u.get(j, i);
                }
                l.set(k, i, (self.get(k, i) - sum) / u.get(i, i));
            }
        }
        
        Ok((l, u))
    }
}

// 特征值计算（QR算法）
pub fn qr_eigenvalues<T>(matrix: &Matrix<T>, max_iterations: usize) -> Vec<T>
where
    T: Clone + Copy + Default + std::ops::Add<Output = T> + std::ops::Sub<Output = T> 
       + std::ops::Mul<Output = T> + std::ops::Div<Output = T> + PartialOrd + Send + Sync,
{
    let mut a = matrix.clone();
    
    for _ in 0..max_iterations {
        let (q, r) = qr_decomposition(&a);
        a = r.multiply(&q).unwrap();
    }
    
    // 提取对角线元素作为特征值
    (0..a.rows).map(|i| a.get(i, i)).collect()
}

// QR分解实现
fn qr_decomposition<T>(matrix: &Matrix<T>) -> (Matrix<T>, Matrix<T>)
where
    T: Clone + Copy + Default + std::ops::Add<Output = T> + std::ops::Sub<Output = T> 
       + std::ops::Mul<Output = T> + std::ops::Div<Output = T> + PartialOrd,
{
    // Gram-Schmidt过程
    todo!("Implement QR decomposition using Gram-Schmidt process")
}
```

## 科学计算算法

### 1. 数值积分

```haskell
-- 数值积分方法
type Function = Double -> Double

-- 梯形法则
trapezoidalRule :: Function -> Double -> Double -> Int -> Double
trapezoidalRule f a b n =
  let h = (b - a) / fromIntegral n
      xs = [a + fromIntegral i * h | i <- [0..n]]
      ys = map f xs
  in h * (sum (init (tail ys)) + (head ys + last ys) / 2)

-- 辛普森法则
simpsonsRule :: Function -> Double -> Double -> Int -> Double
simpsonsRule f a b n
  | even n = error "n must be odd for Simpson's rule"
  | otherwise = 
    let h = (b - a) / fromIntegral n
        xs = [a + fromIntegral i * h | i <- [0..n]]
        ys = map f xs
        odds = [ys !! i | i <- [1,3..n-1]]
        evens = [ys !! i | i <- [2,4..n-2]]
    in (h / 3) * (head ys + 4 * sum odds + 2 * sum evens + last ys)

-- 自适应积分
adaptiveIntegration :: Function -> Double -> Double -> Double -> Double
adaptiveIntegration f a b tolerance = 
  adaptiveStep f a b tolerance (simpsonsRule f a b 10)
  where
    adaptiveStep f a b tol estimate =
      let mid = (a + b) / 2
          left = simpsonsRule f a mid 10
          right = simpsonsRule f mid b 10
          combined = left + right
      in if abs (combined - estimate) < tol
         then combined
         else adaptiveStep f a mid (tol/2) left + 
              adaptiveStep f mid b (tol/2) right

-- 蒙特卡洛积分
monteCarloIntegration :: Function -> Double -> Double -> Int -> IO Double
monteCarloIntegration f a b n = do
  xs <- replicateM n (randomRIO (a, b))
  let samples = map f xs
      estimate = (b - a) * sum samples / fromIntegral n
  return estimate
```

### 2. 常微分方程求解

```haskell
-- ODE求解器
type ODE = Double -> Double -> Double  -- dy/dx = f(x, y)

-- 欧拉方法
eulerMethod :: ODE -> Double -> Double -> Double -> Int -> [Double]
eulerMethod f x0 y0 h n = take (n + 1) $ iterate step y0
  where 
    step y = y + h * f x0 y

-- 四阶龙格-库塔方法
rungeKutta4 :: ODE -> Double -> Double -> Double -> Int -> [(Double, Double)]
rungeKutta4 f x0 y0 h n = 
  take (n + 1) $ iterate step (x0, y0)
  where
    step (x, y) = 
      let k1 = h * f x y
          k2 = h * f (x + h/2) (y + k1/2)
          k3 = h * f (x + h/2) (y + k2/2)
          k4 = h * f (x + h) (y + k3)
          newY = y + (k1 + 2*k2 + 2*k3 + k4) / 6
          newX = x + h
      in (newX, newY)

-- 高阶ODE系统
type ODESystem = [Double] -> [Double] -> [Double]  -- 状态向量的导数

-- 向量化龙格-库塔法
rungeKutta4System :: ODESystem -> [Double] -> [Double] -> Double -> Int -> [[Double]]
rungeKutta4System f t0Vec y0Vec h n =
  take (n + 1) $ map snd $ iterate step (t0Vec, y0Vec)
  where
    step (t, y) =
      let k1 = map (* h) (f t y)
          k2 = map (* h) (f (zipWith (+) t [h/2 | _ <- t]) (zipWith (+) y (map (/2) k1)))
          k3 = map (* h) (f (zipWith (+) t [h/2 | _ <- t]) (zipWith (+) y (map (/2) k2)))
          k4 = map (* h) (f (zipWith (+) t [h | _ <- t]) (zipWith (+) y k3))
          newY = zipWith4 (\yi k1i k2i k3i k4i -> yi + (k1i + 2*k2i + 2*k3i + k4i)/6) y k1 k2 k3 k4
          newT = zipWith (+) t [h | _ <- t]
      in (newT, newY)
```

## 并行计算

### 1. 数据并行

```rust
// 并行数据处理
use rayon::prelude::*;
use std::sync::Arc;

// 并行映射操作
pub fn parallel_map<T, U, F>(data: Vec<T>, f: F) -> Vec<U>
where
    T: Send,
    U: Send,
    F: Fn(T) -> U + Send + Sync,
{
    data.into_par_iter()
        .map(f)
        .collect()
}

// 并行归约
pub fn parallel_reduce<T, F>(data: Vec<T>, identity: T, f: F) -> T
where
    T: Send + Copy,
    F: Fn(T, T) -> T + Send + Sync,
{
    data.into_par_iter()
        .reduce(|| identity, f)
}

// 并行前缀和
pub fn parallel_prefix_sum(data: &[f64]) -> Vec<f64> {
    if data.is_empty() {
        return vec![];
    }
    
    let n = data.len();
    let mut result = vec![0.0; n];
    result[0] = data[0];
    
    // 并行计算区块内前缀和
    let chunk_size = (n + rayon::current_num_threads() - 1) / rayon::current_num_threads();
    let chunks: Vec<_> = data.chunks(chunk_size).collect();
    
    let block_sums: Vec<f64> = chunks.par_iter()
        .map(|chunk| chunk.iter().sum())
        .collect();
    
    // 计算区块前缀和
    let mut block_prefix = vec![0.0; block_sums.len()];
    block_prefix[0] = block_sums[0];
    for i in 1..block_sums.len() {
        block_prefix[i] = block_prefix[i-1] + block_sums[i];
    }
    
    // 并行计算最终结果
    result.par_chunks_mut(chunk_size)
        .zip(data.par_chunks(chunk_size))
        .zip(block_prefix.par_iter())
        .enumerate()
        .for_each(|(block_idx, ((result_chunk, data_chunk), &block_offset))| {
            let mut local_sum = if block_idx == 0 { 0.0 } else { block_offset - block_sums[block_idx] };
            
            for (i, &value) in data_chunk.iter().enumerate() {
                local_sum += value;
                result_chunk[i] = local_sum + if block_idx == 0 { 0.0 } else { block_offset - block_sums[block_idx] };
            }
        });
    
    result
}

// GPU计算接口 (使用wgpu)
use wgpu::util::DeviceExt;

pub struct GpuComputer {
    device: wgpu::Device,
    queue: wgpu::Queue,
}

impl GpuComputer {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor::default());
        let adapter = instance.request_adapter(&wgpu::RequestAdapterOptions::default()).await
            .ok_or("Failed to get adapter")?;
        let (device, queue) = adapter.request_device(&wgpu::DeviceDescriptor::default(), None).await?;
        
        Ok(Self { device, queue })
    }
    
    pub async fn parallel_vector_add(&self, a: &[f32], b: &[f32]) -> Result<Vec<f32>, Box<dyn std::error::Error>> {
        let shader = self.device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("vector_add_shader"),
            source: wgpu::ShaderSource::Wgsl(include_str!("vector_add.wgsl").into()),
        });
        
        // 创建缓冲区
        let buffer_a = self.device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("Buffer A"),
            contents: bytemuck::cast_slice(a),
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        });
        
        let buffer_b = self.device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("Buffer B"),
            contents: bytemuck::cast_slice(b),
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        });
        
        let buffer_result = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Result Buffer"),
            size: (a.len() * std::mem::size_of::<f32>()) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        
        // 创建计算管道
        let compute_pipeline = self.device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("Vector Add Pipeline"),
            layout: None,
            module: &shader,
            entry_point: "main",
        });
        
        // 提交GPU计算
        let mut encoder = self.device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Vector Add Encoder"),
        });
        
        {
            let mut compute_pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Vector Add Pass"),
            });
            compute_pass.set_pipeline(&compute_pipeline);
            compute_pass.dispatch_workgroups((a.len() as u32 + 63) / 64, 1, 1);
        }
        
        self.queue.submit(std::iter::once(encoder.finish()));
        
        // 读取结果
        let staging_buffer = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Staging Buffer"),
            size: (a.len() * std::mem::size_of::<f32>()) as u64,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        
        let mut encoder = self.device.create_command_encoder(&wgpu::CommandEncoderDescriptor {
            label: Some("Copy Encoder"),
        });
        encoder.copy_buffer_to_buffer(&buffer_result, 0, &staging_buffer, 0, (a.len() * std::mem::size_of::<f32>()) as u64);
        self.queue.submit(std::iter::once(encoder.finish()));
        
        let buffer_slice = staging_buffer.slice(..);
        buffer_slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        
        let data = buffer_slice.get_mapped_range();
        let result: Vec<f32> = bytemuck::cast_slice(&data).to_vec();
        
        Ok(result)
    }
}
```

### 2. 任务并行

```haskell
-- 并行任务调度
{-# LANGUAGE BangPatterns #-}

import Control.Parallel
import Control.Parallel.Strategies
import Control.Concurrent.Async
import Control.Concurrent.STM

-- 并行策略
parallelMap :: Strategy b -> (a -> b) -> [a] -> [b]
parallelMap strat f xs = map f xs `using` parList strat

-- 分治算法并行化
divide :: [a] -> ([a], [a])
divide xs = splitAt (length xs `div` 2) xs

conquer :: (Ord a) => [a] -> [a] -> [a]
conquer = merge
  where
    merge [] ys = ys
    merge xs [] = xs
    merge (x:xs) (y:ys) 
      | x <= y    = x : merge xs (y:ys)
      | otherwise = y : merge (x:xs) ys

parallelMergeSort :: (Ord a) => [a] -> [a]
parallelMergeSort [] = []
parallelMergeSort [x] = [x]
parallelMergeSort xs = 
  let (left, right) = divide xs
      leftSorted = parallelMergeSort left
      rightSorted = parallelMergeSort right
  in leftSorted `par` rightSorted `par` conquer leftSorted rightSorted

-- 工作窃取池
data WorkPool a = WorkPool
  { tasks :: TVar [IO a]
  , workers :: Int
  , results :: TVar [a]
  }

createWorkPool :: Int -> IO (WorkPool a)
createWorkPool numWorkers = do
  tasks <- newTVarIO []
  results <- newTVarIO []
  return $ WorkPool tasks numWorkers results

addTask :: WorkPool a -> IO a -> IO ()
addTask pool task = atomically $ do
  currentTasks <- readTVar (tasks pool)
  writeTVar (tasks pool) (task : currentTasks)

worker :: WorkPool a -> IO ()
worker pool = do
  maybeTask <- atomically $ do
    currentTasks <- readTVar (tasks pool)
    case currentTasks of
      [] -> return Nothing
      (t:ts) -> do
        writeTVar (tasks pool) ts
        return (Just t)
  
  case maybeTask of
    Nothing -> return ()  -- 没有任务，退出
    Just task -> do
      result <- task
      atomically $ do
        currentResults <- readTVar (results pool)
        writeTVar (results pool) (result : currentResults)
      worker pool  -- 继续工作

runWorkPool :: WorkPool a -> IO [a]
runWorkPool pool = do
  workers <- mapM async $ replicate (workers pool) (worker pool)
  mapM_ wait workers
  readTVarIO (results pool)
```

## 科学数据分析

### 1. 统计计算

```haskell
-- 统计函数库
import qualified Statistics.Sample as Stat
import qualified Data.Vector.Unboxed as V

-- 描述性统计
data DescriptiveStats = DescriptiveStats
  { mean :: Double
  , median :: Double
  , mode :: [Double]
  , variance :: Double
  , standardDeviation :: Double
  , skewness :: Double
  , kurtosis :: Double
  , minimum :: Double
  , maximum :: Double
  , range :: Double
  , quartiles :: (Double, Double, Double)
  } deriving (Show)

calculateDescriptiveStats :: [Double] -> DescriptiveStats
calculateDescriptiveStats xs =
  let vec = V.fromList xs
      m = Stat.mean vec
      med = Stat.median vec
      var = Stat.variance vec
      std = sqrt var
      skew = calculateSkewness vec m std
      kurt = calculateKurtosis vec m std
      minVal = V.minimum vec
      maxVal = V.maximum vec
      rng = maxVal - minVal
      (q1, q2, q3) = calculateQuartiles vec
  in DescriptiveStats m med [] var std skew kurt minVal maxVal rng (q1, q2, q3)

calculateSkewness :: V.Vector Double -> Double -> Double -> Double
calculateSkewness vec mean std =
  let n = fromIntegral $ V.length vec
      sum3 = V.sum $ V.map (\x -> ((x - mean) / std) ^ 3) vec
  in sum3 / n

calculateKurtosis :: V.Vector Double -> Double -> Double -> Double
calculateKurtosis vec mean std =
  let n = fromIntegral $ V.length vec
      sum4 = V.sum $ V.map (\x -> ((x - mean) / std) ^ 4) vec
  in (sum4 / n) - 3  -- 超额峰度

calculateQuartiles :: V.Vector Double -> (Double, Double, Double)
calculateQuartiles vec =
  let sorted = V.fromList $ sort $ V.toList vec
      n = V.length sorted
      q1Index = n `div` 4
      q2Index = n `div` 2
      q3Index = 3 * n `div` 4
  in (sorted V.! q1Index, sorted V.! q2Index, sorted V.! q3Index)

-- 假设检验
data TTestResult = TTestResult
  { tStatistic :: Double
  , pValue :: Double
  , degreesOfFreedom :: Int
  , confidenceInterval :: (Double, Double)
  } deriving (Show)

oneSampleTTest :: [Double] -> Double -> TTestResult
oneSampleTTest sample mu0 =
  let n = fromIntegral $ length sample
      sampleMean = sum sample / n
      sampleVar = sum (map (\x -> (x - sampleMean)^2) sample) / (n - 1)
      sampleStd = sqrt sampleVar
      standardError = sampleStd / sqrt n
      tStat = (sampleMean - mu0) / standardError
      df = length sample - 1
      -- 计算p值需要t分布的CDF，这里简化
      pVal = 2 * (1 - approximateTCDF (abs tStat) df)
      alpha = 0.05
      tCritical = approximateTInverse (1 - alpha/2) df
      marginOfError = tCritical * standardError
      ci = (sampleMean - marginOfError, sampleMean + marginOfError)
  in TTestResult tStat pVal df ci

-- t分布近似（简化版本）
approximateTCDF :: Double -> Int -> Double
approximateTCDF t df = 
  -- 这是一个非常简化的近似，实际应该使用更准确的算法
  let x = t / sqrt (fromIntegral df)
  in 0.5 + 0.5 * tanh(x)

approximateTInverse :: Double -> Int -> Double
approximateTInverse p df =
  -- 简化的反函数近似
  let x = 2 * p - 1
  in sqrt (fromIntegral df) * atanh(x)
```

### 2. 时间序列分析

```rust
// 时间序列分析
use chrono::{DateTime, Utc};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct TimeSeries {
    data: BTreeMap<DateTime<Utc>, f64>,
}

impl TimeSeries {
    pub fn new() -> Self {
        Self {
            data: BTreeMap::new(),
        }
    }
    
    pub fn insert(&mut self, timestamp: DateTime<Utc>, value: f64) {
        self.data.insert(timestamp, value);
    }
    
    // 移动平均
    pub fn moving_average(&self, window_size: usize) -> TimeSeries {
        let mut result = TimeSeries::new();
        let values: Vec<_> = self.data.iter().collect();
        
        for i in (window_size - 1)..values.len() {
            let window = &values[(i - window_size + 1)..=i];
            let average = window.iter().map(|(_, &v)| v).sum::<f64>() / window_size as f64;
            result.insert(*values[i].0, average);
        }
        
        result
    }
    
    // 指数平滑
    pub fn exponential_smoothing(&self, alpha: f64) -> TimeSeries {
        let mut result = TimeSeries::new();
        let mut smoothed_value = 0.0;
        let mut first = true;
        
        for (&timestamp, &value) in &self.data {
            if first {
                smoothed_value = value;
                first = false;
            } else {
                smoothed_value = alpha * value + (1.0 - alpha) * smoothed_value;
            }
            result.insert(timestamp, smoothed_value);
        }
        
        result
    }
    
    // 季节性分解 (简化版)
    pub fn seasonal_decompose(&self, period: usize) -> (TimeSeries, TimeSeries, TimeSeries) {
        let mut trend = TimeSeries::new();
        let mut seasonal = TimeSeries::new();
        let mut residual = TimeSeries::new();
        
        // 计算趋势(使用移动平均)
        let trend_data = self.moving_average(period);
        
        // 计算季节性成分
        let values: Vec<_> = self.data.iter().collect();
        let trend_values: Vec<_> = trend_data.data.iter().collect();
        
        // 简化的季节性计算
        for (i, (&timestamp, &value)) in values.iter().enumerate() {
            if i < trend_values.len() {
                let trend_value = trend_values[i].1;
                let detrended = value - trend_value;
                
                trend.insert(timestamp, *trend_value);
                seasonal.insert(timestamp, detrended); // 简化的季节性
                residual.insert(timestamp, 0.0); // 简化的残差
            }
        }
        
        (trend, seasonal, residual)
    }
    
    // 自相关函数
    pub fn autocorrelation(&self, max_lag: usize) -> Vec<f64> {
        let values: Vec<f64> = self.data.values().cloned().collect();
        let n = values.len();
        let mean = values.iter().sum::<f64>() / n as f64;
        
        let mut autocorr = Vec::new();
        
        for lag in 0..=max_lag {
            if lag >= n {
                autocorr.push(0.0);
                continue;
            }
            
            let mut numerator = 0.0;
            let mut denominator = 0.0;
            
            for i in 0..(n - lag) {
                numerator += (values[i] - mean) * (values[i + lag] - mean);
            }
            
            for i in 0..n {
                denominator += (values[i] - mean).powi(2);
            }
            
            autocorr.push(numerator / denominator);
        }
        
        autocorr
    }
    
    // ARIMA模型预测 (简化版)
    pub fn arima_forecast(&self, p: usize, d: usize, q: usize, steps: usize) -> Vec<f64> {
        // 这是一个非常简化的ARIMA实现
        // 实际应用中应该使用专门的时间序列库
        
        let mut values: Vec<f64> = self.data.values().cloned().collect();
        
        // 差分处理
        for _ in 0..d {
            values = values.windows(2).map(|w| w[1] - w[0]).collect();
        }
        
        // 简化的AR预测
        let mut forecasts = Vec::new();
        let mut extended_values = values.clone();
        
        for _ in 0..steps {
            if extended_values.len() >= p {
                let ar_sum: f64 = extended_values.iter()
                    .rev()
                    .take(p)
                    .enumerate()
                    .map(|(i, &val)| val * (1.0 / (i + 1) as f64)) // 简化的AR系数
                    .sum();
                
                let forecast = ar_sum / p as f64;
                forecasts.push(forecast);
                extended_values.push(forecast);
            } else {
                // 如果数据不足，使用最后一个值
                forecasts.push(*extended_values.last().unwrap_or(&0.0));
            }
        }
        
        forecasts
    }
}

// 异常检测
pub fn detect_outliers(data: &[f64], method: OutlierMethod) -> Vec<usize> {
    match method {
        OutlierMethod::ZScore(threshold) => {
            let mean = data.iter().sum::<f64>() / data.len() as f64;
            let variance = data.iter()
                .map(|x| (x - mean).powi(2))
                .sum::<f64>() / data.len() as f64;
            let std_dev = variance.sqrt();
            
            data.iter()
                .enumerate()
                .filter_map(|(i, &value)| {
                    let z_score = (value - mean).abs() / std_dev;
                    if z_score > threshold {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect()
        }
        OutlierMethod::IQR(multiplier) => {
            let mut sorted_data = data.to_vec();
            sorted_data.sort_by(|a, b| a.partial_cmp(b).unwrap());
            
            let n = sorted_data.len();
            let q1 = sorted_data[n / 4];
            let q3 = sorted_data[3 * n / 4];
            let iqr = q3 - q1;
            
            let lower_bound = q1 - multiplier * iqr;
            let upper_bound = q3 + multiplier * iqr;
            
            data.iter()
                .enumerate()
                .filter_map(|(i, &value)| {
                    if value < lower_bound || value > upper_bound {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect()
        }
    }
}

pub enum OutlierMethod {
    ZScore(f64),
    IQR(f64),
}
```

## 总结

函数式编程在科学计算中的优势：

1. **数学表达力**: 函数式编程的数学基础使其特别适合科学计算
2. **组合性**: 复杂计算可以通过简单函数的组合来实现
3. **并行性**: 纯函数和不可变性使得并行计算更安全和高效
4. **正确性**: 类型系统和形式验证帮助确保计算的正确性
5. **可重现性**: 确定性计算保证结果的可重现性

科学计算的关键领域：

- **数值分析**: 高精度计算、数值稳定性、误差分析
- **线性代数**: 矩阵运算、特征值计算、分解算法
- **并行计算**: 数据并行、任务并行、GPU计算
- **统计分析**: 描述统计、假设检验、回归分析
- **时间序列**: 趋势分析、季节性分解、预测模型

通过结合函数式编程的理论优势和现代并行计算技术，我们能够构建高效、可靠的科学计算系统。
