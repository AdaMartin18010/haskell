# 应用科学基础

## 概述

应用科学是将基础理论转化为实际应用的桥梁。本文档介绍如何将形式方法、编程语言理论和数学基础应用到实际问题中，特别关注Haskell、Rust和Lean在科学计算和工程应用中的实现。

## 科学计算基础

### 数值计算

```haskell
-- 数值分析基础
module NumericalAnalysis where

import qualified Data.Vector as V

-- 浮点数精度控制
type Precision = Double
epsilon :: Precision
epsilon = 1e-10

-- 数值微分
numericalDerivative :: (Double -> Double) -> Double -> Double -> Double
numericalDerivative f x h = (f (x + h) - f (x - h)) / (2 * h)

-- 数值积分 - 梯形法则
trapezoidalRule :: (Double -> Double) -> Double -> Double -> Int -> Double
trapezoidalRule f a b n = 
  let h = (b - a) / fromIntegral n
      xs = [a + fromIntegral i * h | i <- [0..n]]
      ys = map f xs
  in h * (sum (init (tail ys)) + (head ys + last ys) / 2)

-- 辛普森积分法
simpsonsRule :: (Double -> Double) -> Double -> Double -> Int -> Double
simpsonsRule f a b n = 
  let h = (b - a) / fromIntegral n
      f' i = f (a + fromIntegral i * h)
      odds = sum [f' i | i <- [1,3..n-1]]
      evens = sum [f' i | i <- [2,4..n-2]]
  in (h / 3) * (f' 0 + 4 * odds + 2 * evens + f' n)
```

### 线性代数应用

```haskell
-- 矩阵运算库
module LinearAlgebra where

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

-- 矩阵类型定义
data Matrix a = Matrix 
  { rows :: Int
  , cols :: Int
  , values :: V.Vector a
  } deriving (Show, Eq)

-- 矩阵创建
fromList :: Int -> Int -> [a] -> Matrix a
fromList r c xs = Matrix r c (V.fromList xs)

-- 矩阵乘法
matrixMult :: Num a => Matrix a -> Matrix a -> Maybe (Matrix a)
matrixMult (Matrix r1 c1 v1) (Matrix r2 c2 v2)
  | c1 /= r2 = Nothing
  | otherwise = Just $ Matrix r1 c2 result
  where
    result = V.generate (r1 * c2) $ \idx ->
      let i = idx `div` c2
          j = idx `mod` c2
      in sum [v1 V.! (i * c1 + k) * v2 V.! (k * c2 + j) | k <- [0..c1-1]]

-- 高斯消元法
gaussianElimination :: Matrix Double -> Matrix Double
gaussianElimination mat@(Matrix r c v) = 
  let elimStep i mat'@(Matrix _ _ v') = 
        if i >= min r c then mat'
        else elimStep (i + 1) (pivotAndEliminate i mat')
  in elimStep 0 mat

pivotAndEliminate :: Int -> Matrix Double -> Matrix Double
pivotAndEliminate pivot (Matrix r c v) = 
  let pivotVal = v V.! (pivot * c + pivot)
      newValues = V.imap (\idx val ->
        let i = idx `div` c
            j = idx `mod` c
        in if i > pivot && j >= pivot
           then val - (v V.! (i * c + pivot)) * (v V.! (pivot * c + j)) / pivotVal
           else val) v
  in Matrix r c newValues
```

### 统计分析

```haskell
-- 统计计算模块
module Statistics where

import qualified Data.Vector as V

-- 基本统计量
mean :: V.Vector Double -> Double
mean xs = V.sum xs / fromIntegral (V.length xs)

variance :: V.Vector Double -> Double
variance xs = 
  let m = mean xs
      sq_diffs = V.map (\x -> (x - m)^2) xs
  in V.sum sq_diffs / fromIntegral (V.length xs - 1)

standardDeviation :: V.Vector Double -> Double
standardDeviation = sqrt . variance

-- 线性回归
data LinearModel = LinearModel 
  { slope :: Double
  , intercept :: Double
  , rSquared :: Double
  } deriving (Show)

linearRegression :: V.Vector Double -> V.Vector Double -> LinearModel
linearRegression xs ys = 
  let n = fromIntegral $ V.length xs
      sum_x = V.sum xs
      sum_y = V.sum ys
      sum_xy = V.sum $ V.zipWith (*) xs ys
      sum_x2 = V.sum $ V.map (^2) xs
      
      slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x^2)
      intercept = (sum_y - slope * sum_x) / n
      
      -- 计算 R²
      y_mean = sum_y / n
      ss_tot = V.sum $ V.map (\y -> (y - y_mean)^2) ys
      predictions = V.map (\x -> slope * x + intercept) xs
      ss_res = V.sum $ V.zipWith (\y pred -> (y - pred)^2) ys predictions
      r_squared = 1 - ss_res / ss_tot
      
  in LinearModel slope intercept r_squared

-- 概率分布
normalPDF :: Double -> Double -> Double -> Double
normalPDF mean stddev x = 
  let variance = stddev^2
      coefficient = 1 / sqrt (2 * pi * variance)
      exponent = -((x - mean)^2) / (2 * variance)
  in coefficient * exp exponent
```

## 科学模拟与建模

### 物理仿真

```haskell
-- 物理仿真系统
module Physics where

-- 粒子系统
data Particle = Particle
  { position :: (Double, Double, Double)
  , velocity :: (Double, Double, Double)
  , mass :: Double
  , charge :: Double
  } deriving (Show)

-- 力的计算
type Force = (Double, Double, Double)

gravitationalForce :: Particle -> Particle -> Force
gravitationalForce p1 p2 = 
  let (x1, y1, z1) = position p1
      (x2, y2, z2) = position p2
      dx = x2 - x1
      dy = y2 - y1
      dz = z2 - z1
      r = sqrt (dx^2 + dy^2 + dz^2)
      g = 6.674e-11  -- 万有引力常数
      f_magnitude = g * mass p1 * mass p2 / r^2
      unit_x = dx / r
      unit_y = dy / r
      unit_z = dz / r
  in (f_magnitude * unit_x, f_magnitude * unit_y, f_magnitude * unit_z)

-- 运动方程求解器
eulerMethod :: Double -> Particle -> [Force] -> Particle
eulerMethod dt particle forces = 
  let (px, py, pz) = position particle
      (vx, vy, vz) = velocity particle
      totalForce = foldr addForce (0, 0, 0) forces
      (fx, fy, fz) = totalForce
      m = mass particle
      
      -- 更新速度
      ax = fx / m
      ay = fy / m
      az = fz / m
      new_vx = vx + ax * dt
      new_vy = vy + ay * dt
      new_vz = vz + az * dt
      
      -- 更新位置
      new_px = px + new_vx * dt
      new_py = py + new_vy * dt
      new_pz = pz + new_vz * dt
      
  in particle { position = (new_px, new_py, new_pz)
              , velocity = (new_vx, new_vy, new_vz) }

addForce :: Force -> Force -> Force
addForce (f1x, f1y, f1z) (f2x, f2y, f2z) = (f1x + f2x, f1y + f2y, f1z + f2z)
```

### 生物信息学应用

```haskell
-- 生物信息学计算
module Bioinformatics where

import qualified Data.Map as M
import qualified Data.Set as S

-- DNA 序列分析
type DNASequence = String
type Nucleotide = Char

-- 基本序列操作
complement :: Nucleotide -> Nucleotide
complement 'A' = 'T'
complement 'T' = 'A'
complement 'G' = 'C'
complement 'C' = 'G'
complement n = n

reverseComplement :: DNASequence -> DNASequence
reverseComplement = reverse . map complement

-- GC 含量计算
gcContent :: DNASequence -> Double
gcContent seq = 
  let gcCount = length $ filter (`elem` "GC") seq
      totalCount = length seq
  in fromIntegral gcCount / fromIntegral totalCount

-- 序列比对 - 简单编辑距离
editDistance :: String -> String -> Int
editDistance [] ys = length ys
editDistance xs [] = length xs
editDistance (x:xs) (y:ys)
  | x == y = editDistance xs ys
  | otherwise = 1 + minimum 
      [ editDistance xs (y:ys)    -- 删除
      , editDistance (x:xs) ys    -- 插入
      , editDistance xs ys        -- 替换
      ]

-- 局部序列比对 - Smith-Waterman 算法简化版
localAlignment :: String -> String -> Int
localAlignment seq1 seq2 = 
  let m = length seq1
      n = length seq2
      scoreMatrix = [[score i j | j <- [0..n]] | i <- [0..m]]
      
      score 0 _ = 0
      score _ 0 = 0
      score i j = 
        let match = if seq1 !! (i-1) == seq2 !! (j-1) then 2 else -1
            diag = scoreMatrix !! (i-1) !! (j-1) + match
            up = scoreMatrix !! (i-1) !! j - 1
            left = scoreMatrix !! i !! (j-1) - 1
        in max 0 (maximum [diag, up, left])
        
  in maximum $ map maximum scoreMatrix

-- 蛋白质结构预测基础
type AminoAcid = Char
type Protein = String

-- 氨基酸属性
hydrophobicity :: M.Map AminoAcid Double
hydrophobicity = M.fromList
  [ ('A', 1.8), ('R', -4.5), ('N', -3.5), ('D', -3.5)
  , ('C', 2.5), ('Q', -3.5), ('E', -3.5), ('G', -0.4)
  , ('H', -3.2), ('I', 4.5), ('L', 3.8), ('K', -3.9)
  , ('M', 1.9), ('F', 2.8), ('P', -1.6), ('S', -0.8)
  , ('T', -0.7), ('W', -0.9), ('Y', -1.3), ('V', 4.2)
  ]

-- 疏水性预测
predictHydrophobicity :: Protein -> [Double]
predictHydrophobicity = map (\aa -> M.findWithDefault 0 aa hydrophobicity)
```

## 工程应用

### 信号处理

```haskell
-- 数字信号处理
module SignalProcessing where

import qualified Data.Vector as V
import Data.Complex

-- 离散傅里叶变换 (简化版)
dft :: V.Vector (Complex Double) -> V.Vector (Complex Double)
dft signal = V.generate n $ \k ->
  let omega = -2 * pi * fromIntegral k / fromIntegral n
      term j = (signal V.! j) * exp (0 :+ (omega * fromIntegral j))
  in sum [term j | j <- [0..n-1]]
  where n = V.length signal

-- 滤波器设计
data Filter = Filter
  { coefficients :: V.Vector Double
  , delayLine :: V.Vector Double
  } deriving (Show)

-- FIR 滤波器
firFilter :: Filter -> Double -> (Double, Filter)
firFilter (Filter coeffs delays) input = 
  let newDelays = V.cons input (V.init delays)
      output = V.sum $ V.zipWith (*) coeffs newDelays
  in (output, Filter coeffs newDelays)

-- 低通滤波器设计
lowPassFilter :: Int -> Double -> Filter
lowPassFilter n cutoff = 
  let coeffs = V.generate n $ \i ->
        let x = fromIntegral (i - n `div` 2)
        in if x == 0 
           then cutoff
           else sin (pi * cutoff * x) / (pi * x)
      delays = V.replicate n 0
  in Filter coeffs delays
```

### 控制系统

```haskell
-- 控制系统理论
module ControlSystems where

-- PID 控制器
data PIDController = PIDController
  { kp :: Double        -- 比例增益
  , ki :: Double        -- 积分增益
  , kd :: Double        -- 微分增益
  , integral :: Double  -- 积分累积
  , prevError :: Double -- 前一次误差
  } deriving (Show)

-- PID 控制计算
pidControl :: PIDController -> Double -> Double -> Double -> (Double, PIDController)
pidControl controller setpoint measured dt = 
  let error = setpoint - measured
      newIntegral = integral controller + error * dt
      derivative = (error - prevError controller) / dt
      
      output = kp controller * error + 
               ki controller * newIntegral + 
               kd controller * derivative
      
      newController = controller { integral = newIntegral, prevError = error }
      
  in (output, newController)

-- 状态空间模型
data StateSpaceModel = StateSpaceModel
  { stateMatrix :: [[Double]]     -- A 矩阵
  , inputMatrix :: [[Double]]     -- B 矩阵
  , outputMatrix :: [[Double]]    -- C 矩阵
  , feedthroughMatrix :: [[Double]] -- D 矩阵
  } deriving (Show)

-- 状态方程求解
stateUpdate :: StateSpaceModel -> [Double] -> [Double] -> [Double]
stateUpdate model state input = 
  let ax = matrixVectorMult (stateMatrix model) state
      bu = matrixVectorMult (inputMatrix model) input
  in zipWith (+) ax bu

matrixVectorMult :: [[Double]] -> [Double] -> [Double]
matrixVectorMult matrix vector = 
  map (sum . zipWith (*) vector) matrix
```

## 优化与求解

### 数值优化

```haskell
-- 数值优化算法
module Optimization where

-- 梯度下降法
gradientDescent :: (Double -> Double) -> (Double -> Double) -> Double -> Double -> Int -> Double
gradientDescent f f' x0 alpha maxIter = 
  let step x iter
        | iter <= 0 = x
        | otherwise = 
            let gradient = f' x
                newX = x - alpha * gradient
            in step newX (iter - 1)
  in step x0 maxIter

-- 牛顿法
newtonMethod :: (Double -> Double) -> (Double -> Double) -> (Double -> Double) -> Double -> Double -> Int -> Double
newtonMethod f f' f'' x0 tolerance maxIter = 
  let step x iter
        | iter <= 0 = x
        | abs (f x) < tolerance = x
        | otherwise = 
            let newX = x - f x / f' x
            in step newX (iter - 1)
  in step x0 maxIter

-- 多维优化 - 最速下降法
type Vector = [Double]

steepestDescent :: (Vector -> Double) -> (Vector -> Vector) -> Vector -> Double -> Int -> Vector
steepestDescent f grad x0 alpha maxIter = 
  let step x iter
        | iter <= 0 = x
        | otherwise = 
            let gradient = grad x
                newX = zipWith (\xi gi -> xi - alpha * gi) x gradient
            in step newX (iter - 1)
  in step x0 maxIter

-- 约束优化 - 拉格朗日乘数法概念
lagrangianOptimization :: (Vector -> Double) -> [Vector -> Double] -> Vector -> Vector
lagrangianOptimization objective constraints initialGuess = 
  -- 这里是一个概念性的实现，实际应用中需要更复杂的求解器
  initialGuess
```

### 线性规划

```haskell
-- 线性规划单纯形法 (简化版)
module LinearProgramming where

-- 单纯形表
data SimplexTableau = SimplexTableau
  { tableau :: [[Double]]
  , basicVariables :: [Int]
  , objectiveRow :: Int
  } deriving (Show)

-- 判断是否达到最优解
isOptimal :: SimplexTableau -> Bool
isOptimal (SimplexTableau t _ objRow) = 
  all (>= 0) (init (t !! objRow))  -- 目标函数行除最后一列都非负

-- 选择进基变量 (最小比值法则)
choosePivotColumn :: SimplexTableau -> Int
choosePivotColumn (SimplexTableau t _ objRow) = 
  let objRowValues = init (t !! objRow)
  in snd $ minimum $ zip objRowValues [0..]

-- 选择出基变量
choosePivotRow :: SimplexTableau -> Int -> Int
choosePivotRow (SimplexTableau t _ objRow) pivotCol = 
  let ratios = [if t !! i !! pivotCol > 0 
                then last (t !! i) / t !! i !! pivotCol 
                else 1/0  -- 无穷大
               | i <- [0..length t - 1], i /= objRow]
  in snd $ minimum $ zip ratios [0..]
```

## Rust 中的科学计算

### 高性能数值计算

```rust
// Rust 科学计算库
use nalgebra::{DMatrix, DVector};
use ndarray::{Array1, Array2};

// 矩阵运算
pub struct ScientificComputing;

impl ScientificComputing {
    // 高性能矩阵乘法
    pub fn matrix_multiply(a: &DMatrix<f64>, b: &DMatrix<f64>) -> Option<DMatrix<f64>> {
        if a.ncols() != b.nrows() {
            return None;
        }
        Some(a * b)
    }
    
    // 特征值计算
    pub fn eigenvalues(matrix: &DMatrix<f64>) -> Vec<f64> {
        // 使用 nalgebra 的特征值求解器
        matrix.symmetric_eigen().eigenvalues.iter().cloned().collect()
    }
    
    // 快速傅里叶变换
    pub fn fft(signal: &[f64]) -> Vec<num_complex::Complex<f64>> {
        use rustfft::{FftPlanner, num_complex::Complex};
        
        let mut planner = FftPlanner::new();
        let fft = planner.plan_fft_forward(signal.len());
        
        let mut buffer: Vec<Complex<f64>> = signal.iter()
            .map(|&x| Complex::new(x, 0.0))
            .collect();
            
        fft.process(&mut buffer);
        buffer
    }
}

// 并行科学计算
use rayon::prelude::*;

pub fn parallel_matrix_operations(data: &[Vec<f64>]) -> Vec<f64> {
    data.par_iter()
        .map(|row| row.iter().sum::<f64>() / row.len() as f64)
        .collect()
}

// SIMD 优化的向量运算
pub fn simd_dot_product(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b.iter()).map(|(x, y)| x * y).sum()
}
```

### 机器学习应用

```rust
// 机器学习基础算法
use ndarray::{Array1, Array2, Axis};

pub struct LinearRegression {
    weights: Array1<f64>,
    bias: f64,
}

impl LinearRegression {
    pub fn new(features: usize) -> Self {
        Self {
            weights: Array1::zeros(features),
            bias: 0.0,
        }
    }
    
    pub fn fit(&mut self, x: &Array2<f64>, y: &Array1<f64>, learning_rate: f64, epochs: usize) {
        let n_samples = x.nrows() as f64;
        
        for _ in 0..epochs {
            // 前向传播
            let predictions = self.predict(x);
            let errors = &predictions - y;
            
            // 计算梯度
            let weight_gradients = x.t().dot(&errors) / n_samples;
            let bias_gradient = errors.sum() / n_samples;
            
            // 更新参数
            self.weights = &self.weights - learning_rate * &weight_gradients;
            self.bias -= learning_rate * bias_gradient;
        }
    }
    
    pub fn predict(&self, x: &Array2<f64>) -> Array1<f64> {
        x.dot(&self.weights) + self.bias
    }
}

// 神经网络基础
pub struct NeuralNetwork {
    layers: Vec<Array2<f64>>,
    biases: Vec<Array1<f64>>,
}

impl NeuralNetwork {
    pub fn new(layer_sizes: &[usize]) -> Self {
        let mut layers = Vec::new();
        let mut biases = Vec::new();
        
        for i in 0..layer_sizes.len() - 1 {
            layers.push(Array2::random((layer_sizes[i], layer_sizes[i + 1]), rand::random));
            biases.push(Array1::random(layer_sizes[i + 1], rand::random));
        }
        
        Self { layers, biases }
    }
    
    fn sigmoid(x: f64) -> f64 {
        1.0 / (1.0 + (-x).exp())
    }
    
    pub fn forward(&self, input: &Array1<f64>) -> Array1<f64> {
        let mut activation = input.clone();
        
        for (layer, bias) in self.layers.iter().zip(self.biases.iter()) {
            activation = activation.dot(layer) + bias;
            activation.mapv_inplace(Self::sigmoid);
        }
        
        activation
    }
}
```

## Lean 中的科学计算证明

### 数值计算的形式验证

```lean
-- 数值计算的正确性证明
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- 数值微分的误差分析
theorem numerical_derivative_error 
  (f : ℝ → ℝ) (x h : ℝ) (hf : DifferentiableAt ℝ f x) :
  |((f (x + h) - f (x - h)) / (2 * h)) - deriv f x| ≤ 
  (h^2 / 6) * ‖deriv (deriv f) x‖ :=
sorry

-- 浮点运算的精度分析
structure FloatingPoint where
  mantissa : ℤ
  exponent : ℤ
  precision : ℕ

def fp_add (a b : FloatingPoint) : FloatingPoint :=
sorry

theorem fp_addition_error 
  (a b : FloatingPoint) (x y : ℝ) 
  (ha : abs (a.mantissa * 2^a.exponent - x) ≤ 2^(a.exponent - a.precision))
  (hb : abs (b.mantissa * 2^b.exponent - y) ≤ 2^(b.exponent - b.precision)) :
  abs ((fp_add a b).mantissa * 2^(fp_add a b).exponent - (x + y)) ≤ 
  2^(max a.exponent b.exponent - min a.precision b.precision + 1) :=
sorry

-- 算法复杂度的形式化
def time_complexity (n : ℕ) : ℕ := n^2

theorem sorting_algorithm_complexity 
  (sort : List ℕ → List ℕ) (xs : List ℕ) :
  (∃ c : ℕ, runtime (sort xs) ≤ c * time_complexity xs.length) :=
sorry
```

### 物理定律的数学建模

```lean
-- 物理定律的形式化
structure PhysicalSystem where
  position : ℝ → ℝ³
  velocity : ℝ → ℝ³
  acceleration : ℝ → ℝ³

-- 牛顿第二定律
theorem newtons_second_law 
  (sys : PhysicalSystem) (m : ℝ) (F : ℝ → ℝ³) (t : ℝ) :
  m • sys.acceleration t = F t :=
sorry

-- 能量守恒定律
theorem energy_conservation 
  (sys : PhysicalSystem) (m : ℝ) (V : ℝ³ → ℝ) (t₁ t₂ : ℝ) :
  (1/2) * m * ‖sys.velocity t₁‖^2 + V (sys.position t₁) = 
  (1/2) * m * ‖sys.velocity t₂‖^2 + V (sys.position t₂) :=
sorry

-- 麦克斯韦方程组的形式化
structure ElectromagneticField where
  E : ℝ³ → ℝ → ℝ³  -- 电场
  B : ℝ³ → ℝ → ℝ³  -- 磁场

theorem maxwell_faraday_law 
  (field : ElectromagneticField) (r : ℝ³) (t : ℝ) :
  curl (field.E r) t = -∂t (field.B r) t :=
sorry
```

## 工业应用案例

### 制造业优化

```haskell
-- 生产调度优化
module Manufacturing where

-- 生产任务
data Task = Task
  { taskId :: Int
  , duration :: Double
  , deadline :: Double
  , priority :: Int
  } deriving (Show, Eq)

-- 机器资源
data Machine = Machine
  { machineId :: Int
  , capacity :: Double
  , availability :: [(Double, Double)]  -- (开始时间, 结束时间)
  } deriving (Show)

-- 调度方案
data Schedule = Schedule
  { assignments :: [(Task, Machine, Double)]  -- (任务, 机器, 开始时间)
  , totalCost :: Double
  , completionTime :: Double
  } deriving (Show)

-- 最早完成时间调度
earliestFinishTime :: [Task] -> [Machine] -> Schedule
earliestFinishTime tasks machines = 
  let sortedTasks = sortBy (comparing deadline) tasks
      assignments = scheduleGreedy sortedTasks machines []
      cost = sum [priority task * max 0 (startTime + duration task - deadline task) 
                 | (task, _, startTime) <- assignments]
      maxCompletion = maximum [startTime + duration task | (task, _, startTime) <- assignments]
  in Schedule assignments cost maxCompletion

scheduleGreedy :: [Task] -> [Machine] -> [(Task, Machine, Double)] -> [(Task, Machine, Double)]
scheduleGreedy [] _ acc = acc
scheduleGreedy (task:tasks) machines acc = 
  let bestAssignment = findBestMachine task machines
  in scheduleGreedy tasks machines (bestAssignment : acc)

findBestMachine :: Task -> [Machine] -> (Task, Machine, Double)
findBestMachine task machines = 
  let assignments = [(task, machine, earliestStart machine) | machine <- machines]
      bestAssignment = minimumBy (comparing (\(_, _, start) -> start)) assignments
  in bestAssignment

earliestStart :: Machine -> Double
earliestStart machine = 
  case availability machine of
    [] -> 0.0
    slots -> minimum [start | (start, _) <- slots]
```

### 金融建模

```haskell
-- 金融风险模型
module Finance where

-- 股票价格模型
data Stock = Stock
  { symbol :: String
  , price :: Double
  , volatility :: Double
  , expectedReturn :: Double
  } deriving (Show)

-- 布朗运动模拟
brownianMotion :: Double -> Double -> Int -> [Double] -> [Double]
brownianMotion dt sigma steps randoms = 
  scanl1 (+) [sigma * sqrt dt * r | r <- take steps randoms]

-- 几何布朗运动 (股价模型)
geometricBrownianMotion :: Double -> Double -> Double -> Double -> Int -> [Double] -> [Double]
geometricBrownianMotion s0 mu sigma dt steps randoms = 
  let dW = brownianMotion dt 1.0 steps randoms
      prices = scanl (\s dw -> s * exp ((mu - 0.5 * sigma^2) * dt + sigma * dw)) s0 dW
  in prices

-- 期权定价 - 蒙特卡洛方法
monteCarloOptionPricing :: Stock -> Double -> Double -> Double -> Int -> [Double] -> Double
monteCarloOptionPricing stock strike timeToExpiry riskFreeRate numSims randoms = 
  let dt = timeToExpiry
      simulations = geometricBrownianMotion (price stock) riskFreeRate (volatility stock) dt 1 randoms
      payoffs = [max 0 (finalPrice - strike) | finalPrice <- simulations]
      averagePayoff = sum payoffs / fromIntegral (length payoffs)
  in averagePayoff * exp (-riskFreeRate * timeToExpiry)

-- 投资组合优化
data Portfolio = Portfolio
  { stocks :: [Stock]
  , weights :: [Double]
  } deriving (Show)

portfolioReturn :: Portfolio -> Double
portfolioReturn (Portfolio stocks weights) = 
  sum $ zipWith (\stock weight -> weight * expectedReturn stock) stocks weights

portfolioVolatility :: Portfolio -> [[Double]] -> Double
portfolioVolatility (Portfolio _ weights) covarianceMatrix = 
  sqrt $ sum [weights !! i * weights !! j * (covarianceMatrix !! i !! j)
             | i <- [0..length weights - 1], j <- [0..length weights - 1]]
```

## 总结

应用科学将理论转化为实践，通过以下方式实现：

1. **数值方法**: 将连续问题离散化，使用计算机求解
2. **建模仿真**: 建立数学模型，模拟真实系统行为  
3. **优化算法**: 在约束条件下寻找最优解
4. **验证确认**: 使用形式方法验证算法正确性

在Haskell、Rust和Lean的生态中：

- **Haskell**: 提供高级抽象和数学表达能力
- **Rust**: 提供系统级性能和内存安全
- **Lean**: 提供形式验证和定理证明能力

这三种语言的结合使用，能够在保证正确性的同时，实现高性能的科学计算应用。

## 参考资料

- [Numerical Recipes](http://numerical.recipes/)
- [Scientific Computing with Haskell](https://wiki.haskell.org/Numeric_Haskell:_A_Vector_Tutorial)
- [Rust Scientific Computing](https://www.rust-lang.org/what/science)
- [Lean Mathematical Library](https://leanprover-community.github.io/mathlib_docs/)
