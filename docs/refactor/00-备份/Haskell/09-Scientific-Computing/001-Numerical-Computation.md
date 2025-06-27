# Haskell数值计算

## 📚 快速导航

### 相关理论

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [算法实现](../07-Algorithms/001-Sorting-Algorithms.md)

### 实现示例

- [线性代数](./002-Linear-Algebra.md)
- [微分方程](./003-Differential-Equations.md)
- [优化算法](./004-Optimization-Algorithms.md)

## 🎯 概述

Haskell在科学计算领域具有独特的优势，包括类型安全、高性能和函数式编程的优雅性。本文档介绍Haskell数值计算的基础概念、算法实现和实际应用。

## 📖 1. 数值计算基础

### 1.1 数值类型

**定义 1.1 (数值类型)**
Haskell提供多种数值类型用于科学计算。

```haskell
-- 基本数值类型
basicNumericTypes :: IO ()
basicNumericTypes = do
  let intVal :: Int = 42
      doubleVal :: Double = 3.14159
      floatVal :: Float = 2.71828
      rationalVal :: Rational = 22 % 7
      
  putStrLn $ "Integer: " ++ show intVal
  putStrLn $ "Double: " ++ show doubleVal
  putStrLn $ "Float: " ++ show floatVal
  putStrLn $ "Rational: " ++ show rationalVal
```

### 1.2 数值精度

**定义 1.2 (数值精度)**
数值精度是科学计算中的重要考虑因素。

```haskell
-- 精度比较
precisionComparison :: IO ()
precisionComparison = do
  let piDouble = pi :: Double
      piFloat = pi :: Float
      piRational = 355 % 113
      
  putStrLn $ "Pi as Double: " ++ show piDouble
  putStrLn $ "Pi as Float: " ++ show piFloat
  putStrLn $ "Pi as Rational: " ++ show piRational
  putStrLn $ "Float precision: " ++ show (floatDigits piFloat)
  putStrLn $ "Double precision: " ++ show (floatDigits piDouble)
```

## 🔧 2. 数值算法

### 2.1 数值积分

**定义 2.1 (数值积分)**
数值积分是计算函数定积分的数值方法。

```haskell
-- 矩形法积分
rectangleIntegration :: (Double -> Double) -> Double -> Double -> Int -> Double
rectangleIntegration f a b n = 
  let h = (b - a) / fromIntegral n
      xs = [a + h * fromIntegral i | i <- [0..n-1]]
  in h * sum (map f xs)

-- 梯形法积分
trapezoidIntegration :: (Double -> Double) -> Double -> Double -> Int -> Double
trapezoidIntegration f a b n = 
  let h = (b - a) / fromIntegral n
      xs = [a + h * fromIntegral i | i <- [0..n]]
      ys = map f xs
  in h * (sum (init ys) + sum (tail ys)) / 2

-- 辛普森法积分
simpsonIntegration :: (Double -> Double) -> Double -> Double -> Int -> Double
simpsonIntegration f a b n = 
  let h = (b - a) / fromIntegral n
      xs = [a + h * fromIntegral i | i <- [0..n]]
      ys = map f xs
      weights = [1, 4, 2] ++ replicate (n-3) 4 ++ [2, 4, 1]
  in h * sum (zipWith (*) weights ys) / 3

-- 积分示例
integrationExample :: IO ()
integrationExample = do
  let f x = x * x  -- f(x) = x²
      a = 0.0
      b = 1.0
      n = 100
      
      rectangleResult = rectangleIntegration f a b n
      trapezoidResult = trapezoidIntegration f a b n
      simpsonResult = simpsonIntegration f a b n
      exactResult = 1.0 / 3.0
      
  putStrLn $ "Integrating x² from 0 to 1:"
  putStrLn $ "Rectangle method: " ++ show rectangleResult
  putStrLn $ "Trapezoid method: " ++ show trapezoidResult
  putStrLn $ "Simpson method: " ++ show simpsonResult
  putStrLn $ "Exact result: " ++ show exactResult
```

### 2.2 数值微分

**定义 2.2 (数值微分)**
数值微分是计算函数导数的数值方法。

```haskell
-- 前向差分
forwardDifference :: (Double -> Double) -> Double -> Double -> Double
forwardDifference f x h = (f (x + h) - f x) / h

-- 后向差分
backwardDifference :: (Double -> Double) -> Double -> Double -> Double
backwardDifference f x h = (f x - f (x - h)) / h

-- 中心差分
centralDifference :: (Double -> Double) -> Double -> Double -> Double
centralDifference f x h = (f (x + h) - f (x - h)) / (2 * h)

-- 微分示例
differentiationExample :: IO ()
differentiationExample = do
  let f x = x * x  -- f(x) = x², f'(x) = 2x
      x = 2.0
      h = 0.001
      
      forwardResult = forwardDifference f x h
      backwardResult = backwardDifference f x h
      centralResult = centralDifference f x h
      exactResult = 2 * x
      
  putStrLn $ "Differentiating x² at x = 2:"
  putStrLn $ "Forward difference: " ++ show forwardResult
  putStrLn $ "Backward difference: " ++ show backwardResult
  putStrLn $ "Central difference: " ++ show centralResult
  putStrLn $ "Exact result: " ++ show exactResult
```

## 💾 3. 数值求解

### 3.1 方程求解

**定义 3.1 (方程求解)**
数值方法求解非线性方程。

```haskell
-- 二分法
bisectionMethod :: (Double -> Double) -> Double -> Double -> Double -> Double
bisectionMethod f a b tolerance
  | abs (b - a) < tolerance = (a + b) / 2
  | f c < 0 = bisectionMethod f c b tolerance
  | otherwise = bisectionMethod f a c tolerance
  where c = (a + b) / 2

-- 牛顿法
newtonMethod :: (Double -> Double) -> (Double -> Double) -> Double -> Double -> Double
newtonMethod f f' x0 tolerance
  | abs (f x0) < tolerance = x0
  | otherwise = newtonMethod f f' x1 tolerance
  where x1 = x0 - f x0 / f' x0

-- 方程求解示例
equationSolvingExample :: IO ()
equationSolvingExample = do
  let f x = x * x - 4  -- f(x) = x² - 4, 根为 ±2
      f' x = 2 * x     -- f'(x) = 2x
      
      bisectionResult = bisectionMethod f 0 3 0.0001
      newtonResult = newtonMethod f f' 3 0.0001
      
  putStrLn $ "Solving x² - 4 = 0:"
  putStrLn $ "Bisection method: " ++ show bisectionResult
  putStrLn $ "Newton method: " ++ show newtonResult
  putStrLn $ "Exact positive root: 2.0"
```

### 3.2 插值

**定义 3.2 (插值)**
插值是在已知数据点之间估计函数值的方法。

```haskell
-- 拉格朗日插值
lagrangeInterpolation :: [(Double, Double)] -> Double -> Double
lagrangeInterpolation points x = 
  sum [yi * product [(x - xj) / (xi - xj) | (xj, _) <- points, xj /= xi] 
       | (xi, yi) <- points]

-- 线性插值
linearInterpolation :: [(Double, Double)] -> Double -> Double
linearInterpolation points x = 
  case findSegment points x of
    Just ((x1, y1), (x2, y2)) -> 
      y1 + (y2 - y1) * (x - x1) / (x2 - x1)
    Nothing -> error "Point outside range"

-- 查找线段
findSegment :: [(Double, Double)] -> Double -> Maybe ((Double, Double), (Double, Double))
findSegment points x = 
  case dropWhile (\(x1, _) -> x1 < x) (sort points) of
    (x2, y2):_ -> 
      case takeWhile (\(x1, _) -> x1 < x) (sort points) of
        [] -> Nothing
        points' -> Just (last points', (x2, y2))
    [] -> Nothing

-- 插值示例
interpolationExample :: IO ()
interpolationExample = do
  let points = [(0, 1), (1, 2), (2, 4), (3, 8)]
      x = 1.5
      
      lagrangeResult = lagrangeInterpolation points x
      linearResult = linearInterpolation points x
      
  putStrLn $ "Interpolating at x = 1.5:"
  putStrLn $ "Data points: " ++ show points
  putStrLn $ "Lagrange interpolation: " ++ show lagrangeResult
  putStrLn $ "Linear interpolation: " ++ show linearResult
```

## 🎭 4. 随机数生成

### 4.1 随机数基础

**定义 4.1 (随机数)**
随机数在科学计算中有重要应用。

```haskell
-- 线性同余生成器
data LCG = LCG {
  seed :: Int,
  multiplier :: Int,
  increment :: Int,
  modulus :: Int
} deriving (Show)

-- 生成下一个随机数
nextRandom :: LCG -> (Int, LCG)
nextRandom (LCG seed mult inc mod) = 
  let nextSeed = (mult * seed + inc) `mod` mod
  in (nextSeed, LCG nextSeed mult inc mod)

-- 生成随机数序列
randomSequence :: LCG -> Int -> [Int]
randomSequence lcg n = 
  take n $ unfoldr (Just . nextRandom) lcg

-- 随机数示例
randomNumberExample :: IO ()
randomNumberExample = do
  let lcg = LCG 12345 1103515245 12345 2147483648
      randomNumbers = randomSequence lcg 10
      
  putStrLn $ "Random numbers: " ++ show randomNumbers
```

### 4.2 概率分布

**定义 4.2 (概率分布)**
实现常见的概率分布。

```haskell
-- 均匀分布
uniformDistribution :: Double -> Double -> Double -> Double
uniformDistribution a b u = a + (b - a) * u

-- 正态分布（Box-Muller变换）
normalDistribution :: Double -> Double -> Double -> Double -> (Double, Double)
normalDistribution mu sigma u1 u2 = 
  let z1 = sqrt (-2 * log u1) * cos (2 * pi * u2)
      z2 = sqrt (-2 * log u1) * sin (2 * pi * u2)
  in (mu + sigma * z1, mu + sigma * z2)

-- 指数分布
exponentialDistribution :: Double -> Double -> Double
exponentialDistribution lambda u = -log u / lambda

-- 概率分布示例
probabilityDistributionExample :: IO ()
probabilityDistributionExample = do
  let u1 = 0.5
      u2 = 0.3
      
      uniformResult = uniformDistribution 0 1 u1
      (normal1, normal2) = normalDistribution 0 1 u1 u2
      exponentialResult = exponentialDistribution 1 u1
      
  putStrLn $ "Probability distributions:"
  putStrLn $ "Uniform(0,1): " ++ show uniformResult
  putStrLn $ "Normal(0,1): " ++ show normal1 ++ ", " ++ show normal2
  putStrLn $ "Exponential(1): " ++ show exponentialResult
```

## ⚡ 5. 数值优化

### 5.1 函数优化

**定义 5.1 (函数优化)**
数值方法寻找函数的最优值。

```haskell
-- 黄金分割搜索
goldenSectionSearch :: (Double -> Double) -> Double -> Double -> Double -> Double
goldenSectionSearch f a b tolerance
  | abs (b - a) < tolerance = (a + b) / 2
  | f x1 < f x2 = goldenSectionSearch f a x2 tolerance
  | otherwise = goldenSectionSearch f x1 b tolerance
  where
    phi = (1 + sqrt 5) / 2
    x1 = b - (b - a) / phi
    x2 = a + (b - a) / phi

-- 梯度下降
gradientDescent :: (Double -> Double) -> (Double -> Double) -> Double -> Double -> Int -> Double
gradientDescent f f' x0 learningRate iterations
  | iterations <= 0 = x0
  | otherwise = gradientDescent f f' x1 learningRate (iterations - 1)
  where x1 = x0 - learningRate * f' x0

-- 优化示例
optimizationExample :: IO ()
optimizationExample = do
  let f x = x * x + 2 * x + 1  -- f(x) = x² + 2x + 1, 最小点在 x = -1
      f' x = 2 * x + 2         -- f'(x) = 2x + 2
      
      goldenResult = goldenSectionSearch f (-3) 1 0.0001
      gradientResult = gradientDescent f f' 0 0.1 100
      
  putStrLn $ "Optimizing f(x) = x² + 2x + 1:"
  putStrLn $ "Golden section search: " ++ show goldenResult
  putStrLn $ "Gradient descent: " ++ show gradientResult
  putStrLn $ "Exact minimum at: -1.0"
```

### 5.2 约束优化

**定义 5.2 (约束优化)**
处理有约束条件的优化问题。

```haskell
-- 拉格朗日乘数法（简化版）
lagrangeMultiplier :: (Double -> Double) -> (Double -> Double) -> Double -> Double
lagrangeMultiplier f g lambda = 
  f lambda + lambda * g lambda

-- 约束优化示例
constrainedOptimizationExample :: IO ()
constrainedOptimizationExample = do
  let f x = x * x  -- 目标函数 f(x) = x²
      g x = x - 1  -- 约束条件 g(x) = x - 1 = 0
      
      -- 在约束 x = 1 下优化 f(x)
      result = lagrangeMultiplier f g 1
      
  putStrLn $ "Constrained optimization:"
  putStrLn $ "Minimize f(x) = x² subject to x = 1"
  putStrLn $ "Result: " ++ show result
```

## 🔄 6. 数值稳定性

### 6.1 误差分析

**定义 6.1 (误差分析)**
分析数值计算的误差。

```haskell
-- 相对误差
relativeError :: Double -> Double -> Double
relativeError exact approximate = 
  abs (exact - approximate) / abs exact

-- 绝对误差
absoluteError :: Double -> Double -> Double
absoluteError exact approximate = 
  abs (exact - approximate)

-- 误差分析示例
errorAnalysisExample :: IO ()
errorAnalysisExample = do
  let exact = pi
      approximate = 22 / 7
      
      absError = absoluteError exact approximate
      relError = relativeError exact approximate
      
  putStrLn $ "Error analysis:"
  putStrLn $ "Exact value of π: " ++ show exact
  putStrLn $ "Approximation 22/7: " ++ show approximate
  putStrLn $ "Absolute error: " ++ show absError
  putStrLn $ "Relative error: " ++ show relError
```

### 6.2 条件数

**定义 6.2 (条件数)**
条件数衡量问题的数值稳定性。

```haskell
-- 矩阵条件数（简化版）
matrixConditionNumber :: [[Double]] -> Double
matrixConditionNumber matrix = 
  let det = determinant matrix
      norm = matrixNorm matrix
  in if det == 0 then 1/0 else norm / abs det

-- 行列式计算
determinant :: [[Double]] -> Double
determinant [[a]] = a
determinant matrix = 
  sum [(-1)^i * head matrix !! i * determinant (minor matrix 0 i) 
       | i <- [0..length (head matrix) - 1]]

-- 矩阵范数
matrixNorm :: [[Double]] -> Double
matrixNorm matrix = 
  maximum [sum [abs (matrix !! i !! j) | j <- [0..length (head matrix) - 1]]
           | i <- [0..length matrix - 1]]

-- 子矩阵
minor :: [[Double]] -> Int -> Int -> [[Double]]
minor matrix row col = 
  [take col row' ++ drop (col + 1) row' 
   | (i, row') <- zip [0..] matrix, i /= row]

-- 条件数示例
conditionNumberExample :: IO ()
conditionNumberExample = do
  let matrix = [[1, 2], [3, 4]]
      cond = matrixConditionNumber matrix
      
  putStrLn $ "Matrix condition number:"
  putStrLn $ "Matrix: " ++ show matrix
  putStrLn $ "Condition number: " ++ show cond
```

## 🛠️ 7. 实际应用

### 7.1 物理模拟

**定义 7.1 (物理模拟)**
数值方法在物理模拟中的应用。

```haskell
-- 简单摆模拟
data Pendulum = Pendulum {
  length :: Double,
  mass :: Double,
  angle :: Double,
  angularVelocity :: Double
} deriving (Show)

-- 欧拉方法模拟
eulerSimulation :: Pendulum -> Double -> Int -> [Pendulum]
eulerSimulation pendulum dt steps = 
  take steps $ iterate (eulerStep dt) pendulum

-- 欧拉步骤
eulerStep :: Double -> Pendulum -> Pendulum
eulerStep dt (Pendulum l m theta omega) = 
  let g = 9.81
      alpha = -g * sin theta / l
      newOmega = omega + alpha * dt
      newTheta = theta + omega * dt
  in Pendulum l m newTheta newOmega

-- 物理模拟示例
physicsSimulationExample :: IO ()
physicsSimulationExample = do
  let pendulum = Pendulum 1.0 1.0 (pi/4) 0.0
      dt = 0.01
      steps = 100
      simulation = eulerSimulation pendulum dt steps
      
  putStrLn $ "Pendulum simulation:"
  putStrLn $ "Initial state: " ++ show pendulum
  putStrLn $ "Final angle: " ++ show (angle (last simulation))
```

### 7.2 金融计算

**定义 7.2 (金融计算)**
数值方法在金融计算中的应用。

```haskell
-- 复利计算
compoundInterest :: Double -> Double -> Int -> Double
compoundInterest principal rate periods = 
  principal * (1 + rate) ^ periods

-- 年金现值
presentValue :: Double -> Double -> Int -> Double
presentValue payment rate periods = 
  payment * (1 - (1 + rate) ^ (-periods)) / rate

-- 期权定价（简化Black-Scholes）
blackScholes :: Double -> Double -> Double -> Double -> Double -> Double -> Double
blackScholes s k t r sigma callPut = 
  let d1 = (log (s / k) + (r + sigma^2 / 2) * t) / (sigma * sqrt t)
      d2 = d1 - sigma * sqrt t
      nd1 = normalCDF d1
      nd2 = normalCDF d2
  in case callPut of
       1 -> s * nd1 - k * exp (-r * t) * nd2  -- Call option
       _ -> k * exp (-r * t) * normalCDF (-d2) - s * normalCDF (-d1)  -- Put option

-- 正态分布累积函数（简化）
normalCDF :: Double -> Double
normalCDF x = 0.5 * (1 + erf (x / sqrt 2))
  where erf z = 2 / sqrt pi * sum [(-1)^n * z^(2*n+1) / (fromIntegral (factorial n) * (2*n+1)) | n <- [0..10]]
        factorial n = product [1..n]

-- 金融计算示例
financialCalculationExample :: IO ()
financialCalculationExample = do
  let principal = 1000.0
      rate = 0.05
      periods = 10
      
      compoundResult = compoundInterest principal rate periods
      annuityResult = presentValue 100 rate periods
      optionResult = blackScholes 100 100 1 0.05 0.2 1
      
  putStrLn $ "Financial calculations:"
  putStrLn $ "Compound interest: " ++ show compoundResult
  putStrLn $ "Annuity present value: " ++ show annuityResult
  putStrLn $ "Call option price: " ++ show optionResult
```

## 📊 8. 性能优化

### 8.1 算法优化

**定义 8.1 (算法优化)**
优化数值算法的性能。

```haskell
-- 快速傅里叶变换（简化版）
fft :: [Complex Double] -> [Complex Double]
fft [] = []
fft [x] = [x]
fft xs = 
  let n = length xs
      half = n `div` 2
      (evens, odds) = splitAt half xs
      evensFFT = fft evens
      oddsFFT = fft odds
      twiddleFactors = [cis (-2 * pi * fromIntegral k / fromIntegral n) | k <- [0..half-1]]
  in zipWith (+) evensFFT (zipWith (*) twiddleFactors oddsFFT) ++
     zipWith (-) evensFFT (zipWith (*) twiddleFactors oddsFFT)

-- 性能测试
performanceTest :: IO ()
performanceTest = do
  let n = 1024
      data = [fromIntegral i :+ 0 | i <- [0..n-1]]
      
      start = getCurrentTime
      result = fft data
      end = getCurrentTime
      
      duration = diffUTCTime end start
      
  putStrLn $ "FFT performance test:"
  putStrLn $ "Input size: " ++ show n
  putStrLn $ "Execution time: " ++ show duration
```

### 8.2 并行计算

**定义 8.2 (并行计算)**
利用并行计算加速数值算法。

```haskell
-- 并行数值积分
parallelIntegration :: (Double -> Double) -> Double -> Double -> Int -> IO Double
parallelIntegration f a b n = do
  let h = (b - a) / fromIntegral n
      chunks = 4  -- 使用4个线程
      chunkSize = n `div` chunks
      
      chunkIntegral start = 
        let xs = [a + h * fromIntegral (start + i) | i <- [0..chunkSize-1]]
        in h * sum (map f xs)
      
  results <- mapM (forkIO . return . chunkIntegral) [0, chunkSize..n-chunkSize]
  return $ sum results

-- 并行计算示例
parallelComputationExample :: IO ()
parallelComputationExample = do
  let f x = x * x
      a = 0.0
      b = 1.0
      n = 1000000
      
  result <- parallelIntegration f a b n
  putStrLn $ "Parallel integration result: " ++ show result
```

## 📚 9. 总结与展望

### 9.1 数值计算的核心概念

1. **数值精度**：浮点数运算的精度控制
2. **数值稳定性**：算法的数值稳定性分析
3. **误差分析**：计算误差的定量分析
4. **算法优化**：提高计算效率的方法

### 9.2 Haskell数值计算的优势

1. **类型安全**：编译时类型检查
2. **高性能**：优化的数值计算库
3. **函数式编程**：清晰的算法表达
4. **并行支持**：内置并行计算能力

### 9.3 未来发展方向

1. **机器学习**：数值计算在ML中的应用
2. **量子计算**：量子算法的数值实现
3. **高性能计算**：大规模并行数值计算
4. **实时计算**：实时数值处理系统

---

**相关文档**：

- [函数式编程基础](../01-Basic-Concepts/001-Functional-Programming-Foundation.md)
- [递归和列表](../01-Basic-Concepts/003-Recursion-and-Lists.md)
- [算法实现](../07-Algorithms/001-Sorting-Algorithms.md)
- [线性代数](./002-Linear-Algebra.md)
