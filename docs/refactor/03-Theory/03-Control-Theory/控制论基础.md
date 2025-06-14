# 控制论基础 (Control Theory Foundation)

## 📋 目录

1. [系统基础](#1-系统基础)
2. [稳定性分析](#2-稳定性分析)
3. [可控性和可观性](#3-可控性和可观性)
4. [反馈控制](#4-反馈控制)
5. [最优控制](#5-最优控制)
6. [鲁棒控制](#6-鲁棒控制)
7. [自适应控制](#7-自适应控制)
8. [非线性控制](#8-非线性控制)

## 1. 系统基础

### 1.1 动态系统定义

**定义 1.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间  
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

**Haskell实现：**

```haskell
-- 动态系统类型定义
data DynamicSystem a b c = DynamicSystem
  { stateSpace :: [a]           -- 状态空间
  , inputSpace :: [b]           -- 输入空间
  , outputSpace :: [c]          -- 输出空间
  , stateTransition :: a -> b -> a  -- 状态转移函数
  , outputFunction :: a -> c        -- 输出函数
  }

-- 连续时间系统
data ContinuousSystem = ContinuousSystem
  { stateDim :: Int
  , inputDim :: Int
  , outputDim :: Int
  , stateMatrix :: Matrix Double
  , inputMatrix :: Matrix Double
  , outputMatrix :: Matrix Double
  , feedthroughMatrix :: Matrix Double
  }

-- 离散时间系统
data DiscreteSystem = DiscreteSystem
  { stateDim :: Int
  , inputDim :: Int
  , outputDim :: Int
  , stateMatrix :: Matrix Double
  , inputMatrix :: Matrix Double
  , outputMatrix :: Matrix Double
  , feedthroughMatrix :: Matrix Double
  }
```

**定义 1.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

**定义 1.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

### 1.2 线性系统

**定义 1.4 (线性系统)**
线性系统满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$

**定义 1.5 (线性时不变系统)**
线性时不变系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中 $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$, $D \in \mathbb{R}^{p \times m}$。

**Haskell实现：**

```haskell
-- 线性时不变系统
data LTISystem = LTISystem
  { aMatrix :: Matrix Double  -- 状态矩阵
  , bMatrix :: Matrix Double  -- 输入矩阵
  , cMatrix :: Matrix Double  -- 输出矩阵
  , dMatrix :: Matrix Double  -- 前馈矩阵
  }

-- 系统响应计算
systemResponse :: LTISystem -> Vector Double -> Vector Double -> Double -> Vector Double
systemResponse sys x0 u t = 
  let A = aMatrix sys
      B = bMatrix sys
      C = cMatrix sys
      D = dMatrix sys
      -- 状态响应
      x = matrixExponential A `multiply` x0 + 
          integrate (\tau -> matrixExponential A `multiply` B `multiply` u) 0 t
      -- 输出响应
      y = C `multiply` x + D `multiply` u
  in y

-- 矩阵指数计算
matrixExponential :: Matrix Double -> Matrix Double
matrixExponential A = 
  let n = rows A
      I = identity n
      expA = foldl' (\acc k -> acc + (A `power` k) `scale` (1 / fromIntegral (factorial k))) I [1..10]
  in expA
```

**定理 1.1 (线性系统解)**
线性时不变系统的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过状态方程的积分：

1. 齐次方程 $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. 非齐次方程通过变分常数法求解
3. 利用卷积积分得到完整解

## 2. 稳定性分析

### 2.1 李雅普诺夫稳定性

**定义 2.1 (平衡点)**
状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0) = 0$。

**定义 2.2 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 2.3 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**Haskell实现：**

```haskell
-- 李雅普诺夫函数类型
type LyapunovFunction a = a -> Double

-- 稳定性分析
data StabilityResult = 
    Stable
  | AsymptoticallyStable
  | Unstable
  | MarginallyStable

-- 李雅普诺夫稳定性检查
lyapunovStability :: (VectorSpace a, Floating (Scalar a)) 
                  => LyapunovFunction a 
                  -> (a -> a)  -- 系统动态
                  -> a         -- 平衡点
                  -> StabilityResult
lyapunovStability V f xe = 
  let -- 检查李雅普诺夫函数条件
      vAtEquilibrium = V xe
      isPositiveDefinite = all (\x -> V x > 0) (neighborhood xe)
      isNegativeSemidefinite = all (\x -> derivative V f x <= 0) (neighborhood xe)
      isNegativeDefinite = all (\x -> derivative V f x < 0) (neighborhood xe)
  in if vAtEquilibrium == 0 && isPositiveDefinite
     then if isNegativeDefinite
          then AsymptoticallyStable
          else if isNegativeSemidefinite
               then Stable
               else Unstable
     else Unstable

-- 李雅普诺夫函数导数
derivative :: (VectorSpace a, Floating (Scalar a)) 
           => LyapunovFunction a -> (a -> a) -> a -> Scalar a
derivative V f x = 
  let h = 1e-6
      xPlusH = x + scale h (f x)
      xMinusH = x - scale h (f x)
  in (V xPlusH - V xMinusH) / (2 * h)
```

**定理 2.1 (李雅普诺夫直接法)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：** 通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

### 2.2 线性系统稳定性

**定理 2.2 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：** 通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**Haskell实现：**

```haskell
-- 线性系统稳定性分析
linearSystemStability :: Matrix Double -> StabilityResult
linearSystemStability A = 
  let eigenvalues = eigenValues A
      realParts = map realPart eigenvalues
      maxRealPart = maximum realParts
  in if maxRealPart < 0
     then AsymptoticallyStable
     else if maxRealPart == 0
          then MarginallyStable
          else Unstable

-- 赫尔维茨判据
hurwitzCriterion :: [Double] -> Bool
hurwitzCriterion coeffs = 
  let n = length coeffs - 1
      hurwitzMatrix = buildHurwitzMatrix coeffs
      minors = [determinant (submatrix hurwitzMatrix i) | i <- [1..n]]
  in all (> 0) minors

-- 构建赫尔维茨矩阵
buildHurwitzMatrix :: [Double] -> Matrix Double
buildHurwitzMatrix coeffs = 
  let n = length coeffs - 1
      matrix = matrix n n $ \(i,j) -> 
        if j <= i && i + j <= n
        then coeffs !! (n - i - j)
        else 0
  in matrix
```

## 3. 可控性和可观性

### 3.1 可控性

**定义 3.1 (可控性)**
系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 3.2 (可控性矩阵)**
线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**Haskell实现：**

```haskell
-- 可控性矩阵
controllabilityMatrix :: Matrix Double -> Matrix Double -> Matrix Double
controllabilityMatrix a b = 
  let n = rows a
      powers = [a `power` i | i <- [0..n-1]]
      terms = map (\aPow -> aPow `multiply` b) powers
  in horizontalConcat terms

-- 可控性检查
isControllable :: Matrix Double -> Matrix Double -> Bool
isControllable a b = 
  let cMatrix = controllabilityMatrix a b
      rank = matrixRank cMatrix
      n = rows a
  in rank == n

-- 矩阵幂运算
power :: Matrix Double -> Int -> Matrix Double
power _ 0 = identity (rows a)
power a 1 = a
power a n = 
  if even n
  then let half = power a (n `div` 2) in half `multiply` half
  else a `multiply` power a (n-1)
```

**定理 3.1 (可控性判据)**
线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：** 通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

### 3.2 可观性

**定义 3.3 (可观性)**
系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 3.4 (可观性矩阵)**
线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**Haskell实现：**

```haskell
-- 可观性矩阵
observabilityMatrix :: Matrix Double -> Matrix Double -> Matrix Double
observabilityMatrix a c = 
  let n = rows a
      powers = [a `power` i | i <- [0..n-1]]
      terms = map (\aPow -> c `multiply` aPow) powers
  in verticalConcat terms

-- 可观性检查
isObservable :: Matrix Double -> Matrix Double -> Bool
isObservable a c = 
  let oMatrix = observabilityMatrix a c
      rank = matrixRank oMatrix
      n = rows a
  in rank == n
```

**定理 3.2 (可观性判据)**
线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：** 通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

## 4. 反馈控制

### 4.1 状态反馈

**定义 4.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**Haskell实现：**

```haskell
-- 状态反馈控制器
data StateFeedbackController = StateFeedbackController
  { feedbackGain :: Matrix Double
  , referenceInput :: Double -> Vector Double
  }

-- 状态反馈控制律
stateFeedback :: StateFeedbackController -> Vector Double -> Double -> Vector Double
stateFeedback controller x t = 
  let K = feedbackGain controller
      r = referenceInput controller t
  in -K `multiply` x + r

-- 闭环系统
closedLoopSystem :: LTISystem -> StateFeedbackController -> LTISystem
closedLoopSystem sys controller = 
  let A = aMatrix sys
      B = bMatrix sys
      C = cMatrix sys
      D = dMatrix sys
      K = feedbackGain controller
      -- 闭环状态矩阵
      Acl = A - B `multiply` K
  in LTISystem Acl B C D
```

**定理 4.1 (极点配置)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：** 通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

**Haskell实现：**

```haskell
-- 极点配置算法
polePlacement :: Matrix Double -> Matrix Double -> [Complex Double] -> Matrix Double
polePlacement a b desiredPoles = 
  let -- 转换为可控标准形
      controllableForm = toControllableForm a b
      -- 在标准形下配置极点
      kStandard = placePoles controllableForm desiredPoles
      -- 变换回原坐标系
      transformation = getTransformation a b
  in kStandard `multiply` transformation

-- 可控标准形转换
toControllableForm :: Matrix Double -> Matrix Double -> (Matrix Double, Matrix Double)
toControllableForm a b = 
  let n = rows a
      cMatrix = controllabilityMatrix a b
      -- 可控性矩阵的逆
      cInv = inverse cMatrix
      -- 变换矩阵
      t = cInv
      -- 标准形矩阵
      aStandard = t `multiply` a `multiply` inverse t
      bStandard = t `multiply` b
  in (aStandard, bStandard)
```

### 4.2 输出反馈

**定义 4.2 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

**定理 4.2 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：** 通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 4.3 观测器设计

**定义 4.3 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**Haskell实现：**

```haskell
-- 全维观测器
data FullOrderObserver = FullOrderObserver
  { observerGain :: Matrix Double
  , estimatedState :: Vector Double
  }

-- 观测器动态
observerDynamics :: LTISystem -> FullOrderObserver -> Vector Double -> Vector Double -> Vector Double
observerDynamics sys observer u y = 
  let A = aMatrix sys
      B = bMatrix sys
      C = cMatrix sys
      L = observerGain observer
      xHat = estimatedState observer
      -- 观测器方程
      xHatDot = A `multiply` xHat + B `multiply` u + L `multiply` (y - C `multiply` xHat)
  in xHatDot

-- 观测器极点配置
observerPolePlacement :: Matrix Double -> Matrix Double -> [Complex Double] -> Matrix Double
observerPolePlacement a c desiredPoles = 
  let -- 利用可观性对偶性
      aDual = transpose a
      cDual = transpose c
      -- 对偶系统的极点配置
      lDual = polePlacement aDual cDual desiredPoles
      -- 观测器增益
      l = transpose lDual
  in l
```

**定理 4.3 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：** 通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器极点配置等价于对偶系统的极点配置
3. 利用极点配置定理得到观测器增益

## 5. 最优控制

### 5.1 线性二次型调节器

**定义 5.1 (LQR问题)**
线性二次型调节器问题：
$$\min_{u(t)} \int_0^\infty [x^T(t)Qx(t) + u^T(t)Ru(t)]dt$$

约束：$\dot{x}(t) = Ax(t) + Bu(t)$

其中 $Q \geq 0$, $R > 0$ 是权重矩阵。

**Haskell实现：**

```haskell
-- LQR控制器
data LQRController = LQRController
  { lqrGain :: Matrix Double
  , costMatrices :: (Matrix Double, Matrix Double)
  }

-- 代数黎卡提方程求解
algebraicRiccatiEquation :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
algebraicRiccatiEquation a b q r = 
  let -- 哈密顿矩阵
      h = matrix (2*n) (2*n) $ \(i,j) ->
        if i <= n && j <= n
        then a `atIndex` (i-1, j-1)
        else if i <= n && j > n
             then -(b `multiply` inverse r `multiply` transpose b) `atIndex` (i-1, j-n-1)
             else if i > n && j <= n
                  then -q `atIndex` (i-n-1, j-1)
                  else -transpose a `atIndex` (i-n-1, j-n-1)
      where n = rows a
      -- 特征值分解
      (eigenvals, eigenvecs) = eigenDecomposition h
      -- 稳定子空间
      stableIndices = findIndices (\lambda -> realPart lambda < 0) eigenvals
      stableEigenvecs = submatrix eigenvecs stableIndices
      -- 黎卡提方程解
      p = stableEigenvecs `multiply` inverse (submatrix stableEigenvecs [0..n-1])
  in p

-- LQR增益计算
lqrGain :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
lqrGain a b q r = 
  let p = algebraicRiccatiEquation a b q r
  in inverse r `multiply` transpose b `multiply` p
```

**定理 5.1 (LQR最优性)**
如果系统 $(A, B)$ 可控且 $(A, Q^{1/2})$ 可观，则LQR控制器是最优的。

**证明：** 通过变分法：

1. 构造哈密顿函数
2. 应用最优性必要条件
3. 得到代数黎卡提方程
4. 验证充分条件

### 5.2 模型预测控制

**定义 5.2 (MPC问题)**
模型预测控制问题：
$$\min_{u(k), \ldots, u(k+N-1)} \sum_{i=0}^{N-1} [x^T(k+i)Qx(k+i) + u^T(k+i)Ru(k+i)]$$

约束：$x(k+i+1) = Ax(k+i) + Bu(k+i)$

**Haskell实现：**

```haskell
-- MPC控制器
data MPCController = MPCController
  { predictionHorizon :: Int
  , costMatrices :: (Matrix Double, Matrix Double)
  , constraints :: [Constraint]
  }

-- MPC优化问题求解
mpcOptimization :: MPCController -> Vector Double -> Vector Double
mpcOptimization controller x0 = 
  let N = predictionHorizon controller
      (Q, R) = costMatrices controller
      constraints = constraints controller
      -- 构建预测模型
      predictionModel = buildPredictionModel N
      -- 构建成本函数
      costFunction = buildCostFunction Q R N
      -- 求解优化问题
      optimalInput = solveQP costFunction constraints predictionModel x0
  in optimalInput

-- 预测模型构建
buildPredictionModel :: Int -> Matrix Double
buildPredictionModel N = 
  let -- 状态预测矩阵
      stateMatrix = matrix (N*n) n $ \(i,j) ->
        if i <= n
        then if i == j then 1 else 0
        else a `power` ((i-1) `div` n) `atIndex` ((i-1) `mod` n, j-1)
      -- 输入预测矩阵
      inputMatrix = matrix (N*n) (N*m) $ \(i,j) ->
        let blockRow = i `div` n
            blockCol = j `div` m
            rowInBlock = i `mod` n
            colInBlock = j `mod` m
        in if blockRow >= blockCol
           then (a `power` (blockRow - blockCol) `multiply` b) `atIndex` (rowInBlock, colInBlock)
           else 0
  in (stateMatrix, inputMatrix)
```

## 6. 鲁棒控制

### 6.1 H∞控制

**定义 6.1 (H∞控制问题)**
H∞控制问题：
$$\min_{K} \|T_{zw}\|_\infty$$

其中 $T_{zw}$ 是从干扰 $w$ 到性能输出 $z$ 的闭环传递函数。

**Haskell实现：**

```haskell
-- H∞控制器
data HInfController = HInfController
  { hinfGain :: Matrix Double
  , performanceLevel :: Double
  }

-- H∞范数计算
hinfNorm :: Matrix (Complex Double) -> Double
hinfNorm g = 
  let -- 频率响应
      frequencies = [10^((-3 + i*0.1)) | i <- [0..60]]
      -- 奇异值
      singularValues = map (\w -> maximumSingularValue (g w)) frequencies
      -- H∞范数
      hinfNorm = maximum singularValues
  in hinfNorm

-- 最大奇异值
maximumSingularValue :: Matrix (Complex Double) -> Double
maximumSingularValue m = 
  let -- SVD分解
      (u, s, v) = svd m
      -- 最大奇异值
      maxSigma = maximum (map magnitude s)
  in maxSigma
```

### 6.2 μ综合

**定义 6.2 (μ综合问题)**
μ综合问题：
$$\min_{K} \mu_\Delta(T_{zw})$$

其中 $\mu_\Delta$ 是结构奇异值。

**Haskell实现：**

```haskell
-- μ综合控制器
data MuSynthesisController = MuSynthesisController
  { muGain :: Matrix Double
  , uncertaintyStructure :: UncertaintyStructure
  }

-- 结构奇异值计算
structuredSingularValue :: Matrix (Complex Double) -> UncertaintyStructure -> Double
structuredSingularValue m delta = 
  let -- D-K迭代
      (dOpt, kOpt) = dkIteration m delta
      -- μ值
      muValue = 1 / maximumSingularValue (dOpt `multiply` m `multiply` inverse dOpt)
  in muValue

-- D-K迭代
dkIteration :: Matrix (Complex Double) -> UncertaintyStructure -> (Matrix Double, Matrix Double)
dkIteration m delta = 
  let -- D步：固定K，优化D
      dStep m k = optimizeD m k delta
      -- K步：固定D，优化K
      kStep m d = optimizeK m d
      -- 迭代收敛
      iterate dk = 
        let (d, k) = dk
            dNew = dStep m k
            kNew = kStep m dNew
        in if convergenceTest (d, k) (dNew, kNew)
           then (dNew, kNew)
           else iterate (dNew, kNew)
  in iterate (identity (rows m), zero (rows m, cols m))
```

## 7. 自适应控制

### 7.1 模型参考自适应控制

**定义 7.1 (MRAC问题)**
模型参考自适应控制问题：
$$\min_{\theta(t)} \|y(t) - y_m(t)\|^2$$

其中 $y_m(t)$ 是参考模型输出。

**Haskell实现：**

```haskell
-- MRAC控制器
data MRACController = MRACController
  { adaptiveGains :: Vector Double
  , referenceModel :: LTISystem
  , adaptationRate :: Double
  }

-- 自适应律
adaptiveLaw :: MRACController -> Vector Double -> Vector Double -> Vector Double -> Vector Double
adaptiveLaw controller x e phi = 
  let gamma = adaptationRate controller
      theta = adaptiveGains controller
      -- 梯度自适应律
      thetaDot = -gamma `scale` (phi `multiply` e)
  in thetaDot

-- 参考模型跟踪
referenceModelTracking :: MRACController -> Vector Double -> Vector Double -> Vector Double
referenceModelTracking controller x u = 
  let refModel = referenceModel controller
      -- 参考模型输出
      ym = cMatrix refModel `multiply` x
      -- 实际输出
      y = cMatrix refModel `multiply` x
      -- 跟踪误差
      e = y - ym
  in e
```

### 7.2 自校正控制

**定义 7.2 (自校正控制)**
自校正控制通过在线参数估计和控制器设计实现自适应。

**Haskell实现：**

```haskell
-- 自校正控制器
data SelfTuningController = SelfTuningController
  { parameterEstimator :: ParameterEstimator
  , controllerDesigner :: ControllerDesigner
  , estimatedParameters :: Vector Double
  }

-- 递归最小二乘估计
recursiveLeastSquares :: Vector Double -> Vector Double -> Vector Double -> Vector Double -> (Vector Double, Matrix Double)
recursiveLeastSquares theta phi y p = 
  let -- 预测误差
      e = y - transpose phi `multiply` theta
      -- 增益向量
      k = p `multiply` phi `multiply` inverse (1 + transpose phi `multiply` p `multiply` phi)
      -- 参数更新
      thetaNew = theta + k `scale` e
      -- 协方差更新
      pNew = (identity (length theta) - k `outer` phi) `multiply` p
  in (thetaNew, pNew)
```

## 8. 非线性控制

### 8.1 反馈线性化

**定义 8.1 (反馈线性化)**
通过状态反馈将非线性系统转换为线性系统。

**Haskell实现：**

```haskell
-- 反馈线性化控制器
data FeedbackLinearizationController = FeedbackLinearizationController
  { nonlinearSystem :: NonlinearSystem
  , linearizingTransformation :: Vector Double -> Vector Double
  , linearController :: LTISystem
  }

-- 相对度计算
relativeDegree :: NonlinearSystem -> Int
relativeDegree sys = 
  let -- 计算李导数
      lieDerivatives = computeLieDerivatives sys
      -- 找到第一个非零李导数
      firstNonZero = findIndex (/= 0) lieDerivatives
  in maybe 0 (+1) firstNonZero

-- 反馈线性化变换
feedbackLinearizationTransform :: NonlinearSystem -> (Vector Double -> Vector Double, Vector Double -> Vector Double)
feedbackLinearizationTransform sys = 
  let r = relativeDegree sys
      -- 坐标变换
      z = coordinateTransformation sys r
      -- 控制变换
      v = controlTransformation sys r
  in (z, v)
```

### 8.2 滑模控制

**定义 8.2 (滑模控制)**
滑模控制通过设计滑模面实现鲁棒控制。

**Haskell实现：**

```haskell
-- 滑模控制器
data SlidingModeController = SlidingModeController
  { slidingSurface :: Vector Double -> Double
  , controlGain :: Double
  , boundaryLayer :: Double
  }

-- 滑模面设计
slidingSurface :: Vector Double -> Vector Double -> Double
slidingSurface lambda x = 
  let -- 滑模面：s = λ₁x₁ + λ₂x₂ + ... + λₙ₋₁xₙ₋₁ + xₙ
      s = sum (zipWith (*) lambda (init (toList x))) + last (toList x)
  in s

-- 滑模控制律
slidingModeControl :: SlidingModeController -> Vector Double -> Vector Double -> Vector Double
slidingModeControl controller x xDot = 
  let s = slidingSurface controller x
      lambda = slidingSurface controller
      k = controlGain controller
      phi = boundaryLayer controller
      -- 等效控制
      uEq = computeEquivalentControl x xDot lambda
      -- 切换控制
      uSw = -k * signum s
      -- 边界层平滑
      uSmooth = if abs s < phi
                then -k * s / phi
                else uSw
  in uEq + uSmooth
```

## 📚 参考文献

1. Khalil, H. K. (2002). Nonlinear Systems. Prentice Hall.
2. Sontag, E. D. (1998). Mathematical Control Theory. Springer.
3. Zhou, K., & Doyle, J. C. (1998). Essentials of Robust Control. Prentice Hall.
4. Åström, K. J., & Wittenmark, B. (2008). Adaptive Control. Dover Publications.
5. Slotine, J. J. E., & Li, W. (1991). Applied Nonlinear Control. Prentice Hall.

## 🔗 相关链接

- [系统理论基础](../02-System-Theory/系统理论基础.md)
- [分布式系统理论](../04-Distributed-Systems-Theory/分布式系统理论基础.md)
- [时态逻辑控制](../05-Temporal-Logic-Control/时态逻辑控制基础.md)
- [Petri网理论](../06-Petri-Net-Theory/Petri网理论基础.md)

---

*本文档提供了控制论的完整理论基础，包含形式化定义、Haskell实现和数学证明，为后续的具体应用提供理论支撑。*
