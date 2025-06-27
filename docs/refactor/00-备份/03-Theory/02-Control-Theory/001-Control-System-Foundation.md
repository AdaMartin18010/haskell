# 控制系统基础

## 📋 概述

控制理论是研究动态系统行为和控制策略的数学理论。本文档介绍控制系统的基础概念，包括动态系统建模、稳定性分析、可控性、可观性和反馈控制设计。

## 🎯 动态系统基础

### 定义 1.1 (动态系统)

动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

```haskell
-- 动态系统定义
data DynamicSystem a b c = DynamicSystem
    { stateSpace :: Set a
    , inputSpace :: Set b
    , outputSpace :: Set c
    , stateTransition :: a -> b -> a
    , outputFunction :: a -> c
    }

-- 连续时间系统
type ContinuousSystem = DynamicSystem (Vector Double) (Vector Double) (Vector Double)

-- 离散时间系统
type DiscreteSystem = DynamicSystem (Vector Double) (Vector Double) (Vector Double)

-- 系统示例：简单积分器
integratorSystem :: ContinuousSystem
integratorSystem = DynamicSystem
    { stateSpace = Set.fromList [Vector.fromList [x] | x <- [-10, -9.9..10]]
    , inputSpace = Set.fromList [Vector.fromList [u] | u <- [-5, -4.9..5]]
    , outputSpace = Set.fromList [Vector.fromList [y] | y <- [-10, -9.9..10]]
    , stateTransition = \x u -> x + u * 0.1  -- 简单积分
    , outputFunction = id
    }
```

### 定义 1.2 (连续时间系统)

连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

### 定义 1.3 (离散时间系统)

离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

```haskell
-- 连续时间系统模拟
simulateContinuous :: ContinuousSystem -> Vector Double -> [Vector Double] -> [Vector Double]
simulateContinuous sys x0 inputs = 
    let dt = 0.01  -- 时间步长
        step x u = x + (stateTransition sys x u) * dt
    in scanl step x0 inputs

-- 离散时间系统模拟
simulateDiscrete :: DiscreteSystem -> Vector Double -> [Vector Double] -> [Vector Double]
simulateDiscrete sys x0 inputs = 
    scanl (stateTransition sys) x0 inputs
```

## 🔧 线性系统

### 定义 1.4 (线性系统)

线性系统满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$

### 定义 1.5 (线性时不变系统)

线性时不变系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中 $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$, $D \in \mathbb{R}^{p \times m}$。

```haskell
-- 线性时不变系统
data LTISystem = LTISystem
    { matrixA :: Matrix Double
    , matrixB :: Matrix Double
    , matrixC :: Matrix Double
    , matrixD :: Matrix Double
    }

-- 线性系统状态转移
linearStateTransition :: LTISystem -> Vector Double -> Vector Double -> Vector Double
linearStateTransition sys x u = 
    let Ax = matrixA sys `multiply` x
        Bu = matrixB sys `multiply` u
    in Ax + Bu

-- 线性系统输出
linearOutput :: LTISystem -> Vector Double -> Vector Double
linearOutput sys x = 
    let Cx = matrixC sys `multiply` x
    in Cx

-- 示例：二阶系统
secondOrderSystem :: LTISystem
secondOrderSystem = LTISystem
    { matrixA = (2><2) [0, 1, -1, -0.5]  -- 阻尼振荡器
    , matrixB = (2><1) [0, 1]
    , matrixC = (1><2) [1, 0]
    , matrixD = (1><1) [0]
    }
```

### 定理 1.1 (线性系统解)

线性时不变系统的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过状态方程的积分：

1. 齐次方程 $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. 非齐次方程通过变分常数法求解
3. 利用卷积积分得到完整解

```haskell
-- 矩阵指数
matrixExponential :: Matrix Double -> Matrix Double
matrixExponential a = 
    let n = rows a
        identity = ident n
        terms = take 20 [identity, a, a^2, a^3, a^4, a^5, a^6, a^7, a^8, a^9, a^10, a^11, a^12, a^13, a^14, a^15, a^16, a^17, a^18, a^19]
        factorials = [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600, 6227020800, 87178291200, 1307674368000, 20922789888000, 355687428096000, 6402373705728000, 121645100408832000]
    in sum $ zipWith (\term fact -> term / fromIntegral fact) terms factorials

-- 线性系统解析解
linearSystemSolution :: LTISystem -> Vector Double -> [Vector Double] -> [Vector Double] -> [Vector Double]
linearSystemSolution sys x0 times inputs = 
    let dt = times !! 1 - times !! 0
        eAt = matrixExponential (matrixA sys * dt)
        convolution t = sum [eAt `multiply` (matrixB sys `multiply` u) * dt | (tau, u) <- zip times inputs, tau <= t]
    in [eAt `multiply` x0 + convolution t | t <- times]
```

## 📊 稳定性分析

### 定义 2.1 (平衡点)

状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0) = 0$。

### 定义 2.2 (李雅普诺夫稳定性)

平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

### 定义 2.3 (渐近稳定性)

平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

### 定理 2.1 (李雅普诺夫直接法)

如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：** 通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

```haskell
-- 李雅普诺夫函数
type LyapunovFunction = Vector Double -> Double

-- 李雅普诺夫稳定性检查
lyapunovStability :: LTISystem -> Vector Double -> LyapunovFunction -> Bool
lyapunovStability sys xe v = 
    let -- 检查条件1: V(xe) = 0
        condition1 = abs (v xe) < 1e-10
        
        -- 检查条件2: V(x) > 0 for x ≠ xe
        testPoints = [xe + Vector.fromList [dx, dy] | dx <- [-1, -0.5, 0.5, 1], dy <- [-1, -0.5, 0.5, 1]]
        condition2 = all (\x -> v x > 0) testPoints
        
        -- 检查条件3: V̇(x) ≤ 0 for x ≠ xe
        derivative x = 
            let dx = linearStateTransition sys x (Vector.fromList [0])  -- 零输入
                gradV = gradient v x
            in dot gradV dx
        condition3 = all (\x -> derivative x <= 0) testPoints
    in condition1 && condition2 && condition3

-- 二次李雅普诺夫函数
quadraticLyapunov :: Matrix Double -> LyapunovFunction
quadraticLyapunov p x = x `dot` (p `multiply` x)

-- 梯度计算（数值近似）
gradient :: (Vector Double -> Double) -> Vector Double -> Vector Double
gradient f x = 
    let h = 1e-6
        n = size x
        ei i = Vector.fromList [if i == j then 1 else 0 | j <- [0..n-1]]
    in Vector.fromList [(f (x + h * ei i) - f (x - h * ei i)) / (2 * h) | i <- [0..n-1]]
```

### 定理 2.2 (线性系统稳定性)

线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：** 通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

```haskell
-- 特征值计算
eigenvalues :: Matrix Double -> [Complex Double]
eigenvalues a = 
    let (eigenvals, _) = eig a
    in eigenvals

-- 线性系统稳定性检查
linearStability :: LTISystem -> Bool
linearStability sys = 
    let eigenvals = eigenvalues (matrixA sys)
    in all (\lambda -> realPart lambda < 0) eigenvals

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
        pad = replicate (n - length coeffs) 0
        padded = coeffs ++ pad
    in (n><n) [padded !! (i + j) | i <- [0..n-1], j <- [0..n-1]]
```

## 🔍 可控性和可观性

### 定义 3.1 (可控性)

系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

### 定义 3.2 (可控性矩阵)

线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

### 定理 3.1 (可控性判据)

线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：** 通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

```haskell
-- 可控性矩阵
controllabilityMatrix :: LTISystem -> Matrix Double
controllabilityMatrix sys = 
    let a = matrixA sys
        b = matrixB sys
        n = rows a
        powers = take n [a^i | i <- [0..]]
    in hcat [powers !! i `multiply` b | i <- [0..n-1]]

-- 可控性检查
isControllable :: LTISystem -> Bool
isControllable sys = 
    let c = controllabilityMatrix sys
        rank = rank c
        n = rows (matrixA sys)
    in rank == n

-- 矩阵秩计算
rank :: Matrix Double -> Int
rank a = 
    let (u, s, _) = svd a
        singularValues = takeDiag s
        threshold = 1e-10
    in length $ filter (> threshold) singularValues
```

### 定义 3.3 (可观性)

系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

### 定义 3.4 (可观性矩阵)

线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

### 定理 3.2 (可观性判据)

线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：** 通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

```haskell
-- 可观性矩阵
observabilityMatrix :: LTISystem -> Matrix Double
observabilityMatrix sys = 
    let a = matrixA sys
        c = matrixC sys
        n = rows a
        powers = take n [a^i | i <- [0..]]
    in vcat [c `multiply` (powers !! i) | i <- [0..n-1]]

-- 可观性检查
isObservable :: LTISystem -> Bool
isObservable sys = 
    let o = observabilityMatrix sys
        rank = rank o
        n = rows (matrixA sys)
    in rank == n
```

## 📈 反馈控制

### 定义 4.1 (状态反馈)

状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

### 定理 4.1 (极点配置)

如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：** 通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

```haskell
-- 极点配置
polePlacement :: LTISystem -> [Complex Double] -> Matrix Double
polePlacement sys desiredPoles = 
    let a = matrixA sys
        b = matrixB sys
        n = rows a
        
        -- 可控性标准形变换
        controllableForm = toControllableForm a b
        transformation = getTransformation a b
        
        -- 标准形下的极点配置
        kStandard = placePolesStandard controllableForm desiredPoles
        
        -- 变换回原坐标系
    in kStandard `multiply` transformation

-- 可控性标准形
toControllableForm :: Matrix Double -> Matrix Double -> Matrix Double
toControllableForm a b = 
    let c = controllabilityMatrix (LTISystem a b (ident (rows a)) (ident (cols b)))
        t = inv c
    in t `multiply` a `multiply` inv t

-- 标准形极点配置
placePolesStandard :: Matrix Double -> [Complex Double] -> Matrix Double
placePolesStandard a desiredPoles = 
    let n = rows a
        characteristicPoly = product [(\s -> s - lambda) | lambda <- desiredPoles]
        coeffs = polynomialCoefficients characteristicPoly
        k = Vector.fromList [coeffs !! i | i <- [0..n-1]]
    in (1><n) (toList k)
```

### 定义 4.2 (输出反馈)

输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

### 定理 4.2 (输出反馈限制)

输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：** 通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 定义 4.3 (全维观测器)

全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

### 定理 4.3 (观测器极点配置)

如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：** 通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器设计等价于对偶系统的状态反馈设计
3. 利用极点配置定理得到观测器增益

```haskell
-- 观测器设计
observerDesign :: LTISystem -> [Complex Double] -> Matrix Double
observerDesign sys observerPoles = 
    let a = matrixA sys
        c = matrixC sys
        
        -- 对偶系统
        aDual = tr a
        bDual = tr c
        
        -- 对偶系统的状态反馈设计
        kDual = polePlacement (LTISystem aDual bDual (ident (rows aDual)) (ident (cols bDual))) observerPoles
        
        -- 观测器增益
    in tr kDual

-- 观测器系统
observerSystem :: LTISystem -> Matrix Double -> LTISystem
observerSystem sys l = 
    let a = matrixA sys
        b = matrixB sys
        c = matrixC sys
        d = matrixD sys
        
        -- 观测器动态
        aObs = a - l `multiply` c
        bObs = b - l `multiply` d
        cObs = c
        dObs = d
    in LTISystem aObs bObs cObs dObs
```

## 🔗 相关链接

### 理论基础

- [系统理论](../01-System-Theory/001-System-Dynamics.md)
- [线性代数](../02-Formal-Science/01-Mathematics/001-Linear-Algebra.md)
- [微分方程](../02-Formal-Science/07-Analysis/001-Differential-Equations.md)

### 高级控制理论

- [非线性控制](./002-Nonlinear-Control.md)
- [鲁棒控制](./003-Robust-Control.md)
- [自适应控制](./004-Adaptive-Control.md)

### 实际应用

- [机器人控制](../haskell/14-Real-World-Applications/001-Robotics-Control.md)
- [过程控制](../haskell/14-Real-World-Applications/002-Process-Control.md)
- [飞行控制](../haskell/14-Real-World-Applications/003-Flight-Control.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
