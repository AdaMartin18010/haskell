# 系统动力学基础

## 概述

系统动力学是控制论的基础，研究动态系统的行为规律和数学描述。本文档建立系统动力学的形式化理论框架，包括系统定义、状态方程、动态行为分析等核心概念。

## 1. 动态系统定义

### 1.1 基本定义

**定义 1.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间  
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

**Haskell实现**：

```haskell
-- 动态系统类型
data DynamicSystem a b c = DynamicSystem {
    stateSpace :: [a],           -- 状态空间
    inputSpace :: [b],           -- 输入空间
    outputSpace :: [c],          -- 输出空间
    stateTransition :: a -> b -> a,  -- 状态转移函数
    outputFunction :: a -> c         -- 输出函数
}

-- 系统状态
data SystemState a = SystemState {
    currentState :: a,
    time :: Double
}

-- 系统输入
data SystemInput b = SystemInput {
    inputValue :: b,
    inputTime :: Double
}
```

### 1.2 连续时间系统

**定义 1.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

其中 $t \in \mathbb{R}$ 是连续时间变量。

**Haskell实现**：

```haskell
-- 连续时间系统
data ContinuousSystem a b c = ContinuousSystem {
    stateEquation :: a -> b -> Vector Double,  -- 状态方程右端
    outputEquation :: a -> c,                  -- 输出方程
    timeDomain :: (Double, Double)             -- 时间域
}

-- 数值积分求解器
class ODESolver where
    solveODE :: (a -> b -> Vector Double) -> a -> [b] -> [Double] -> [a]
    
-- 欧拉方法
eulerMethod :: (a -> b -> Vector Double) -> a -> b -> Double -> a
eulerMethod f x u dt = x + (f x u * dt)

-- 四阶龙格库塔方法
rk4Method :: (a -> b -> Vector Double) -> a -> b -> Double -> a
rk4Method f x u dt = 
    let k1 = f x u
        k2 = f (x + k1 * (dt/2)) u
        k3 = f (x + k2 * (dt/2)) u
        k4 = f (x + k3 * dt) u
    in x + (k1 + 2*k2 + 2*k3 + k4) * (dt/6)
```

### 1.3 离散时间系统

**定义 1.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

其中 $k \in \mathbb{Z}$ 是离散时间变量。

**Haskell实现**：

```haskell
-- 离散时间系统
data DiscreteSystem a b c = DiscreteSystem {
    discreteStateEquation :: a -> b -> a,  -- 离散状态方程
    discreteOutputEquation :: a -> c,      -- 离散输出方程
    samplingTime :: Double                 -- 采样时间
}

-- 离散时间仿真
simulateDiscrete :: DiscreteSystem a b c -> a -> [b] -> [a]
simulateDiscrete sys x0 inputs = 
    scanl (\x u -> discreteStateEquation sys x u) x0 inputs
```

## 2. 线性系统理论

### 2.1 线性系统定义

**定义 2.1 (线性系统)**
系统 $\Sigma$ 是线性的，如果满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$
$$h(\alpha x_1 + \beta x_2) = \alpha h(x_1) + \beta h(x_2)$$

**定义 2.2 (线性时不变系统)**
线性时不变系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中：

- $A \in \mathbb{R}^{n \times n}$ 是系统矩阵
- $B \in \mathbb{R}^{n \times m}$ 是输入矩阵
- $C \in \mathbb{R}^{p \times n}$ 是输出矩阵
- $D \in \mathbb{R}^{p \times m}$ 是直接传递矩阵

**Haskell实现**：

```haskell
-- 线性时不变系统
data LinearSystem = LinearSystem {
    systemMatrix :: Matrix Double,      -- A矩阵
    inputMatrix :: Matrix Double,       -- B矩阵
    outputMatrix :: Matrix Double,      -- C矩阵
    directMatrix :: Matrix Double       -- D矩阵
}

-- 线性系统状态方程
linearStateEquation :: LinearSystem -> Vector Double -> Vector Double -> Vector Double
linearStateEquation sys x u = 
    systemMatrix sys `multiply` x + inputMatrix sys `multiply` u

-- 线性系统输出方程
linearOutputEquation :: LinearSystem -> Vector Double -> Vector Double -> Vector Double
linearOutputEquation sys x u = 
    outputMatrix sys `multiply` x + directMatrix sys `multiply` u
```

### 2.2 线性系统解

**定理 2.1 (线性系统解)**
线性时不变系统 $\dot{x} = Ax + Bu$ 的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明**：

1. 齐次方程 $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. 非齐次方程通过变分常数法求解
3. 利用卷积积分得到完整解

**Haskell实现**：

```haskell
-- 矩阵指数
matrixExponential :: Matrix Double -> Matrix Double
matrixExponential a = 
    let n = rows a
        identity = identityMatrix n
        series = scanl (\acc k -> acc + (a^k) / fromIntegral (factorial k)) identity [1..20]
    in last series

-- 线性系统解析解
linearSystemSolution :: LinearSystem -> Vector Double -> (Double -> Vector Double) -> Double -> Vector Double
linearSystemSolution sys x0 u t = 
    let eAt = matrixExponential (systemMatrix sys * t)
        homogeneous = eAt `multiply` x0
        convolution = integrateConvolution sys u t
    in homogeneous + convolution

-- 卷积积分
integrateConvolution :: LinearSystem -> (Double -> Vector Double) -> Double -> Vector Double
integrateConvolution sys u t = 
    let integrand tau = 
            let eA_tau = matrixExponential (systemMatrix sys * (t - tau))
            in eA_tau `multiply` (inputMatrix sys `multiply` u tau)
    in numericalIntegral integrand 0 t
```

## 3. 系统动态行为

### 3.1 平衡点分析

**定义 3.1 (平衡点)**
状态 $x_e \in X$ 是系统 $\Sigma$ 的平衡点，如果 $f(x_e, 0) = 0$。

**定义 3.2 (平衡点分类)**:

- **稳定平衡点**：系统在平衡点附近保持稳定
- **不稳定平衡点**：系统在平衡点附近发散
- **鞍点**：某些方向稳定，某些方向不稳定

**Haskell实现**：

```haskell
-- 平衡点
data EquilibriumPoint a = EquilibriumPoint {
    equilibriumState :: a,
    stabilityType :: StabilityType
}

data StabilityType = 
    Stable | 
    Unstable | 
    Saddle | 
    Center

-- 寻找平衡点
findEquilibriumPoints :: (a -> b -> a) -> [a] -> [a]
findEquilibriumPoints f stateSpace = 
    filter (\x -> norm (f x zeroInput) < epsilon) stateSpace
    where
        epsilon = 1e-10
        zeroInput = -- 零输入定义
```

### 3.2 相空间分析

**定义 3.3 (相空间)**
相空间是系统所有可能状态的集合，每个状态对应相空间中的一个点。

**定义 3.4 (相轨迹)**
相轨迹是系统状态在相空间中的演化路径。

**Haskell实现**：

```haskell
-- 相空间
data PhaseSpace a = PhaseSpace {
    states :: [a],
    trajectories :: [Trajectory a]
}

data Trajectory a = Trajectory {
    initialState :: a,
    timePoints :: [Double],
    statePoints :: [a]
}

-- 生成相轨迹
generateTrajectory :: (a -> b -> a) -> a -> [b] -> [Double] -> Trajectory a
generateTrajectory f x0 inputs times = 
    let states = scanl (\x (u, t) -> f x u) x0 (zip inputs times)
    in Trajectory x0 times states
```

## 4. 系统响应特性

### 4.1 阶跃响应

**定义 4.1 (阶跃响应)**
系统对单位阶跃输入的响应称为阶跃响应。

**Haskell实现**：

```haskell
-- 阶跃响应
stepResponse :: LinearSystem -> Vector Double -> Double -> [Vector Double]
stepResponse sys x0 finalTime = 
    let timePoints = [0, dt..finalTime]
        stepInput = replicate (length timePoints) (vector [1.0])
        states = simulateLinearSystem sys x0 stepInput timePoints
    in map (linearOutputEquation sys) states stepInput
```

### 4.2 脉冲响应

**定义 4.2 (脉冲响应)**
系统对单位脉冲输入的响应称为脉冲响应。

**Haskell实现**：

```haskell
-- 脉冲响应
impulseResponse :: LinearSystem -> Vector Double -> Double -> [Vector Double]
impulseResponse sys x0 finalTime = 
    let timePoints = [0, dt..finalTime]
        impulseInput = [vector [1.0/dt]] ++ replicate (length timePoints - 1) (vector [0.0])
        states = simulateLinearSystem sys x0 impulseInput timePoints
    in map (linearOutputEquation sys) states impulseInput
```

## 5. 系统仿真

### 5.1 数值仿真

**Haskell实现**：

```haskell
-- 系统仿真器
class SystemSimulator sys where
    simulate :: sys -> a -> [b] -> [Double] -> [a]
    
-- 线性系统仿真
simulateLinearSystem :: LinearSystem -> Vector Double -> [Vector Double] -> [Double] -> [Vector Double]
simulateLinearSystem sys x0 inputs times = 
    let dt = times !! 1 - times !! 0
        step x u = x + (linearStateEquation sys x u) * dt
    in scanl step x0 inputs

-- 非线性系统仿真
simulateNonlinearSystem :: (a -> b -> a) -> a -> [b] -> [Double] -> [a]
simulateNonlinearSystem f x0 inputs times = 
    let dt = times !! 1 - times !! 0
        step x u = rk4Method f x u dt
    in scanl step x0 inputs
```

### 5.2 性能分析

**Haskell实现**：

```haskell
-- 系统性能指标
data SystemPerformance = SystemPerformance {
    riseTime :: Double,      -- 上升时间
    settlingTime :: Double,  --  settling时间
    overshoot :: Double,     -- 超调量
    steadyStateError :: Double  -- 稳态误差
}

-- 计算性能指标
calculatePerformance :: [Vector Double] -> [Double] -> SystemPerformance
calculatePerformance outputs times = 
    let finalValue = last outputs
        maxValue = maximum outputs
        overshoot = (maxValue - finalValue) / finalValue * 100
        
        -- 计算上升时间（10%到90%）
        riseTime = calculateRiseTime outputs times
        
        -- 计算settling时间（±2%）
        settlingTime = calculateSettlingTime outputs times
        
        -- 计算稳态误差
        steadyStateError = abs (finalValue - 1.0)  -- 假设期望值为1
    in SystemPerformance riseTime settlingTime overshoot steadyStateError
```

## 6. 应用示例

### 6.1 简单振荡器

**数学描述**：
$$\ddot{x} + \omega^2 x = 0$$

状态空间表示：
$$\begin{bmatrix} \dot{x}_1 \\ \dot{x}_2 \end{bmatrix} = \begin{bmatrix} 0 & 1 \\ -\omega^2 & 0 \end{bmatrix} \begin{bmatrix} x_1 \\ x_2 \end{bmatrix}$$

**Haskell实现**：

```haskell
-- 简单振荡器
simpleOscillator :: Double -> LinearSystem
simpleOscillator omega = LinearSystem {
    systemMatrix = matrix 2 [0, 1, -omega^2, 0],
    inputMatrix = matrix 2 [0, 0],
    outputMatrix = matrix 2 [1, 0],
    directMatrix = matrix 1 [0]
}

-- 仿真示例
oscillatorExample :: IO ()
oscillatorExample = do
    let sys = simpleOscillator 1.0
        x0 = vector [1.0, 0.0]
        times = [0, 0.01..10]
        inputs = replicate (length times) (vector [0.0])
        states = simulateLinearSystem sys x0 inputs times
        outputs = map (linearOutputEquation sys) states inputs
    
    putStrLn "振荡器仿真结果："
    mapM_ print (zip times outputs)
```

### 6.2 阻尼振荡器

**数学描述**：
$$\ddot{x} + 2\zeta\omega\dot{x} + \omega^2 x = 0$$

**Haskell实现**：

```haskell
-- 阻尼振荡器
dampedOscillator :: Double -> Double -> LinearSystem
dampedOscillator omega zeta = LinearSystem {
    systemMatrix = matrix 2 [0, 1, -omega^2, -2*zeta*omega],
    inputMatrix = matrix 2 [0, 0],
    outputMatrix = matrix 2 [1, 0],
    directMatrix = matrix 1 [0]
}
```

## 总结

本文档建立了系统动力学的形式化理论框架，包括：

1. **严格定义**：动态系统、线性系统、平衡点等核心概念
2. **数学理论**：线性系统解、相空间分析等理论结果
3. **Haskell实现**：所有概念都有对应的类型安全实现
4. **应用示例**：振荡器系统的完整建模和仿真

这个框架为后续的控制理论、稳定性分析等提供了坚实的基础。

---

**相关文档**：

- [反馈控制系统](./02-Feedback-Control.md)
- [稳定性理论](./03-Stability-Theory.md)
- [最优控制](./04-Optimal-Control.md)
