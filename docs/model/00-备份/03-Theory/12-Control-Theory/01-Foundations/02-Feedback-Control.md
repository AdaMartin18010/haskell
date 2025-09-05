# 反馈控制理论

## 概述

反馈控制是控制论的核心概念，通过将系统输出反馈到输入端来调节系统行为。本文档建立反馈控制的形式化理论框架，包括状态反馈、输出反馈、观测器设计等核心内容。

## 1. 反馈控制基础

### 1.1 反馈控制原理

**定义 1.1 (反馈控制)**
反馈控制是通过测量系统输出，将其与期望值比较，然后根据误差调整控制输入的过程。

**定义 1.2 (闭环系统)**
闭环系统是包含反馈控制器的系统，其结构为：
$$u(t) = K(r(t) - y(t))$$

其中：

- $r(t)$ 是参考输入
- $y(t)$ 是系统输出
- $u(t)$ 是控制输入
- $K$ 是控制器增益

**Haskell实现**：

```haskell
-- 反馈控制器
data FeedbackController a b = FeedbackController {
    controllerGain :: a,           -- 控制器增益
    referenceInput :: b -> Double, -- 参考输入函数
    controlLaw :: b -> b -> a      -- 控制律
}

-- 基本反馈控制律
basicFeedbackControl :: FeedbackController a b -> b -> b -> a
basicFeedbackControl controller output reference = 
    let error = reference - output
        gain = controllerGain controller
    in gain * error

-- 闭环系统
data ClosedLoopSystem a b c = ClosedLoopSystem {
    plant :: LinearSystem,                    -- 被控对象
    controller :: FeedbackController a b,     -- 控制器
    feedbackPath :: c -> b                   -- 反馈路径
}
```

### 1.2 反馈控制优势

**定理 1.1 (反馈控制优势)**
反馈控制具有以下优势：

1. **鲁棒性**：对系统参数变化不敏感
2. **抗干扰性**：能够抑制外部干扰
3. **稳定性**：能够稳定不稳定系统
4. **精度**：能够提高系统精度

**Haskell实现**：

```haskell
-- 系统鲁棒性分析
robustnessAnalysis :: LinearSystem -> [LinearSystem] -> Double
robustnessAnalysis nominal variations = 
    let nominalPerformance = calculatePerformance nominal
        worstCasePerformance = minimum [calculatePerformance sys | sys <- variations]
    in worstCasePerformance / nominalPerformance

-- 抗干扰性分析
disturbanceRejection :: LinearSystem -> Vector Double -> Double
disturbanceRejection sys disturbance = 
    let openLoopResponse = simulateOpenLoop sys disturbance
        closedLoopResponse = simulateClosedLoop sys disturbance
    in norm (openLoopResponse - closedLoopResponse)
```

## 2. 状态反馈控制

### 2.1 状态反馈定义

**定义 2.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是状态反馈增益矩阵。

**定义 2.2 (闭环系统矩阵)**
状态反馈下的闭环系统：
$$\dot{x}(t) = (A - BK)x(t) + Br(t)$$
$$y(t) = Cx(t)$$

闭环系统矩阵为 $A_{cl} = A - BK$。

**Haskell实现**：

```haskell
-- 状态反馈控制器
data StateFeedbackController = StateFeedbackController {
    feedbackGain :: Matrix Double,    -- 反馈增益矩阵K
    referenceInput :: Vector Double   -- 参考输入
}

-- 状态反馈控制律
stateFeedbackControl :: StateFeedbackController -> Vector Double -> Vector Double
stateFeedbackControl controller state = 
    let k = feedbackGain controller
        r = referenceInput controller
    in -k `multiply` state + r

-- 闭环系统矩阵
closedLoopMatrix :: LinearSystem -> Matrix Double -> Matrix Double
closedLoopMatrix sys k = 
    systemMatrix sys - inputMatrix sys `multiply` k
```

### 2.2 极点配置

**定理 2.1 (极点配置定理)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明**：

1. 可控系统可以变换为可控标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

**Haskell实现**：

```haskell
-- 极点配置算法
polePlacement :: LinearSystem -> [Complex Double] -> Maybe (Matrix Double)
polePlacement sys desiredPoles = 
    if isControllable sys
        then Just (calculateFeedbackGain sys desiredPoles)
        else Nothing

-- 可控性检查
isControllable :: LinearSystem -> Bool
isControllable sys = 
    let controllabilityMatrix = buildControllabilityMatrix sys
        rank = matrixRank controllabilityMatrix
        n = rows (systemMatrix sys)
    in rank == n

-- 构建可控性矩阵
buildControllabilityMatrix :: LinearSystem -> Matrix Double
buildControllabilityMatrix sys = 
    let a = systemMatrix sys
        b = inputMatrix sys
        n = rows a
        powers = [a^i | i <- [0..n-1]]
    in hconcat [b `multiply` power | power <- powers]

-- 计算反馈增益
calculateFeedbackGain :: LinearSystem -> [Complex Double] -> Matrix Double
calculateFeedbackGain sys desiredPoles = 
    let controllableForm = toControllableForm sys
        kStandard = placePoles controllableForm desiredPoles
        transformation = getTransformation sys
    in kStandard `multiply` transformation
```

### 2.3 线性二次型调节器(LQR)

**定义 2.3 (LQR问题)**
LQR问题是最小化二次型性能指标：
$$J = \int_0^\infty (x^T Q x + u^T R u) dt$$

其中 $Q \geq 0$ 和 $R > 0$ 是权重矩阵。

**定理 2.2 (LQR解)**
LQR问题的最优控制律为：
$$u(t) = -Kx(t)$$

其中 $K = R^{-1}B^TP$，$P$ 是代数Riccati方程的解：
$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**Haskell实现**：

```haskell
-- LQR控制器
data LQRController = LQRController {
    stateWeight :: Matrix Double,     -- 状态权重矩阵Q
    inputWeight :: Matrix Double,     -- 输入权重矩阵R
    optimalGain :: Matrix Double      -- 最优反馈增益
}

-- 求解代数Riccati方程
solveAlgebraicRiccati :: LinearSystem -> Matrix Double -> Matrix Double -> Matrix Double
solveAlgebraicRiccati sys q r = 
    let a = systemMatrix sys
        b = inputMatrix sys
        n = rows a
        
        -- 迭代求解
        iterateRiccati p = 
            let newP = a `multiply` p + p `multiply` a - 
                      p `multiply` b `multiply` (inverse r) `multiply` (transpose b) `multiply` p + q
            in if norm (newP - p) < epsilon
                then newP
                else iterateRiccati newP
        
        initialP = identityMatrix n
    in iterateRiccati initialP

-- 计算LQR最优增益
calculateLQRGain :: LinearSystem -> Matrix Double -> Matrix Double -> Matrix Double
calculateLQRGain sys q r = 
    let p = solveAlgebraicRiccati sys q r
        b = inputMatrix sys
    in inverse r `multiply` transpose b `multiply` p
```

## 3. 输出反馈控制

### 3.1 输出反馈定义

**定义 3.1 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times p}$ 是输出反馈增益矩阵。

**定义 3.2 (输出反馈闭环系统)**
输出反馈下的闭环系统：
$$\dot{x}(t) = (A - BKC)x(t) + Br(t)$$
$$y(t) = Cx(t)$$

**Haskell实现**：

```haskell
-- 输出反馈控制器
data OutputFeedbackController = OutputFeedbackController {
    outputGain :: Matrix Double,      -- 输出反馈增益矩阵K
    referenceInput :: Vector Double   -- 参考输入
}

-- 输出反馈控制律
outputFeedbackControl :: OutputFeedbackController -> Vector Double -> Vector Double
outputFeedbackControl controller output = 
    let k = outputGain controller
        r = referenceInput controller
    in -k `multiply` output + r

-- 输出反馈闭环系统矩阵
outputFeedbackClosedLoop :: LinearSystem -> Matrix Double -> Matrix Double
outputFeedbackClosedLoop sys k = 
    let a = systemMatrix sys
        b = inputMatrix sys
        c = outputMatrix sys
    in a - b `multiply` k `multiply` c
```

### 3.2 输出反馈限制

**定理 3.1 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明**：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

**Haskell实现**：

```haskell
-- 可观性分解
observabilityDecomposition :: LinearSystem -> (LinearSystem, LinearSystem)
observabilityDecomposition sys = 
    let observablePart = extractObservablePart sys
        unobservablePart = extractUnobservablePart sys
    in (observablePart, unobservablePart)

-- 提取可观部分
extractObservablePart :: LinearSystem -> LinearSystem
extractObservablePart sys = 
    let transformation = getObservabilityTransformation sys
        transformed = transformSystem sys transformation
        observableStates = countObservableStates sys
    in extractSubsystem transformed observableStates
```

## 4. 观测器设计

### 4.1 全维观测器

**定义 4.1 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**定义 4.2 (观测误差)**
观测误差 $e(t) = x(t) - \hat{x}(t)$ 满足：
$$\dot{e}(t) = (A - LC)e(t)$$

**Haskell实现**：

```haskell
-- 全维观测器
data FullOrderObserver = FullOrderObserver {
    observerGain :: Matrix Double,    -- 观测器增益矩阵L
    estimatedState :: Vector Double   -- 状态估计
}

-- 观测器动态
observerDynamics :: LinearSystem -> FullOrderObserver -> Vector Double -> Vector Double -> Vector Double
observerDynamics sys observer input output = 
    let a = systemMatrix sys
        b = inputMatrix sys
        c = outputMatrix sys
        l = observerGain observer
        xhat = estimatedState observer
        
        predictedOutput = c `multiply` xhat
        outputError = output - predictedOutput
    in a `multiply` xhat + b `multiply` input + l `multiply` outputError

-- 观测误差动态
observerErrorDynamics :: LinearSystem -> Matrix Double -> Vector Double -> Vector Double
observerErrorDynamics sys l error = 
    let a = systemMatrix sys
        c = outputMatrix sys
    in (a - l `multiply` c) `multiply` error
```

### 4.2 观测器极点配置

**定理 4.1 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明**：
通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器极点配置等价于状态反馈极点配置
3. 利用对偶性得到观测器增益

**Haskell实现**：

```haskell
-- 观测器极点配置
observerPolePlacement :: LinearSystem -> [Complex Double] -> Maybe (Matrix Double)
observerPolePlacement sys desiredPoles = 
    if isObservable sys
        then Just (calculateObserverGain sys desiredPoles)
        else Nothing

-- 可观性检查
isObservable :: LinearSystem -> Bool
isObservable sys = 
    let observabilityMatrix = buildObservabilityMatrix sys
        rank = matrixRank observabilityMatrix
        n = rows (systemMatrix sys)
    in rank == n

-- 构建可观性矩阵
buildObservabilityMatrix :: LinearSystem -> Matrix Double
buildObservabilityMatrix sys = 
    let a = systemMatrix sys
        c = outputMatrix sys
        n = rows a
        powers = [a^i | i <- [0..n-1]]
    in vconcat [c `multiply` power | power <- powers]

-- 计算观测器增益
calculateObserverGain :: LinearSystem -> [Complex Double] -> Matrix Double
calculateObserverGain sys desiredPoles = 
    let a = systemMatrix sys
        c = outputMatrix sys
        
        -- 对偶系统
        dualA = transpose a
        dualB = transpose c
        
        -- 对偶系统的状态反馈增益
        dualK = calculateFeedbackGain (LinearSystem dualA dualB c (zeroMatrix 1 1)) desiredPoles
        
        -- 观测器增益
    in transpose dualK
```

### 4.3 降维观测器

**定义 4.3 (降维观测器)**
降维观测器只估计不可测量的状态，减少计算复杂度。

**Haskell实现**：

```haskell
-- 降维观测器
data ReducedOrderObserver = ReducedOrderObserver {
    reducedGain :: Matrix Double,     -- 降维观测器增益
    unmeasuredStates :: Vector Double -- 不可测量状态估计
}

-- 降维观测器设计
designReducedOrderObserver :: LinearSystem -> [Int] -> [Complex Double] -> ReducedOrderObserver
designReducedOrderObserver sys measuredIndices desiredPoles = 
    let unmeasuredIndices = filter (`notElem` measuredIndices) [0..n-1]
        reducedSystem = extractReducedSystem sys unmeasuredIndices
        reducedGain = calculateObserverGain reducedSystem desiredPoles
    in ReducedOrderObserver reducedGain (zeroVector (length unmeasuredIndices))
```

## 5. 分离原理

### 5.1 分离原理

**定理 5.1 (分离原理)**
对于线性系统，状态反馈控制器和观测器可以独立设计，然后组合使用。

**证明**：

1. 观测器误差动态独立于控制输入
2. 系统状态和观测误差可以分别控制
3. 闭环系统极点等于控制器极点和观测器极点的并集

**Haskell实现**：

```haskell
-- 基于观测器的状态反馈
data ObserverBasedController = ObserverBasedController {
    stateFeedback :: StateFeedbackController,
    observer :: FullOrderObserver
}

-- 组合控制器
combinedControl :: ObserverBasedController -> Vector Double -> Vector Double -> Vector Double
combinedControl controller output input = 
    let stateEstimate = estimatedState (observer controller)
        controlInput = stateFeedbackControl (stateFeedback controller) stateEstimate
    in controlInput

-- 闭环系统仿真
simulateObserverBasedControl :: LinearSystem -> ObserverBasedController -> Vector Double -> [Vector Double] -> [Double] -> [Vector Double]
simulateObserverBasedControl sys controller x0 inputs times = 
    let dt = times !! 1 - times !! 0
        
        step (x, xhat) (u, t) = 
            let -- 系统动态
                xNew = x + (linearStateEquation sys x u) * dt
                y = linearOutputEquation sys x u
                
                -- 观测器动态
                xhatNew = xhat + (observerDynamics sys (observer controller) u y) * dt
                
                -- 控制输入
                uNew = combinedControl controller y u
            in (xNew, xhatNew)
        
        initialEstimate = estimatedState (observer controller)
        states = scanl step (x0, initialEstimate) (zip inputs times)
    in map fst states
```

## 6. 应用示例

### 6.1 倒立摆控制

**数学描述**：
$$\ddot{\theta} = \frac{g}{l}\sin\theta + \frac{u}{ml^2}$$

线性化后：
$$\begin{bmatrix} \dot{x}_1 \\ \dot{x}_2 \end{bmatrix} = \begin{bmatrix} 0 & 1 \\ \frac{g}{l} & 0 \end{bmatrix} \begin{bmatrix} x_1 \\ x_2 \end{bmatrix} + \begin{bmatrix} 0 \\ \frac{1}{ml^2} \end{bmatrix} u$$

**Haskell实现**：

```haskell
-- 倒立摆系统
invertedPendulum :: Double -> Double -> Double -> LinearSystem
invertedPendulum g l m = LinearSystem {
    systemMatrix = matrix 2 [0, 1, g/l, 0],
    inputMatrix = matrix 2 [0, 1/(m*l*l)],
    outputMatrix = matrix 2 [1, 0],
    directMatrix = matrix 1 [0]
}

-- 倒立摆控制示例
pendulumControlExample :: IO ()
pendulumControlExample = do
    let g = 9.81
        l = 1.0
        m = 1.0
        sys = invertedPendulum g l m
        
        -- 设计状态反馈控制器
        desiredPoles = [(-2.0) :+ 0.0, (-2.0) :+ 0.0]
        k = fromJust (polePlacement sys desiredPoles)
        controller = StateFeedbackController k (vector [0.0])
        
        -- 设计观测器
        observerPoles = [(-3.0) :+ 0.0, (-3.0) :+ 0.0]
        l = fromJust (observerPolePlacement sys observerPoles)
        observer = FullOrderObserver l (vector [0.1, 0.0])
        
        -- 组合控制器
        combinedController = ObserverBasedController controller observer
        
        -- 仿真
        x0 = vector [0.1, 0.0]  -- 初始角度0.1弧度
        times = [0, 0.01..5]
        inputs = replicate (length times) (vector [0.0])
        states = simulateObserverBasedControl sys combinedController x0 inputs times
    
    putStrLn "倒立摆控制仿真结果："
    mapM_ print (zip times states)
```

### 6.2 汽车巡航控制

**数学描述**：
$$\dot{v} = -\frac{c}{m}v + \frac{1}{m}u$$

其中 $v$ 是速度，$u$ 是控制输入，$c$ 是阻力系数，$m$ 是质量。

**Haskell实现**：

```haskell
-- 汽车巡航控制系统
cruiseControl :: Double -> Double -> LinearSystem
cruiseControl c m = LinearSystem {
    systemMatrix = matrix 1 [-c/m],
    inputMatrix = matrix 1 [1/m],
    outputMatrix = matrix 1 [1],
    directMatrix = matrix 1 [0]
}

-- 巡航控制示例
cruiseControlExample :: IO ()
cruiseControlExample = do
    let c = 0.1
        m = 1000.0
        sys = cruiseControl c m
        
        -- 设计PI控制器
        kp = 100.0
        ki = 10.0
        controller = PIController kp ki
        
        -- 仿真
        v0 = vector [0.0]  -- 初始速度0
        targetSpeed = 20.0  -- 目标速度20 m/s
        times = [0, 0.1..10]
        states = simulateCruiseControl sys controller v0 targetSpeed times
    
    putStrLn "巡航控制仿真结果："
    mapM_ print (zip times states)
```

## 总结

本文档建立了反馈控制的形式化理论框架，包括：

1. **状态反馈**：极点配置、LQR最优控制
2. **输出反馈**：输出反馈限制和设计方法
3. **观测器设计**：全维观测器、降维观测器、极点配置
4. **分离原理**：控制器和观测器的独立设计
5. **应用示例**：倒立摆控制、汽车巡航控制

这个框架为实际控制系统的设计和实现提供了理论基础和实用工具。

---

**相关文档**：

- [系统动力学基础](./01-System-Dynamics.md)
- [稳定性理论](./03-Stability-Theory.md)
- [最优控制](./04-Optimal-Control.md)
