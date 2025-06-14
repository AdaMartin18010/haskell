# PID控制理论

## 概述

PID控制是最经典和广泛使用的控制方法，通过比例(Proportional)、积分(Integral)、微分(Derivative)三个环节的组合来实现控制目标。本文档建立PID控制的形式化理论框架，包括控制器设计、参数整定、性能分析等核心内容。

## 1. PID控制器基础

### 1.1 PID控制器结构

**定义 1.1 (PID控制器)**
PID控制器的控制律为：
$$u(t) = K_p e(t) + K_i \int_0^t e(\tau) d\tau + K_d \frac{d}{dt} e(t)$$

其中：

- $e(t) = r(t) - y(t)$ 是误差信号
- $K_p$ 是比例增益
- $K_i$ 是积分增益
- $K_d$ 是微分增益

**定义 1.2 (PID控制器传递函数)**
PID控制器的传递函数为：
$$G_c(s) = K_p + \frac{K_i}{s} + K_d s$$

**Haskell实现**：

```haskell
-- PID控制器
data PIDController = PIDController {
    kp :: Double,        -- 比例增益
    ki :: Double,        -- 积分增益
    kd :: Double,        -- 微分增益
    integral :: Double,  -- 积分项
    previousError :: Double,  -- 前一次误差
    setpoint :: Double   -- 设定值
}

-- PID控制律
pidControl :: PIDController -> Double -> Double -> (PIDController, Double)
pidController controller currentValue dt = 
    let error = setpoint controller - currentValue
        newIntegral = integral controller + error * dt
        derivative = (error - previousError controller) / dt
        output = kp controller * error + 
                 ki controller * newIntegral + 
                 kd controller * derivative
        newController = controller {
            integral = newIntegral,
            previousError = error
        }
    in (newController, output)

-- PID控制器传递函数
pidTransferFunction :: PIDController -> TransferFunction
pidTransferFunction controller = 
    let kp = kp controller
        ki = ki controller
        kd = kd controller
        
        -- 传递函数: G(s) = Kp + Ki/s + Kd*s
        numerator = [kd, kp, ki]  -- Kd*s^2 + Kp*s + Ki
        denominator = [1, 0]      -- s
    in TransferFunction numerator denominator
```

### 1.2 PID控制器特性

**定理 1.1 (PID控制器特性)**
PID控制器具有以下特性：

1. **比例项(P)**：提供与误差成比例的控制作用
2. **积分项(I)**：消除稳态误差
3. **微分项(D)**：提供预测性控制，改善动态响应

**Haskell实现**：

```haskell
-- PID控制器特性分析
analyzePIDCharacteristics :: PIDController -> SystemResponse -> PIDCharacteristics
analyzePIDCharacteristics controller response = 
    let -- 比例项分析
        proportionalEffect = analyzeProportionalEffect controller response
        
        -- 积分项分析
        integralEffect = analyzeIntegralEffect controller response
        
        -- 微分项分析
        derivativeEffect = analyzeDerivativeEffect controller response
    in PIDCharacteristics proportionalEffect integralEffect derivativeEffect

-- PID特性
data PIDCharacteristics = PIDCharacteristics {
    proportionalEffect :: ProportionalEffect,
    integralEffect :: IntegralEffect,
    derivativeEffect :: DerivativeEffect
}

data ProportionalEffect = ProportionalEffect {
    steadyStateError :: Double,
    responseSpeed :: Double
}

data IntegralEffect = IntegralEffect {
    steadyStateErrorElimination :: Bool,
    overshoot :: Double
}

data DerivativeEffect = DerivativeEffect {
    damping :: Double,
    settlingTime :: Double
}
```

## 2. PID控制器设计

### 2.1 参数选择原则

**定义 2.1 (PID参数选择原则)**
PID参数选择应遵循以下原则：

1. **比例增益 $K_p$**：影响响应速度和稳态误差
2. **积分增益 $K_i$**：消除稳态误差，但可能增加超调
3. **微分增益 $K_d$**：改善动态响应，但可能放大噪声

**Haskell实现**：

```haskell
-- PID参数选择
data PIDTuningMethod = 
    ZieglerNichols | 
    CohenCoon | 
    ITAE | 
    IMC

-- Ziegler-Nichols方法
zieglerNicholsTuning :: SystemResponse -> PIDController
zieglerNicholsTuning response = 
    let (ku, tu) = findUltimateGain response
        kp = 0.6 * ku
        ki = 1.2 * ku / tu
        kd = 0.075 * ku * tu
    in PIDController kp ki kd 0 0 0

-- Cohen-Coon方法
cohenCoonTuning :: SystemResponse -> PIDController
cohenCoonTuning response = 
    let (k, tau, theta) = extractSystemParameters response
        ratio = theta / tau
        
        -- Cohen-Coon公式
        kp = (1.35 + 0.25 * ratio) / k
        ki = kp / (2.5 + 2 * ratio) / tau
        kd = kp * 0.37 * tau / (1 + 0.81 * ratio)
    in PIDController kp ki kd 0 0 0

-- ITAE方法
itaeTuning :: SystemResponse -> PIDController
itaeTuning response = 
    let (k, tau, theta) = extractSystemParameters response
        ratio = theta / tau
        
        -- ITAE公式
        kp = (0.965 + 0.85 * ratio) / k
        ki = kp / (1.357 + 0.947 * ratio) / tau
        kd = kp * 0.381 * tau / (1 + 0.995 * ratio)
    in PIDController kp ki kd 0 0 0
```

### 2.2 系统辨识

**定义 2.2 (系统辨识)**
通过实验数据识别系统模型参数的过程。

**Haskell实现**：

```haskell
-- 系统参数
data SystemParameters = SystemParameters {
    gain :: Double,      -- 系统增益
    timeConstant :: Double,  -- 时间常数
    deadTime :: Double,      -- 死区时间
    order :: Int            -- 系统阶数
}

-- 阶跃响应辨识
stepResponseIdentification :: [Double] -> [Double] -> SystemParameters
stepResponseIdentification times outputs = 
    let -- 提取关键参数
        finalValue = last outputs
        initialValue = head outputs
        gain = finalValue - initialValue
        
        -- 找到63.2%响应时间
        targetValue = initialValue + 0.632 * gain
        timeConstant = findTimeConstant times outputs targetValue
        
        -- 找到死区时间
        deadTime = findDeadTime times outputs initialValue
        
    in SystemParameters gain timeConstant deadTime 1

-- 找到时间常数
findTimeConstant :: [Double] -> [Double] -> Double -> Double
findTimeConstant times outputs targetValue = 
    let -- 找到最接近目标值的时间点
        differences = zipWith (\t y -> (t, abs (y - targetValue))) times outputs
        (time, _) = minimumBy (comparing snd) differences
    in time

-- 找到死区时间
findDeadTime :: [Double] -> [Double] -> Double -> Double
findDeadTime times outputs initialValue = 
    let -- 找到输出开始变化的时间
        threshold = 0.05  -- 5%变化阈值
        changes = zipWith (\t y -> (t, abs (y - initialValue))) times outputs
        significantChanges = filter (\(_, diff) -> diff > threshold) changes
        (deadTime, _) = head significantChanges
    in deadTime
```

## 3. PID参数整定

### 3.1 Ziegler-Nichols方法

**算法 3.1 (Ziegler-Nichols方法)**:

1. 将积分和微分增益设为0
2. 逐渐增加比例增益直到系统产生等幅振荡
3. 记录临界增益 $K_u$ 和临界周期 $T_u$
4. 根据经验公式计算PID参数

**经验公式**：

- $K_p = 0.6 K_u$
- $K_i = 1.2 K_u / T_u$
- $K_d = 0.075 K_u T_u$

**Haskell实现**：

```haskell
-- Ziegler-Nichols整定
zieglerNicholsTuning :: SystemResponse -> PIDController
zieglerNicholsTuning response = 
    let (ku, tu) = findUltimateGain response
        kp = 0.6 * ku
        ki = 1.2 * ku / tu
        kd = 0.075 * ku * tu
    in PIDController kp ki kd 0 0 0

-- 寻找临界增益和周期
findUltimateGain :: SystemResponse -> (Double, Double)
findUltimateGain response = 
    let -- 通过实验找到临界增益
        gains = [0.1, 0.2..10.0]
        oscillations = map (\k -> testOscillation response k) gains
        criticalGain = findCriticalGain gains oscillations
        
        -- 测量临界周期
        criticalPeriod = measureOscillationPeriod response criticalGain
    in (criticalGain, criticalPeriod)

-- 测试振荡
testOscillation :: SystemResponse -> Double -> Bool
testOscillation response gain = 
    let -- 模拟系统响应
        simulation = simulateSystem response gain
        -- 检查是否产生等幅振荡
    in isOscillating simulation

-- 测量振荡周期
measureOscillationPeriod :: SystemResponse -> Double -> Double
measureOscillationPeriod response gain = 
    let simulation = simulateSystem response gain
        peaks = findPeaks simulation
        periods = zipWith (-) (tail peaks) peaks
    in average periods
```

### 3.2 Cohen-Coon方法

**算法 3.2 (Cohen-Coon方法)**
基于系统的一阶加死区模型进行参数整定。

**经验公式**：

- $K_p = \frac{1.35 + 0.25\tau/\theta}{K}$
- $K_i = \frac{K_p}{2.5 + 2\tau/\theta} \cdot \frac{1}{\tau}$
- $K_d = K_p \cdot \frac{0.37\tau}{1 + 0.81\tau/\theta}$

**Haskell实现**：

```haskell
-- Cohen-Coon整定
cohenCoonTuning :: SystemParameters -> PIDController
cohenCoonTuning params = 
    let k = gain params
        tau = timeConstant params
        theta = deadTime params
        ratio = theta / tau
        
        -- Cohen-Coon公式
        kp = (1.35 + 0.25 * ratio) / k
        ki = kp / (2.5 + 2 * ratio) / tau
        kd = kp * 0.37 * tau / (1 + 0.81 * ratio)
    in PIDController kp ki kd 0 0 0
```

### 3.3 ITAE方法

**算法 3.3 (ITAE方法)**
基于时间加权绝对误差积分准则的参数整定。

**经验公式**：

- $K_p = \frac{0.965 + 0.85\tau/\theta}{K}$
- $K_i = \frac{K_p}{1.357 + 0.947\tau/\theta} \cdot \frac{1}{\tau}$
- $K_d = K_p \cdot \frac{0.381\tau}{1 + 0.995\tau/\theta}$

**Haskell实现**：

```haskell
-- ITAE整定
itaeTuning :: SystemParameters -> PIDController
itaeTuning params = 
    let k = gain params
        tau = timeConstant params
        theta = deadTime params
        ratio = theta / tau
        
        -- ITAE公式
        kp = (0.965 + 0.85 * ratio) / k
        ki = kp / (1.357 + 0.947 * ratio) / tau
        kd = kp * 0.381 * tau / (1 + 0.995 * ratio)
    in PIDController kp ki kd 0 0 0
```

## 4. PID控制器性能分析

### 4.1 性能指标

**定义 4.1 (PID性能指标)**
PID控制器的性能指标包括：

1. **上升时间**：响应从10%到90%的时间
2. **超调量**：最大超调百分比
3. **调节时间**：进入±2%误差带的时间
4. **稳态误差**：稳态时的误差

**Haskell实现**：

```haskell
-- PID性能指标
data PIDPerformance = PIDPerformance {
    riseTime :: Double,      -- 上升时间
    overshoot :: Double,     -- 超调量
    settlingTime :: Double,  -- 调节时间
    steadyStateError :: Double  -- 稳态误差
}

-- 计算PID性能
calculatePIDPerformance :: PIDController -> SystemResponse -> PIDPerformance
calculatePIDPerformance controller response = 
    let simulation = simulatePIDSystem controller response
        riseTime = calculateRiseTime simulation
        overshoot = calculateOvershoot simulation
        settlingTime = calculateSettlingTime simulation
        steadyStateError = calculateSteadyStateError simulation
    in PIDPerformance riseTime overshoot settlingTime steadyStateError

-- 计算上升时间
calculateRiseTime :: [Double] -> Double
calculateRiseTime response = 
    let finalValue = last response
        initialValue = head response
        target10 = initialValue + 0.1 * (finalValue - initialValue)
        target90 = initialValue + 0.9 * (finalValue - initialValue)
        
        time10 = findTimeForValue response target10
        time90 = findTimeForValue response target90
    in time90 - time10

-- 计算超调量
calculateOvershoot :: [Double] -> Double
calculateOvershoot response = 
    let finalValue = last response
        maxValue = maximum response
        overshoot = (maxValue - finalValue) / finalValue * 100
    in overshoot

-- 计算调节时间
calculateSettlingTime :: [Double] -> Double
calculateSettlingTime response = 
    let finalValue = last response
        tolerance = 0.02 * finalValue  -- ±2%误差带
        
        -- 找到进入误差带的时间
        inBand = filter (\(t, y) -> abs (y - finalValue) <= tolerance) 
                        (zip [0, dt..] response)
        settlingTime = fst (head inBand)
    in settlingTime
```

### 4.2 鲁棒性分析

**定义 4.2 (PID鲁棒性)**
PID控制器对系统参数变化的敏感程度。

**Haskell实现**：

```haskell
-- PID鲁棒性分析
analyzePIDRobustness :: PIDController -> [SystemParameters] -> RobustnessMetrics
analyzePIDRobustness controller parameterVariations = 
    let -- 在不同参数下测试性能
        performances = map (\params -> 
            calculatePIDPerformance controller (createSystemResponse params)) 
            parameterVariations
        
        -- 计算性能变化
        riseTimeVariation = calculateVariation (map riseTime performances)
        overshootVariation = calculateVariation (map overshoot performances)
        settlingTimeVariation = calculateVariation (map settlingTime performances)
        
    in RobustnessMetrics riseTimeVariation overshootVariation settlingTimeVariation

-- 鲁棒性指标
data RobustnessMetrics = RobustnessMetrics {
    riseTimeVariation :: Double,
    overshootVariation :: Double,
    settlingTimeVariation :: Double
}

-- 计算变化量
calculateVariation :: [Double] -> Double
calculateVariation values = 
    let mean = average values
        variance = average (map (\x -> (x - mean)^2) values)
    in sqrt variance
```

## 5. PID控制器改进

### 5.1 积分饱和

**定义 5.1 (积分饱和)**
当控制器输出达到限幅时，积分项继续累积导致控制性能下降的现象。

**Haskell实现**：

```haskell
-- 抗积分饱和PID控制器
data AntiWindupPIDController = AntiWindupPIDController {
    pidController :: PIDController,
    outputLimit :: (Double, Double),  -- 输出限幅
    antiWindupGain :: Double          -- 抗饱和增益
}

-- 抗积分饱和控制
antiWindupPIDControl :: AntiWindupPIDController -> Double -> Double -> (AntiWindupPIDController, Double)
antiWindupPIDControl controller currentValue dt = 
    let (pid, output) = pidControl (pidController controller) currentValue dt
        (minLimit, maxLimit) = outputLimit controller
        
        -- 限幅输出
        limitedOutput = max minLimit (min maxLimit output)
        
        -- 抗积分饱和
        saturation = output - limitedOutput
        antiWindupCorrection = antiWindupGain controller * saturation
        
        -- 更新积分项
        correctedPID = pid { integral = integral pid - antiWindupCorrection * dt }
        
        newController = controller { pidController = correctedPID }
    in (newController, limitedOutput)
```

### 5.2 微分滤波

**定义 5.2 (微分滤波)**
对微分项进行低通滤波以减少噪声影响。

**Haskell实现**：

```haskell
-- 带滤波的PID控制器
data FilteredPIDController = FilteredPIDController {
    pidController :: PIDController,
    derivativeFilter :: LowPassFilter,  -- 微分滤波器
    filterTimeConstant :: Double        -- 滤波时间常数
}

-- 带滤波的PID控制
filteredPIDControl :: FilteredPIDController -> Double -> Double -> (FilteredPIDController, Double)
filteredPIDController controller currentValue dt = 
    let error = setpoint (pidController controller) - currentValue
        derivative = (error - previousError (pidController controller)) / dt
        
        -- 微分滤波
        filteredDerivative = lowPassFilter (derivativeFilter controller) derivative dt
        
        -- 计算输出
        output = kp (pidController controller) * error + 
                 ki (pidController controller) * integral (pidController controller) +
                 kd (pidController controller) * filteredDerivative
        
        -- 更新控制器状态
        newPID = (pidController controller) {
            integral = integral (pidController controller) + error * dt,
            previousError = error
        }
        
        newController = controller { pidController = newPID }
    in (newController, output)

-- 低通滤波器
data LowPassFilter = LowPassFilter {
    timeConstant :: Double,
    previousOutput :: Double
}

-- 低通滤波
lowPassFilter :: LowPassFilter -> Double -> Double -> (LowPassFilter, Double)
lowPassFilter filter input dt = 
    let alpha = dt / (timeConstant filter + dt)
        output = alpha * input + (1 - alpha) * previousOutput filter
        newFilter = filter { previousOutput = output }
    in (newFilter, output)
```

## 6. 应用示例

### 6.1 温度控制系统

**数学描述**：
$$\tau \frac{dT}{dt} + T = K u(t)$$

其中 $T$ 是温度，$u$ 是加热功率，$\tau$ 是时间常数，$K$ 是增益。

**Haskell实现**：

```haskell
-- 温度控制系统
temperatureControlExample :: IO ()
temperatureControlExample = do
    let -- 系统参数
        tau = 10.0  -- 时间常数10秒
        k = 2.0     -- 增益2°C/W
        
        -- 设计PID控制器
        targetTemp = 50.0  -- 目标温度50°C
        controller = PIDController 5.0 0.5 1.0 0 0 targetTemp
        
        -- 仿真
        initialTemp = 20.0
        simulationTime = 100.0
        dt = 0.1
        
        -- 运行仿真
        (finalController, temperatures) = simulateTemperatureControl 
                                            controller initialTemp simulationTime dt
        
        -- 分析性能
        performance = calculatePIDPerformance controller (SystemResponse temperatures)
    
    putStrLn "温度控制仿真结果："
    putStrLn $ "上升时间: " ++ show (riseTime performance) ++ " 秒"
    putStrLn $ "超调量: " ++ show (overshoot performance) ++ "%"
    putStrLn $ "调节时间: " ++ show (settlingTime performance) ++ " 秒"
    putStrLn $ "稳态误差: " ++ show (steadyStateError performance) ++ "°C"

-- 温度控制仿真
simulateTemperatureControl :: PIDController -> Double -> Double -> Double -> (PIDController, [Double])
simulateTemperatureControl controller initialTemp simulationTime dt = 
    let times = [0, dt..simulationTime]
        simulate controller temp (t:ts) = 
            let (newController, output) = pidControl controller temp dt
                -- 系统动态
                dT = (k * output - temp) / tau
                newTemp = temp + dT * dt
            in temp : simulate newController newTemp ts
        simulate _ _ [] = []
    in (controller, simulate controller initialTemp times)
```

### 6.2 电机速度控制

**数学描述**：
$$J \frac{d\omega}{dt} + b\omega = K u(t)$$

其中 $\omega$ 是角速度，$u$ 是控制电压，$J$ 是转动惯量，$b$ 是阻尼系数，$K$ 是增益。

**Haskell实现**：

```haskell
-- 电机速度控制系统
motorSpeedControlExample :: IO ()
motorSpeedControlExample = do
    let -- 系统参数
        j = 0.1     -- 转动惯量0.1 kg·m²
        b = 0.1     -- 阻尼系数0.1 N·m·s/rad
        k = 1.0     -- 增益1 N·m/V
        
        -- 设计PID控制器
        targetSpeed = 100.0  -- 目标速度100 rad/s
        controller = PIDController 10.0 5.0 0.1 0 0 targetSpeed
        
        -- 仿真
        initialSpeed = 0.0
        simulationTime = 10.0
        dt = 0.01
        
        -- 运行仿真
        (finalController, speeds) = simulateMotorSpeedControl 
                                      controller initialSpeed simulationTime dt
        
        -- 分析性能
        performance = calculatePIDPerformance controller (SystemResponse speeds)
    
    putStrLn "电机速度控制仿真结果："
    putStrLn $ "上升时间: " ++ show (riseTime performance) ++ " 秒"
    putStrLn $ "超调量: " ++ show (overshoot performance) ++ "%"
    putStrLn $ "调节时间: " ++ show (settlingTime performance) ++ " 秒"
    putStrLn $ "稳态误差: " ++ show (steadyStateError performance) ++ " rad/s"
```

## 总结

本文档建立了PID控制的形式化理论框架，包括：

1. **基础理论**：PID控制器结构、特性分析
2. **设计方法**：参数选择、系统辨识
3. **参数整定**：Ziegler-Nichols、Cohen-Coon、ITAE方法
4. **性能分析**：性能指标、鲁棒性分析
5. **改进技术**：抗积分饱和、微分滤波
6. **应用示例**：温度控制、电机速度控制

这个框架为实际控制系统的设计和实现提供了理论基础和实用工具。

---

**相关文档**：

- [系统动力学基础](../01-Foundations/01-System-Dynamics.md)
- [反馈控制理论](../01-Foundations/02-Feedback-Control.md)
- [稳定性理论](../01-Foundations/03-Stability-Theory.md)
