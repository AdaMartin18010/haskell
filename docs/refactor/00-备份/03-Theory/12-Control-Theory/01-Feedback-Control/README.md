# 反馈控制理论 (Feedback Control Theory)

## 概述

反馈控制理论是控制理论的核心分支，研究如何通过测量系统输出并调整输入来实现期望的系统行为。反馈控制能够提高系统的稳定性、鲁棒性和性能。

## 目录结构

```
01-Feedback-Control/
├── README.md                    # 本文件
├── 01-Basic-Concepts.md         # 基本概念
├── 02-PID-Control.md           # PID控制器
├── 03-State-Feedback.md        # 状态反馈控制
├── 04-Observer-Design.md       # 观测器设计
├── 05-Robust-Control.md        # 鲁棒控制
└── 06-Adaptive-Control.md      # 自适应控制
```

## 核心概念

### 1. 反馈控制系统结构
- **被控对象**: 需要控制的系统
- **传感器**: 测量系统输出
- **控制器**: 根据误差计算控制信号
- **执行器**: 将控制信号转换为物理动作

### 2. 反馈控制类型
- **负反馈**: 减小误差，提高稳定性
- **正反馈**: 增大误差，可能导致不稳定
- **比例反馈**: 控制信号与误差成正比
- **积分反馈**: 消除稳态误差
- **微分反馈**: 提高响应速度

### 3. 控制性能指标
- **稳定性**: 系统是否收敛到平衡点
- **快速性**: 系统响应的速度
- **准确性**: 稳态误差的大小
- **鲁棒性**: 对参数变化的敏感性

## 形式化定义

### 反馈控制系统模型

```haskell
-- 系统状态
data SystemState = SystemState {
  position :: Double,
  velocity :: Double,
  acceleration :: Double
} deriving (Show)

-- 控制输入
data ControlInput = ControlInput {
  force :: Double,
  torque :: Double
} deriving (Show)

-- 系统输出
data SystemOutput = SystemOutput {
  measuredPosition :: Double,
  measuredVelocity :: Double
} deriving (Show)

-- 参考输入
data ReferenceInput = ReferenceInput {
  desiredPosition :: Double,
  desiredVelocity :: Double
} deriving (Show)

-- 反馈控制系统
data FeedbackControlSystem = FeedbackControlSystem {
  plant :: SystemState -> ControlInput -> SystemState,
  sensor :: SystemState -> SystemOutput,
  controller :: SystemOutput -> ReferenceInput -> ControlInput,
  actuator :: ControlInput -> ControlInput
} deriving (Show)

-- 系统动态方程
systemDynamics :: SystemState -> ControlInput -> SystemState
systemDynamics state input = SystemState {
  position = position state + velocity state * dt,
  velocity = velocity state + acceleration state * dt,
  acceleration = force input / mass
}
  where
    dt = 0.01  -- 时间步长
    mass = 1.0 -- 系统质量
```

### 反馈控制算法

```haskell
-- 误差计算
calculateError :: SystemOutput -> ReferenceInput -> SystemOutput
calculateError output reference = SystemOutput {
  measuredPosition = desiredPosition reference - measuredPosition output,
  measuredVelocity = desiredVelocity reference - measuredVelocity output
}

-- 比例控制器
proportionalController :: Double -> SystemOutput -> ControlInput
proportionalController kp error = ControlInput {
  force = kp * measuredPosition error,
  torque = 0.0
}

-- 积分控制器
integralController :: Double -> [SystemOutput] -> ControlInput
integralController ki errors = ControlInput {
  force = ki * sum (map measuredPosition errors),
  torque = 0.0
}

-- 微分控制器
derivativeController :: Double -> SystemOutput -> SystemOutput -> ControlInput
derivativeController kd currentError previousError = ControlInput {
  force = kd * (measuredPosition currentError - measuredPosition previousError) / dt,
  torque = 0.0
}
  where
    dt = 0.01

-- PID控制器
pidController :: Double -> Double -> Double -> SystemOutput -> [SystemOutput] -> SystemOutput -> ControlInput
pidController kp ki kd currentError errorHistory previousError = ControlInput {
  force = proportionalForce + integralForce + derivativeForce,
  torque = 0.0
}
  where
    proportionalForce = kp * measuredPosition currentError
    integralForce = ki * sum (map measuredPosition errorHistory)
    derivativeForce = kd * (measuredPosition currentError - measuredPosition previousError) / dt
    dt = 0.01
```

## 反馈控制类型详解

### 1. 比例控制 (P Control)

```haskell
-- 比例控制特性
data ProportionalControl = ProportionalControl {
  gain :: Double,
  steadyStateError :: Double
} deriving (Show)

-- 比例控制器实现
proportionalControl :: ProportionalControl -> SystemOutput -> ControlInput
proportionalControl controller error = ControlInput {
  force = gain controller * measuredPosition error,
  torque = 0.0
}

-- 比例控制分析
analyzeProportionalControl :: ProportionalControl -> SystemState -> Bool
analyzeProportionalControl controller state = 
  abs (measuredPosition (SystemOutput (position state) (velocity state))) < threshold
  where
    threshold = 0.01
```

### 2. 积分控制 (I Control)

```haskell
-- 积分控制特性
data IntegralControl = IntegralControl {
  gain :: Double,
  integralError :: Double,
  antiWindup :: Bool
} deriving (Show)

-- 积分控制器实现
integralControl :: IntegralControl -> SystemOutput -> IntegralControl
integralControl controller error = controller {
  integralError = integralError controller + measuredPosition error
}

-- 积分控制输出
integralControlOutput :: IntegralControl -> ControlInput
integralControlOutput controller = ControlInput {
  force = gain controller * integralError controller,
  torque = 0.0
}

-- 抗积分饱和
antiWindupControl :: IntegralControl -> SystemOutput -> IntegralControl
antiWindupControl controller error = 
  if antiWindup controller && abs (measuredPosition error) > saturationLimit
  then controller { integralError = 0.0 }
  else controller
  where
    saturationLimit = 1.0
```

### 3. 微分控制 (D Control)

```haskell
-- 微分控制特性
data DerivativeControl = DerivativeControl {
  gain :: Double,
  previousError :: Double,
  filterTimeConstant :: Double
} deriving (Show)

-- 微分控制器实现
derivativeControl :: DerivativeControl -> SystemOutput -> (DerivativeControl, ControlInput)
derivativeControl controller error = (newController, output)
  where
    newController = controller { previousError = measuredPosition error }
    derivativeSignal = (measuredPosition error - previousError controller) / dt
    filteredDerivative = lowPassFilter derivativeSignal (filterTimeConstant controller)
    output = ControlInput {
      force = gain controller * filteredDerivative,
      torque = 0.0
    }
    dt = 0.01

-- 低通滤波器
lowPassFilter :: Double -> Double -> Double
lowPassFilter input timeConstant = 
  alpha * input + (1 - alpha) * previousOutput
  where
    alpha = dt / (timeConstant + dt)
    dt = 0.01
    previousOutput = 0.0  -- 简化实现
```

## 状态反馈控制

```haskell
-- 状态反馈控制器
data StateFeedbackController = StateFeedbackController {
  feedbackGains :: [Double],
  referenceGain :: Double
} deriving (Show)

-- 状态反馈控制律
stateFeedbackControl :: StateFeedbackController -> SystemState -> ReferenceInput -> ControlInput
stateFeedbackControl controller state reference = ControlInput {
  force = referenceTerm - feedbackTerm,
  torque = 0.0
}
  where
    referenceTerm = referenceGain controller * desiredPosition reference
    feedbackTerm = sum (zipWith (*) (feedbackGains controller) [position state, velocity state, acceleration state])

-- 极点配置
polePlacement :: [Double] -> StateFeedbackController
polePlacement desiredPoles = StateFeedbackController {
  feedbackGains = calculateFeedbackGains desiredPoles,
  referenceGain = 1.0
}

-- 计算反馈增益
calculateFeedbackGains :: [Double] -> [Double]
calculateFeedbackGains poles = 
  -- 这里需要根据系统模型计算反馈增益
  -- 简化实现
  [1.0, 2.0, 0.5]
```

## 观测器设计

```haskell
-- 观测器
data Observer = Observer {
  observerGains :: [Double],
  estimatedState :: SystemState
} deriving (Show)

-- 观测器更新
updateObserver :: Observer -> SystemOutput -> ControlInput -> Observer
updateObserver observer output input = observer {
  estimatedState = newEstimatedState
}
  where
    newEstimatedState = SystemState {
      position = estimatedPosition + observerGains observer !! 0 * positionError,
      velocity = estimatedVelocity + observerGains observer !! 1 * positionError,
      acceleration = estimatedAcceleration + observerGains observer !! 2 * positionError
    }
    estimatedPosition = position (estimatedState observer)
    estimatedVelocity = velocity (estimatedState observer)
    estimatedAcceleration = acceleration (estimatedState observer)
    positionError = measuredPosition output - estimatedPosition

-- 卡尔曼滤波器
data KalmanFilter = KalmanFilter {
  state :: SystemState,
  covariance :: Matrix Double,
  processNoise :: Matrix Double,
  measurementNoise :: Double
} deriving (Show)

-- 卡尔曼滤波更新
kalmanUpdate :: KalmanFilter -> SystemOutput -> ControlInput -> KalmanFilter
kalmanFilter measurement input = 
  -- 预测步骤
  let predictedState = predictState (state kalmanFilter) input
      predictedCovariance = predictCovariance (covariance kalmanFilter) (processNoise kalmanFilter)
  -- 更新步骤
      kalmanGain = calculateKalmanGain predictedCovariance (measurementNoise kalmanFilter)
      updatedState = updateState predictedState kalmanGain measurement
      updatedCovariance = updateCovariance predictedCovariance kalmanGain
  in kalmanFilter {
    state = updatedState,
    covariance = updatedCovariance
  }
```

## 反馈控制与Haskell

### 1. 函数式控制设计

```haskell
-- 控制器的函数式表示
type Controller = SystemOutput -> ReferenceInput -> ControlInput

-- 控制器的组合
composeControllers :: Controller -> Controller -> Controller
composeControllers controller1 controller2 = \output reference ->
  let control1 = controller1 output reference
      control2 = controller2 output reference
  in ControlInput {
    force = force control1 + force control2,
    torque = torque control1 + torque control2
  }

-- 高阶控制器
higherOrderController :: (Controller -> Controller) -> Controller -> Controller
higherOrderController modifier baseController = modifier baseController

-- 自适应控制器
adaptiveController :: Controller -> (SystemOutput -> Controller) -> Controller
adaptiveController baseController adaptor = \output reference ->
  let adaptedController = adaptor output
  in adaptedController output reference
```

### 2. 类型安全控制

```haskell
-- 控制信号类型
newtype ControlSignal = ControlSignal { unControlSignal :: Double }
  deriving (Show, Num, Fractional)

-- 安全控制范围
data SafeControlRange = SafeControlRange {
  minValue :: ControlSignal,
  maxValue :: ControlSignal
} deriving (Show)

-- 安全控制器
safeController :: SafeControlRange -> Controller -> Controller
safeController range controller = \output reference ->
  let rawControl = controller output reference
      safeForce = clamp (force rawControl) (unControlSignal (minValue range)) (unControlSignal (maxValue range))
  in ControlInput {
    force = safeForce,
    torque = torque rawControl
  }

-- 值限制函数
clamp :: Double -> Double -> Double -> Double
clamp value minVal maxVal = max minVal (min maxVal value)
```

## 应用示例

### 1. 温度控制系统

```haskell
-- 温度系统状态
data TemperatureState = TemperatureState {
  temperature :: Double,
  heatRate :: Double
} deriving (Show)

-- 温度控制器
temperatureController :: Double -> Double -> Double -> TemperatureState -> Double -> ControlInput
temperatureController kp ki kd state setpoint = ControlInput {
  force = controlSignal,
  torque = 0.0
}
  where
    error = setpoint - temperature state
    controlSignal = kp * error + ki * integralError + kd * heatRate state
    integralError = 0.0  -- 简化实现
```

### 2. 机器人位置控制

```haskell
-- 机器人状态
data RobotState = RobotState {
  position :: (Double, Double),
  velocity :: (Double, Double),
  orientation :: Double
} deriving (Show)

-- 机器人控制器
robotController :: RobotState -> (Double, Double) -> ControlInput
robotController state target = ControlInput {
  force = linearForce,
  torque = angularTorque
}
  where
    positionError = fst target - fst (position state)
    velocityError = snd target - fst (velocity state)
    linearForce = kp * positionError + kd * velocityError
    angularTorque = kp * (orientation target - orientation state)
    kp = 1.0
    kd = 0.5
```

## 总结

反馈控制理论为系统控制提供了强大的理论基础：

1. **比例控制**: 提供基本的误差修正能力
2. **积分控制**: 消除稳态误差
3. **微分控制**: 提高系统响应速度
4. **状态反馈**: 实现精确的极点配置
5. **观测器**: 估计不可测量的状态

在Haskell中，反馈控制可以通过函数式编程的方式实现，提供类型安全和模块化的控制设计。反馈控制理论在自动化系统、机器人控制、过程控制等领域有广泛应用。 