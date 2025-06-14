# 稳定性理论

## 概述

稳定性理论是控制论的核心内容，研究系统在平衡点附近的行为特性。本文档建立稳定性的形式化理论框架，包括李雅普诺夫稳定性、线性系统稳定性、频域稳定性等核心概念。

## 1. 稳定性基本概念

### 1.1 平衡点

**定义 1.1 (平衡点)**
对于系统 $\dot{x} = f(x)$，状态 $x_e$ 是平衡点，如果 $f(x_e) = 0$。

**定义 1.2 (平衡点分类)**

- **孤立平衡点**：在平衡点附近没有其他平衡点
- **非孤立平衡点**：平衡点附近存在其他平衡点
- **稳定平衡点**：系统在平衡点附近保持稳定
- **不稳定平衡点**：系统在平衡点附近发散

**Haskell实现**：

```haskell
-- 平衡点
data EquilibriumPoint a = EquilibriumPoint {
    equilibriumState :: a,
    equilibriumType :: EquilibriumType,
    stabilityType :: StabilityType
}

data EquilibriumType = 
    Isolated | 
    NonIsolated

data StabilityType = 
    Stable | 
    Unstable | 
    AsymptoticallyStable | 
    ExponentiallyStable

-- 寻找平衡点
findEquilibriumPoints :: (a -> a) -> [a] -> [EquilibriumPoint a]
findEquilibriumPoints f stateSpace = 
    let equilibria = filter (\x -> norm (f x) < epsilon) stateSpace
        classifyEquilibrium x = 
            let isIsolated = checkIsolation x stateSpace
                stability = analyzeStability f x
            in EquilibriumPoint x isIsolated stability
    in map classifyEquilibrium equilibria
    where
        epsilon = 1e-10
```

### 1.2 稳定性定义

**定义 1.3 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 1.4 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**定义 1.5 (指数稳定性)**
平衡点 $x_e$ 是指数稳定的，如果存在常数 $M > 0$ 和 $\alpha > 0$ 使得：
$$\|x(t) - x_e\| \leq M\|x(0) - x_e\|e^{-\alpha t}$$

**Haskell实现**：

```haskell
-- 稳定性分析
class StabilityAnalyzer sys where
    isStable :: sys -> a -> Bool
    isAsymptoticallyStable :: sys -> a -> Bool
    isExponentiallyStable :: sys -> a -> Bool

-- 李雅普诺夫稳定性检查
lyapunovStability :: (a -> a) -> a -> Bool
lyapunovStability f x0 = 
    let trajectory = simulateTrajectory f x0
        equilibrium = findEquilibrium f x0
        stabilityCheck = checkBoundedness trajectory equilibrium
    in stabilityCheck

-- 渐近稳定性检查
asymptoticStability :: (a -> a) -> a -> Bool
asymptoticStability f x0 = 
    let trajectory = simulateTrajectory f x0
        equilibrium = findEquilibrium f x0
        convergenceCheck = checkConvergence trajectory equilibrium
    in lyapunovStability f x0 && convergenceCheck

-- 指数稳定性检查
exponentialStability :: (a -> a) -> a -> Bool
exponentialStability f x0 = 
    let trajectory = simulateTrajectory f x0
        equilibrium = findEquilibrium f x0
        exponentialCheck = checkExponentialDecay trajectory equilibrium
    in exponentialCheck
```

## 2. 李雅普诺夫方法

### 2.1 李雅普诺夫函数

**定义 2.1 (李雅普诺夫函数)**
函数 $V : D \rightarrow \mathbb{R}$ 是系统 $\dot{x} = f(x)$ 在平衡点 $x_e$ 的李雅普诺夫函数，如果：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \in D \setminus \{x_e\}$
3. $\dot{V}(x) \leq 0$ 对于 $x \in D$

其中 $D$ 是包含 $x_e$ 的开集。

**定义 2.2 (严格李雅普诺夫函数)**
如果 $\dot{V}(x) < 0$ 对于 $x \in D \setminus \{x_e\}$，则 $V$ 是严格李雅普诺夫函数。

**Haskell实现**：

```haskell
-- 李雅普诺夫函数
data LyapunovFunction a = LyapunovFunction {
    lyapunovValue :: a -> Double,           -- 李雅普诺夫函数值
    lyapunovDerivative :: a -> a -> Double, -- 李雅普诺夫函数导数
    domain :: [a]                           -- 定义域
}

-- 李雅普诺夫函数检查
isLyapunovFunction :: LyapunovFunction a -> a -> (a -> a) -> Bool
isLyapunovFunction lyap x0 f = 
    let v = lyapunovValue lyap
        vdot = lyapunovDerivative lyap
        domain = domain lyap
        
        -- 检查条件1: V(x0) = 0
        condition1 = abs (v x0) < epsilon
        
        -- 检查条件2: V(x) > 0 for x ≠ x0
        condition2 = all (\x -> v x > 0 || norm (x - x0) < epsilon) 
                        (filter (\x -> norm (x - x0) > epsilon) domain)
        
        -- 检查条件3: V̇(x) ≤ 0
        condition3 = all (\x -> vdot x (f x) <= 0) domain
    in condition1 && condition2 && condition3

-- 严格李雅普诺夫函数检查
isStrictLyapunovFunction :: LyapunovFunction a -> a -> (a -> a) -> Bool
isStrictLyapunovFunction lyap x0 f = 
    let vdot = lyapunovDerivative lyap
        domain = domain lyap
        
        -- 检查严格条件: V̇(x) < 0 for x ≠ x0
        strictCondition = all (\x -> vdot x (f x) < 0) 
                              (filter (\x -> norm (x - x0) > epsilon) domain)
    in isLyapunovFunction lyap x0 f && strictCondition
```

### 2.2 李雅普诺夫稳定性定理

**定理 2.1 (李雅普诺夫直接法)**
如果存在李雅普诺夫函数 $V$，则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明**：

1. 李雅普诺夫函数在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

**定理 2.2 (渐近稳定性定理)**
如果存在严格李雅普诺夫函数 $V$，则平衡点 $x_e$ 是渐近稳定的。

**证明**：

1. 严格李雅普诺夫函数确保 $V(x)$ 单调递减
2. $V(x)$ 有下界（非负）
3. 因此 $V(x)$ 收敛到最小值
4. 最小值对应平衡点

**Haskell实现**：

```haskell
-- 李雅普诺夫稳定性定理
lyapunovStabilityTheorem :: LyapunovFunction a -> a -> (a -> a) -> Bool
lyapunovStabilityTheorem lyap x0 f = 
    isLyapunovFunction lyap x0 f

-- 渐近稳定性定理
asymptoticStabilityTheorem :: LyapunovFunction a -> a -> (a -> a) -> Bool
asymptoticStabilityTheorem lyap x0 f = 
    isStrictLyapunovFunction lyap x0 f

-- 构造李雅普诺夫函数
constructLyapunovFunction :: LinearSystem -> LyapunovFunction (Vector Double)
constructLyapunovFunction sys = 
    let a = systemMatrix sys
        -- 求解李雅普诺夫方程: A^T P + P A = -Q
        q = identityMatrix (rows a)
        p = solveLyapunovEquation a q
        
        -- 李雅普诺夫函数: V(x) = x^T P x
        v x = transpose x `multiply` p `multiply` x
        
        -- 李雅普诺夫函数导数: V̇(x) = x^T (A^T P + P A) x
        vdot x dx = transpose x `multiply` (transpose a `multiply` p + p `multiply` a) `multiply` x
    in LyapunovFunction v vdot []

-- 求解李雅普诺夫方程
solveLyapunovEquation :: Matrix Double -> Matrix Double -> Matrix Double
solveLyapunovEquation a q = 
    let n = rows a
        -- 将李雅普诺夫方程转换为线性方程组
        linearSystem = buildLyapunovLinearSystem a q
        solution = solveLinearSystem linearSystem
        
        -- 重构矩阵P
    in reconstructMatrix solution n
```

## 3. 线性系统稳定性

### 3.1 线性系统稳定性判据

**定理 3.1 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明**：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**Haskell实现**：

```haskell
-- 线性系统稳定性检查
linearSystemStability :: LinearSystem -> Bool
linearSystemStability sys = 
    let a = systemMatrix sys
        eigenvalues = matrixEigenvalues a
        realParts = map realPart eigenvalues
    in all (< 0) realParts

-- 矩阵特征值
matrixEigenvalues :: Matrix Double -> [Complex Double]
matrixEigenvalues a = 
    -- 使用QR算法或其他数值方法计算特征值
    qrEigenvalues a

-- 稳定性分类
linearStabilityClassification :: LinearSystem -> StabilityType
linearStabilityClassification sys = 
    let a = systemMatrix sys
        eigenvalues = matrixEigenvalues a
        realParts = map realPart eigenvalues
        imaginaryParts = map imagPart eigenvalues
        
        hasPositiveReal = any (> 0) realParts
        hasZeroReal = any (== 0) realParts
        hasNonzeroImaginary = any (/= 0) imaginaryParts
    in if hasPositiveReal
        then Unstable
        else if hasZeroReal
            then if hasNonzeroImaginary
                then Stable  -- 临界稳定
                else Unstable  -- 多重零特征值
            else AsymptoticallyStable
```

### 3.2 赫尔维茨判据

**定义 3.1 (赫尔维茨多项式)**
多项式 $p(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$ 是赫尔维茨的，如果所有根都有负实部。

**定理 3.2 (赫尔维茨判据)**
多项式 $p(s)$ 是赫尔维茨的当且仅当赫尔维茨矩阵的所有主子式都为正。

**Haskell实现**：

```haskell
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
        buildRow i = 
            let row = replicate n 0
                start = max 0 (i - n + 1)
                end = min i n
            in [if j >= start && j <= end 
                then coeffs !! (i - j) 
                else 0 | j <- [0..n-1]]
    in matrix n (concat [buildRow i | i <- [0..2*n-1]])

-- 赫尔维茨稳定性检查
hurwitzStability :: LinearSystem -> Bool
hurwitzStability sys = 
    let a = systemMatrix sys
        characteristicPoly = characteristicPolynomial a
        coeffs = polynomialCoefficients characteristicPoly
    in hurwitzCriterion coeffs
```

### 3.3 劳斯判据

**定理 3.3 (劳斯判据)**
多项式 $p(s)$ 的所有根都有负实部当且仅当劳斯表的第一列所有元素都为正。

**Haskell实现**：

```haskell
-- 劳斯判据
routhCriterion :: [Double] -> Bool
routhCriterion coeffs = 
    let routhTable = buildRouthTable coeffs
        firstColumn = map head routhTable
    in all (> 0) firstColumn

-- 构建劳斯表
buildRouthTable :: [Double] -> [[Double]]
buildRouthTable coeffs = 
    let n = length coeffs - 1
        firstRow = [coeffs !! i | i <- [0,2..n]]
        secondRow = [coeffs !! i | i <- [1,3..n]]
        initialTable = [firstRow, secondRow]
        
        buildNextRow table = 
            let lastRow = last table
                secondLastRow = last (init table)
                newRow = calculateRouthRow secondLastRow lastRow
            in if length newRow <= 1
                then table
                else buildNextRow (table ++ [newRow])
    in buildNextRow initialTable

-- 计算劳斯行
calculateRouthRow :: [Double] -> [Double] -> [Double]
calculateRouthRow row1 row2 = 
    let a1 = head row1
        a2 = head row2
        elements = zipWith (\b1 b2 -> (a1 * b2 - a2 * b1) / a1) 
                          (tail row1) (tail row2)
    in elements
```

## 4. 频域稳定性

### 4.1 奈奎斯特判据

**定理 4.1 (奈奎斯特判据)**
闭环系统稳定的充要条件是奈奎斯特图不包围点 $(-1, 0)$。

**Haskell实现**：

```haskell
-- 奈奎斯特判据
nyquistCriterion :: TransferFunction -> Bool
nyquistCriterion tf = 
    let nyquistPlot = generateNyquistPlot tf
        encirclements = countEncirclements nyquistPlot (-1, 0)
        openLoopPoles = countUnstablePoles tf
    in encirclements == openLoopPoles

-- 生成奈奎斯特图
generateNyquistPlot :: TransferFunction -> [(Double, Double)]
generateNyquistPlot tf = 
    let frequencies = [0.001, 0.01..1000]
        evaluateAtFreq omega = 
            let s = 0 :+ omega
                g = evaluateTransferFunction tf s
                realPart = realPart g
                imagPart = imagPart g
            in (realPart, imagPart)
    in map evaluateAtFreq frequencies

-- 计算包围次数
countEncirclements :: [(Double, Double)] -> (Double, Double) -> Int
countEncirclements plot point = 
    let (px, py) = point
        angles = map (\(x, y) -> atan2 (y - py) (x - px)) plot
        angleChanges = zipWith (-) (tail angles) angles
        totalAngle = sum angleChanges
    in round (totalAngle / (2 * pi))
```

### 4.2 伯德图稳定性

**定义 4.1 (增益裕度)**
增益裕度是系统在相位交叉频率处的增益倒数。

**定义 4.2 (相位裕度)**
相位裕度是系统在增益交叉频率处的相位与 $-180^\circ$ 的差值。

**Haskell实现**：

```haskell
-- 伯德图稳定性分析
bodeStabilityAnalysis :: TransferFunction -> (Double, Double)
bodeStabilityAnalysis tf = 
    let (gainMargin, phaseMargin) = calculateMargins tf
    in (gainMargin, phaseMargin)

-- 计算裕度
calculateMargins :: TransferFunction -> (Double, Double)
calculateMargins tf = 
    let frequencies = [0.001, 0.01..1000]
        bodeData = map (\omega -> evaluateBodeData tf omega) frequencies
        
        -- 找到相位交叉频率（相位 = -180°）
        phaseCrossFreq = findPhaseCrossFrequency bodeData
        
        -- 找到增益交叉频率（增益 = 0 dB）
        gainCrossFreq = findGainCrossFrequency bodeData
        
        -- 计算增益裕度
        gainMargin = calculateGainMargin tf phaseCrossFreq
        
        -- 计算相位裕度
        phaseMargin = calculatePhaseMargin tf gainCrossFreq
    in (gainMargin, phaseMargin)

-- 伯德图数据
data BodeData = BodeData {
    frequency :: Double,
    magnitude :: Double,
    phase :: Double
}

-- 评估伯德图数据
evaluateBodeData :: TransferFunction -> Double -> BodeData
evaluateBodeData tf omega = 
    let s = 0 :+ omega
        g = evaluateTransferFunction tf s
        magnitude = 20 * log10 (magnitude g)
        phase = phase g * 180 / pi
    in BodeData omega magnitude phase
```

## 5. 非线性系统稳定性

### 5.1 局部稳定性

**定义 5.1 (局部稳定性)**
平衡点 $x_e$ 是局部渐近稳定的，如果存在邻域 $U$ 使得从 $U$ 内任意初始状态出发的轨迹都收敛到 $x_e$。

**Haskell实现**：

```haskell
-- 局部稳定性分析
localStabilityAnalysis :: (a -> a) -> a -> Bool
localStabilityAnalysis f x0 = 
    let -- 线性化系统
        jacobian = computeJacobian f x0
        linearizedSystem = LinearSystem jacobian (zeroMatrix n 1) (identityMatrix n) (zeroMatrix n 1)
        
        -- 检查线性化系统的稳定性
    in linearSystemStability linearizedSystem

-- 计算雅可比矩阵
computeJacobian :: (a -> a) -> a -> Matrix Double
computeJacobian f x0 = 
    let n = dimension x0
        h = 1e-8
        jacobianElements = 
            [computePartialDerivative f x0 i j h | i <- [0..n-1], j <- [0..n-1]]
    in matrix n jacobianElements

-- 计算偏导数
computePartialDerivative :: (a -> a) -> a -> Int -> Int -> Double -> Double
computePartialDerivative f x0 i j h = 
    let ei = unitVector n i
        ej = unitVector n j
        f1 = f (x0 + h * ej)
        f2 = f (x0 - h * ej)
    in (f1 - f2) / (2 * h)
```

### 5.2 全局稳定性

**定义 5.2 (全局稳定性)**
平衡点 $x_e$ 是全局渐近稳定的，如果从任意初始状态出发的轨迹都收敛到 $x_e$。

**Haskell实现**：

```haskell
-- 全局稳定性分析
globalStabilityAnalysis :: (a -> a) -> a -> Bool
globalStabilityAnalysis f x0 = 
    let -- 构造全局李雅普诺夫函数
        lyap = constructGlobalLyapunovFunction f x0
        
        -- 检查全局李雅普诺夫函数
    in isGlobalLyapunovFunction lyap x0 f

-- 构造全局李雅普诺夫函数
constructGlobalLyapunovFunction :: (a -> a) -> a -> LyapunovFunction a
constructGlobalLyapunovFunction f x0 = 
    -- 对于线性系统，可以使用二次型李雅普诺夫函数
    -- 对于非线性系统，需要根据具体系统构造
    undefined  -- 具体实现取决于系统类型
```

## 6. 应用示例

### 6.1 简单振荡器稳定性

**数学描述**：
$$\ddot{x} + \omega^2 x = 0$$

**Haskell实现**：

```haskell
-- 简单振荡器稳定性分析
oscillatorStabilityExample :: IO ()
oscillatorStabilityExample = do
    let omega = 1.0
        sys = simpleOscillator omega
        
        -- 特征值分析
        eigenvalues = matrixEigenvalues (systemMatrix sys)
        stability = linearSystemStability sys
        
        -- 李雅普诺夫函数分析
        lyap = constructLyapunovFunction sys
        lyapunovStable = lyapunovStabilityTheorem lyap (vector [0, 0]) (linearStateEquation sys)
    
    putStrLn "振荡器稳定性分析："
    putStrLn $ "特征值: " ++ show eigenvalues
    putStrLn $ "线性稳定性: " ++ show stability
    putStrLn $ "李雅普诺夫稳定性: " ++ show lyapunovStable
```

### 6.2 阻尼振荡器稳定性

**数学描述**：
$$\ddot{x} + 2\zeta\omega\dot{x} + \omega^2 x = 0$$

**Haskell实现**：

```haskell
-- 阻尼振荡器稳定性分析
dampedOscillatorStabilityExample :: IO ()
dampedOscillatorStabilityExample = do
    let omega = 1.0
        zeta = 0.5
        sys = dampedOscillator omega zeta
        
        -- 特征值分析
        eigenvalues = matrixEigenvalues (systemMatrix sys)
        stability = linearSystemStability sys
        
        -- 赫尔维茨判据
        hurwitzStable = hurwitzStability sys
        
        -- 劳斯判据
        characteristicPoly = characteristicPolynomial (systemMatrix sys)
        coeffs = polynomialCoefficients characteristicPoly
        routhStable = routhCriterion coeffs
    
    putStrLn "阻尼振荡器稳定性分析："
    putStrLn $ "特征值: " ++ show eigenvalues
    putStrLn $ "线性稳定性: " ++ show stability
    putStrLn $ "赫尔维茨稳定性: " ++ show hurwitzStable
    putStrLn $ "劳斯稳定性: " ++ show routhStable
```

## 总结

本文档建立了稳定性理论的形式化框架，包括：

1. **基本概念**：平衡点、稳定性定义
2. **李雅普诺夫方法**：李雅普诺夫函数、稳定性定理
3. **线性系统稳定性**：特征值判据、赫尔维茨判据、劳斯判据
4. **频域稳定性**：奈奎斯特判据、伯德图分析
5. **非线性系统稳定性**：局部稳定性、全局稳定性
6. **应用示例**：振荡器系统的稳定性分析

这个框架为控制系统的稳定性分析和设计提供了理论基础和实用工具。

---

**相关文档**：

- [系统动力学基础](./01-System-Dynamics.md)
- [反馈控制理论](./02-Feedback-Control.md)
- [最优控制](./04-Optimal-Control.md)
