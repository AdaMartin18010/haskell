# 量子计算基本概念 (Quantum Computing Basic Concepts)

## 概述

量子计算基本概念是理解量子计算理论的基础，包括量子比特、量子门、量子态等核心概念。本文档提供这些概念的严格数学定义和Haskell实现。

## 1. 量子比特 (Qubit)

### 1.1 数学定义

**定义 1.1.1 (量子比特)**
量子比特是二维希尔伯特空间 $\mathcal{H}_2 = \mathbb{C}^2$ 中的量子态：
$$|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$$

其中 $\alpha, \beta \in \mathbb{C}$ 满足归一化条件：
$$|\alpha|^2 + |\beta|^2 = 1$$

**定义 1.1.2 (计算基)**
计算基是二维希尔伯特空间的标准正交基：
$$|0\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \quad |1\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix}$$

**定义 1.1.3 (Bloch球表示)**
量子比特可以用Bloch球表示：
$$|\psi\rangle = \cos\frac{\theta}{2}|0\rangle + e^{i\phi}\sin\frac{\theta}{2}|1\rangle$$

其中 $\theta \in [0, \pi]$ 和 $\phi \in [0, 2\pi]$ 是球坐标。

### 1.2 Haskell实现

```haskell
-- 量子比特类型
data Qubit = Qubit { amplitude0 :: Complex Double
                   , amplitude1 :: Complex Double
                   } deriving (Show, Eq)

-- 计算基态
zero :: Qubit
zero = Qubit 1 0

one :: Qubit
one = Qubit 0 1

-- 归一化检查
isNormalized :: Qubit -> Bool
isNormalized (Qubit a b) = 
    abs (magnitude a ^ 2 + magnitude b ^ 2 - 1) < 1e-10

-- 归一化函数
normalize :: Qubit -> Qubit
normalize (Qubit a b) = 
    let norm = sqrt (magnitude a ^ 2 + magnitude b ^ 2)
    in Qubit (a / (norm :+ 0)) (b / (norm :+ 0))

-- Bloch球表示
data BlochSphere = BlochSphere { theta :: Double  -- [0, π]
                               , phi :: Double     -- [0, 2π]
                               } deriving (Show, Eq)

-- 从Bloch球到量子比特
blochToQubit :: BlochSphere -> Qubit
blochToQubit (BlochSphere theta phi) =
    let cosHalfTheta = cos (theta / 2)
        sinHalfTheta = sin (theta / 2)
        phase = cos phi :+ sin phi
    in Qubit cosHalfTheta (phase * sinHalfTheta)

-- 从量子比特到Bloch球
qubitToBloch :: Qubit -> BlochSphere
qubitToBloch (Qubit a b) =
    let r0 = magnitude a
        r1 = magnitude b
        theta = 2 * atan2 r1 r0
        phi = phase b
    in BlochSphere theta phi

-- 量子比特的测量
measureQubit :: Qubit -> IO Bool
measureQubit (Qubit a b) = do
    let prob0 = magnitude a ^ 2
        prob1 = magnitude b ^ 2
    random <- randomRIO (0, 1)
    return $ random > prob0

-- 量子比特的克隆（不可行）
-- 注意：量子不可克隆定理表明这是不可能的
-- 这里只是演示概念
cloneQubit :: Qubit -> (Qubit, Qubit)
cloneQubit q = (q, q)  -- 这只是复制引用，不是真正的克隆
```

### 1.3 量子不可克隆定理

**定理 1.3.1 (量子不可克隆定理)**
不存在能够完美克隆任意未知量子态的量子操作。

**证明：**
假设存在克隆操作 $U$，对于任意量子态 $|\psi\rangle$：
$$U(|\psi\rangle \otimes |0\rangle) = |\psi\rangle \otimes |\psi\rangle$$

考虑两个不同的量子态 $|\psi\rangle$ 和 $|\phi\rangle$：
$$U(|\psi\rangle \otimes |0\rangle) = |\psi\rangle \otimes |\psi\rangle$$
$$U(|\phi\rangle \otimes |0\rangle) = |\phi\rangle \otimes |\phi\rangle$$

由于 $U$ 是酉操作，保持内积：
$$\langle\psi|\phi\rangle = \langle\psi|\phi\rangle^2$$

这意味着 $\langle\psi|\phi\rangle = 0$ 或 $\langle\psi|\phi\rangle = 1$，即 $|\psi\rangle$ 和 $|\phi\rangle$ 要么正交，要么相同。这与"任意未知量子态"的假设矛盾。

## 2. 量子门 (Quantum Gates)

### 2.1 数学定义

**定义 2.1.1 (量子门)**
量子门是希尔伯特空间上的酉算子 $U : \mathcal{H} \rightarrow \mathcal{H}$，满足：
$$U^\dagger U = UU^\dagger = I$$

**定义 2.1.2 (单量子比特门)**
单量子比特门是 $2 \times 2$ 的酉矩阵。

**定义 2.1.3 (Pauli门)**
Pauli门是基本的单量子比特门：

- **X门（NOT门）**：
$$X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$$

- **Y门**：
$$Y = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}$$

- **Z门**：
$$Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$$

**定义 2.1.4 (Hadamard门)**
Hadamard门：
$$H = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$$

**定义 2.1.5 (相位门)**
相位门：
$$S = \begin{pmatrix} 1 & 0 \\ 0 & i \end{pmatrix}$$

### 2.2 Haskell实现

```haskell
-- 量子门类型
data QuantumGate = PauliX | PauliY | PauliZ | Hadamard | Phase
                 | RotX Double | RotY Double | RotZ Double
                 | Custom (Matrix (Complex Double))
                 deriving (Show, Eq)

-- 矩阵类型（简化实现）
type Matrix a = [[a]]

-- 单位矩阵
identity :: Num a => Int -> Matrix a
identity n = [[if i == j then 1 else 0 | j <- [0..n-1]] | i <- [0..n-1]]

-- 矩阵乘法
matrixMultiply :: Num a => Matrix a -> Matrix a -> Matrix a
matrixMultiply a b = 
    [[sum [a !! i !! k * b !! k !! j | k <- [0..length (head a) - 1]]
      | j <- [0..length (head b) - 1]]
     | i <- [0..length a - 1]]

-- 共轭转置
conjugateTranspose :: Matrix (Complex Double) -> Matrix (Complex Double)
conjugateTranspose m = 
    [[conjugate (m !! j !! i) | j <- [0..length m - 1]]
     | i <- [0..length (head m) - 1]]

-- 检查酉性
isUnitary :: Matrix (Complex Double) -> Bool
isUnitary m = 
    let m' = conjugateTranspose m
        product = matrixMultiply m m'
        identity = identity (length m)
    in all (\i -> all (\j -> abs (product !! i !! j - identity !! i !! j) < 1e-10)
                      [0..length (head product) - 1])
           [0..length product - 1]

-- Pauli门矩阵
pauliX :: Matrix (Complex Double)
pauliX = [[0, 1], [1, 0]]

pauliY :: Matrix (Complex Double)
pauliY = [[0, -i], [i, 0]]
  where i = 0 :+ 1

pauliZ :: Matrix (Complex Double)
pauliZ = [[1, 0], [0, -1]]

-- Hadamard门矩阵
hadamard :: Matrix (Complex Double)
hadamard = [[1/sqrt2, 1/sqrt2], [1/sqrt2, -1/sqrt2]]
  where sqrt2 = sqrt 2

-- 相位门矩阵
phase :: Matrix (Complex Double)
phase = [[1, 0], [0, i]]
  where i = 0 :+ 1

-- 旋转门
rotationX :: Double -> Matrix (Complex Double)
rotationX theta = 
    let cosHalf = cos (theta / 2) :+ 0
        sinHalf = sin (theta / 2) :+ 0
    in [[cosHalf, -i * sinHalf], [-i * sinHalf, cosHalf]]
  where i = 0 :+ 1

rotationY :: Double -> Matrix (Complex Double)
rotationY theta = 
    let cosHalf = cos (theta / 2) :+ 0
        sinHalf = sin (theta / 2) :+ 0
    in [[cosHalf, -sinHalf], [sinHalf, cosHalf]]

rotationZ :: Double -> Matrix (Complex Double)
rotationZ theta = 
    let expHalf = exp (i * theta / 2)
        expNegHalf = exp (-i * theta / 2)
    in [[expNegHalf, 0], [0, expHalf]]
  where i = 0 :+ 1

-- 应用量子门到量子比特
applyGate :: Matrix (Complex Double) -> Qubit -> Qubit
applyGate gate (Qubit a b) =
    let vector = [[a], [b]]
        result = matrixMultiply gate vector
    in Qubit (result !! 0 !! 0) (result !! 1 !! 0)

-- 门操作函数
applyPauliX :: Qubit -> Qubit
applyPauliX = applyGate pauliX

applyPauliY :: Qubit -> Qubit
applyPauliY = applyGate pauliY

applyPauliZ :: Qubit -> Qubit
applyPauliZ = applyGate pauliZ

applyHadamard :: Qubit -> Qubit
applyHadamard = applyGate hadamard

applyPhase :: Qubit -> Qubit
applyPhase = applyGate phase

-- 门序列应用
applyGateSequence :: [Matrix (Complex Double)] -> Qubit -> Qubit
applyGateSequence gates qubit = foldl (flip applyGate) qubit gates
```

### 2.3 量子门的性质

**定理 2.3.1 (量子门的线性性)**
量子门是线性操作：
$$U(\alpha|\psi\rangle + \beta|\phi\rangle) = \alpha U|\psi\rangle + \beta U|\phi\rangle$$

**定理 2.3.2 (量子门的可逆性)**
所有量子门都是可逆的，逆门是共轭转置：
$$U^{-1} = U^\dagger$$

**定理 2.3.3 (量子门的保范性)**
量子门保持量子态的范数：
$$\|U|\psi\rangle\| = \||\psi\rangle\|$$

## 3. 量子态 (Quantum States)

### 3.1 数学定义

**定义 3.1.1 (纯态)**
纯态是希尔伯特空间中的单位向量：
$$|\psi\rangle \in \mathcal{H}, \quad \langle\psi|\psi\rangle = 1$$

**定义 3.1.2 (混合态)**
混合态是纯态的统计混合，用密度矩阵表示：
$$\rho = \sum_i p_i |\psi_i\rangle\langle\psi_i|$$

其中 $p_i \geq 0$ 且 $\sum_i p_i = 1$。

**定义 3.1.3 (密度矩阵)**
密度矩阵是满足以下条件的厄米矩阵：
1. $\rho = \rho^\dagger$（厄米性）
2. $\text{Tr}(\rho) = 1$（归一化）
3. $\rho \geq 0$（正定性）

### 3.2 Haskell实现

```haskell
-- 密度矩阵类型
data DensityMatrix = DensityMatrix { 
    matrix :: Matrix (Complex Double)
    } deriving (Show, Eq)

-- 从纯态创建密度矩阵
pureStateToDensity :: Qubit -> DensityMatrix
pureStateToDensity (Qubit a b) =
    let ket = [[a], [b]]
        bra = [[conjugate a, conjugate b]]
        outer = matrixMultiply ket bra
    in DensityMatrix outer

-- 从密度矩阵到纯态（如果可能）
densityToPureState :: DensityMatrix -> Maybe Qubit
densityToPureState (DensityMatrix m) =
    -- 检查是否为纯态（秩为1）
    if rank m == 1 then
        let eigenvector = principalEigenvector m
        in Just $ Qubit (eigenvector !! 0) (eigenvector !! 1)
    else
        Nothing

-- 混合态
data MixedState = MixedState {
    components :: [(Double, Qubit)]  -- (概率, 纯态)
    } deriving (Show, Eq)

-- 从混合态创建密度矩阵
mixedStateToDensity :: MixedState -> DensityMatrix
mixedStateToDensity (MixedState components) =
    let densityMatrices = map (\(p, q) -> 
            scaleMatrix p (pureStateToDensity q)) components
    in sumDensityMatrices densityMatrices

-- 矩阵缩放
scaleMatrix :: Double -> DensityMatrix -> DensityMatrix
scaleMatrix s (DensityMatrix m) =
    DensityMatrix [[s * x | x <- row] | row <- m]

-- 密度矩阵求和
sumDensityMatrices :: [DensityMatrix] -> DensityMatrix
sumDensityMatrices matrices =
    let matrices' = map matrix matrices
        n = length (head (head matrices'))
        m = length (head matrices')
    in DensityMatrix [[sum [matrices' !! k !! i !! j | k <- [0..length matrices' - 1]]
                       | j <- [0..m-1]]
                      | i <- [0..n-1]]

-- 迹
trace :: Matrix (Complex Double) -> Complex Double
trace m = sum [m !! i !! i | i <- [0..length m - 1]]

-- 检查密度矩阵的有效性
isValidDensityMatrix :: DensityMatrix -> Bool
isValidDensityMatrix (DensityMatrix m) =
    let tr = trace m
        isHermitian = isUnitary m  -- 简化检查
        isPositive = all (\i -> realPart (m !! i !! i) >= 0) [0..length m - 1]
    in abs (realPart tr - 1) < 1e-10 && isHermitian && isPositive

-- 冯·诺依曼熵
vonNeumannEntropy :: DensityMatrix -> Double
vonNeumannEntropy (DensityMatrix m) =
    let eigenvalues = realEigenvalues m
        entropy = -sum [lambda * logBase 2 lambda | lambda <- eigenvalues, lambda > 0]
    in entropy

-- 量子态的保真度
fidelity :: Qubit -> Qubit -> Double
fidelity (Qubit a1 b1) (Qubit a2 b2) =
    let overlap = a1 * conjugate a2 + b1 * conjugate b2
    in magnitude overlap

-- 量子态的保真度（密度矩阵版本）
fidelityDensity :: DensityMatrix -> DensityMatrix -> Double
fidelityDensity (DensityMatrix rho1) (DensityMatrix rho2) =
    let sqrtRho1 = matrixSqrt rho1
        product = matrixMultiply (matrixMultiply sqrtRho1 rho2) sqrtRho1
        eigenvalues = realEigenvalues product
    in sum [sqrt lambda | lambda <- eigenvalues, lambda > 0]
```

### 3.3 量子态的性质

**定理 3.3.1 (量子态的叠加原理)**
量子系统可以处于多个态的叠加：
$$|\psi\rangle = \sum_i \alpha_i |\psi_i\rangle$$

**定理 3.3.2 (量子态的纠缠)**
多量子比特系统可以处于纠缠态，无法分解为单个量子比特的乘积。

**定理 3.3.3 (量子态的测量)**
量子态的测量会改变量子态，测量是不可逆的。

## 4. 量子测量 (Quantum Measurement)

### 4.1 数学定义

**定义 4.1.1 (投影测量)**
投影测量由投影算子 $\{P_i\}$ 描述，满足：
$$\sum_i P_i = I, \quad P_i P_j = \delta_{ij} P_i$$

**定义 4.1.2 (测量概率)**
测量结果 $i$ 的概率：
$$P(i) = \langle\psi|P_i|\psi\rangle$$

**定义 4.1.3 (测量后态)**
测量后的量子态：
$$|\psi_i\rangle = \frac{P_i|\psi\rangle}{\sqrt{P(i)}}$$

### 4.2 Haskell实现

```haskell
-- 测量算子类型
data MeasurementOperator = Projection {
    projector :: Matrix (Complex Double)
    } deriving (Show, Eq)

-- 测量结果
data MeasurementResult = MeasurementResult {
    outcome :: Int,
    probability :: Double,
    postMeasurementState :: Qubit
    } deriving (Show, Eq)

-- 投影测量
projectionMeasurement :: [Matrix (Complex Double)] -> Qubit -> IO MeasurementResult
projectionMeasurement projectors qubit = do
    let probabilities = map (\p -> realPart (measurementProbability p qubit)) projectors
        cumulative = scanl1 (+) probabilities
    random <- randomRIO (0, 1)
    let outcome = length (takeWhile (<= random) cumulative)
        selectedProjector = projectors !! outcome
        prob = probabilities !! outcome
        postState = applyGate selectedProjector qubit
        normalizedPostState = normalize postState
    return $ MeasurementResult outcome prob normalizedPostState

-- 测量概率
measurementProbability :: Matrix (Complex Double) -> Qubit -> Complex Double
measurementProbability projector (Qubit a b) =
    let ket = [[a], [b]]
        bra = [[conjugate a, conjugate b]]
        result = matrixMultiply (matrixMultiply bra projector) ket
    in result !! 0 !! 0

-- 计算基测量
computationalBasisMeasurement :: Qubit -> IO Bool
computationalBasisMeasurement qubit = do
    let projectors = [pauliZ, matrixSubtract identity pauliZ]
    result <- projectionMeasurement projectors qubit
    return $ result.outcome == 0

-- Bell态测量
bellStateMeasurement :: (Qubit, Qubit) -> IO Int
bellStateMeasurement (q1, q2) = do
    -- Bell态投影算子
    let bellStates = [bellState00, bellState01, bellState10, bellState11]
        projectors = map (\state -> outerProduct state state) bellStates
    result <- projectionMeasurement projectors (entangle q1 q2)
    return result.outcome

-- Bell态
bellState00 :: [Complex Double]
bellState00 = [1/sqrt2, 0, 0, 1/sqrt2]
  where sqrt2 = sqrt 2

bellState01 :: [Complex Double]
bellState01 = [0, 1/sqrt2, 1/sqrt2, 0]
  where sqrt2 = sqrt 2

bellState10 :: [Complex Double]
bellState10 = [1/sqrt2, 0, 0, -1/sqrt2]
  where sqrt2 = sqrt 2

bellState11 :: [Complex Double]
bellState11 = [0, 1/sqrt2, -1/sqrt2, 0]
  where sqrt2 = sqrt 2

-- 外积
outerProduct :: [Complex Double] -> [Complex Double] -> Matrix (Complex Double)
outerProduct ket bra = [[k * conjugate b | b <- bra] | k <- ket]

-- 矩阵减法
matrixSubtract :: Num a => Matrix a -> Matrix a -> Matrix a
matrixSubtract a b = [[a !! i !! j - b !! i !! j | j <- [0..length (head a) - 1]]
                      | i <- [0..length a - 1]]

-- 纠缠两个量子比特
entangle :: Qubit -> Qubit -> Qubit  -- 简化的双量子比特表示
entangle (Qubit a1 b1) (Qubit a2 b2) =
    Qubit (a1 * a2) (b1 * b2)  -- 简化的张量积
```

## 5. 量子纠缠 (Quantum Entanglement)

### 5.1 数学定义

**定义 5.1.1 (纠缠态)**
双量子比特系统的纠缠态：
$$|\psi\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$$

**定义 5.1.2 (Schmidt分解)**
任意双量子比特态可以表示为：
$$|\psi\rangle = \sum_i \lambda_i |i_A\rangle \otimes |i_B\rangle$$

其中 $\lambda_i$ 是Schmidt系数。

### 5.2 Haskell实现

```haskell
-- 双量子比特系统
data TwoQubitSystem = TwoQubit {
    qubit1 :: Qubit,
    qubit2 :: Qubit
    } deriving (Show, Eq)

-- Bell态
bellState00 :: TwoQubitSystem
bellState00 = TwoQubit (Qubit (1/sqrt2) 0) (Qubit (1/sqrt2) 0)
  where sqrt2 = sqrt 2

bellState01 :: TwoQubitSystem
bellState01 = TwoQubit (Qubit (1/sqrt2) 0) (Qubit 0 (1/sqrt2))
  where sqrt2 = sqrt 2

bellState10 :: TwoQubitSystem
bellState10 = TwoQubit (Qubit (1/sqrt2) 0) (Qubit (1/sqrt2) 0)
  where sqrt2 = sqrt 2

bellState11 :: TwoQubitSystem
bellState11 = TwoQubit (Qubit (1/sqrt2) 0) (Qubit 0 (1/sqrt2))
  where sqrt2 = sqrt 2

-- 纠缠度量
concurrence :: TwoQubitSystem -> Double
concurrence (TwoQubit q1 q2) =
    let density = pureStateToDensity (entangle q1 q2)
        -- 简化的纠缠度量
        eigenvalues = realEigenvalues (matrix density)
    in maximum eigenvalues

-- 部分迹
partialTrace :: TwoQubitSystem -> Qubit
partialTrace (TwoQubit q1 q2) = q1  -- 简化的部分迹

-- 量子隐形传态
quantumTeleportation :: Qubit -> TwoQubitSystem -> IO Qubit
quantumTeleportation state (TwoQubit alice qubit) = do
    -- 1. Alice和Bob共享Bell态
    let bellState = bellState00
    
    -- 2. Alice对要传输的态和她的Bell态进行Bell测量
    measurement <- bellStateMeasurement (state, alice)
    
    -- 3. Alice将测量结果发送给Bob
    let correction = case measurement of
            0 -> id
            1 -> applyPauliX
            2 -> applyPauliZ
            3 -> applyPauliX . applyPauliZ
    
    -- 4. Bob根据测量结果进行修正
    return $ correction qubit
```

## 6. 量子算法基础

### 6.1 量子并行性

**定义 6.1.1 (量子并行性)**
量子并行性允许量子计算机同时处理多个输入：
$$U_f(|x\rangle \otimes |0\rangle) = |x\rangle \otimes |f(x)\rangle$$

### 6.2 Haskell实现

```haskell
-- 量子函数评估
quantumFunctionEvaluation :: (Int -> Int) -> Qubit -> Qubit -> Qubit
quantumFunctionEvaluation f input output =
    let inputValue = qubitToInt input
        outputValue = f inputValue
        newOutput = intToQubit outputValue
    in newOutput

-- 量子比特到整数（简化）
qubitToInt :: Qubit -> Int
qubitToInt (Qubit a b) = if magnitude a > magnitude b then 0 else 1

-- 整数到量子比特（简化）
intToQubit :: Int -> Qubit
intToQubit 0 = zero
intToQubit 1 = one
intToQubit _ = error "Invalid qubit value"

-- 量子并行计算
quantumParallelComputation :: (Int -> Int) -> [Qubit] -> [Qubit]
quantumParallelComputation f inputs =
    let outputs = map (\input -> quantumFunctionEvaluation f input zero) inputs
    in outputs

-- Deutsch算法
deutschAlgorithm :: (Int -> Int) -> IO Bool
deutschAlgorithm f = do
    -- 准备输入态
    let input1 = applyHadamard zero
        input2 = applyHadamard one
    
    -- 应用Oracle
    let output1 = quantumFunctionEvaluation f input1 zero
        output2 = quantumFunctionEvaluation f input2 zero
    
    -- 应用Hadamard门
    let final1 = applyHadamard output1
        final2 = applyHadamard output2
    
    -- 测量
    result1 <- measureQubit final1
    result2 <- measureQubit final2
    
    -- 判断函数是否平衡
    return $ result1 /= result2
```

## 7. 量子错误纠正基础

### 7.1 数学定义

**定义 7.1.1 (量子错误)**
量子错误包括：
- **比特翻转错误**：$X$ 门错误
- **相位翻转错误**：$Z$ 门错误
- **组合错误**：$Y$ 门错误

**定义 7.1.2 (量子编码)**
量子编码将逻辑量子比特编码为多个物理量子比特：
$$|0_L\rangle = \frac{1}{\sqrt{2}}(|000\rangle + |111\rangle)$$
$$|1_L\rangle = \frac{1}{\sqrt{2}}(|000\rangle - |111\rangle)$$

### 7.2 Haskell实现

```haskell
-- 三量子比特编码
data LogicalQubit = LogicalQubit {
    physicalQubits :: [Qubit]
    } deriving (Show, Eq)

-- 编码
encode :: Qubit -> LogicalQubit
encode (Qubit a b) =
    let encoded0 = Qubit (a/sqrt2) (a/sqrt2)  -- |0_L>
        encoded1 = Qubit (b/sqrt2) (-b/sqrt2) -- |1_L>
    in LogicalQubit [encoded0, encoded1]
  where sqrt2 = sqrt 2

-- 解码
decode :: LogicalQubit -> Qubit
decode (LogicalQubit qubits) =
    let q0 = qubits !! 0
        q1 = qubits !! 1
        -- 简化的解码
        a = amplitude0 q0 + amplitude0 q1
        b = amplitude1 q0 + amplitude1 q1
    in normalize $ Qubit a b

-- 错误检测
detectError :: LogicalQubit -> Maybe QuantumGate
detectError (LogicalQubit qubits) =
    let q0 = qubits !! 0
        q1 = qubits !! 1
        q2 = qubits !! 2
        
        -- 检查比特翻转错误
        bitFlipError = measureQubit q0 /= measureQubit q1
        
        -- 检查相位翻转错误
        phaseFlipError = measureQubit q1 /= measureQubit q2
        
    in case (bitFlipError, phaseFlipError) of
        (True, False) -> Just PauliX
        (False, True) -> Just PauliZ
        (True, True) -> Just PauliY
        (False, False) -> Nothing

-- 错误纠正
correctError :: LogicalQubit -> LogicalQubit
correctError logicalQubit =
    case detectError logicalQubit of
        Just PauliX -> applyCorrection PauliX logicalQubit
        Just PauliZ -> applyCorrection PauliZ logicalQubit
        Just PauliY -> applyCorrection PauliY logicalQubit
        Nothing -> logicalQubit

-- 应用纠正
applyCorrection :: QuantumGate -> LogicalQubit -> LogicalQubit
applyCorrection gate (LogicalQubit qubits) =
    let correctedQubits = map (\q -> applyGate (gateToMatrix gate) q) qubits
    in LogicalQubit correctedQubits

-- 门到矩阵
gateToMatrix :: QuantumGate -> Matrix (Complex Double)
gateToMatrix PauliX = pauliX
gateToMatrix PauliY = pauliY
gateToMatrix PauliZ = pauliZ
gateToMatrix Hadamard = hadamard
gateToMatrix Phase = phase
gateToMatrix (RotX theta) = rotationX theta
gateToMatrix (RotY theta) = rotationY theta
gateToMatrix (RotZ theta) = rotationZ theta
gateToMatrix (Custom m) = m
```

## 总结

本文档介绍了量子计算的基本概念，包括：

1. **量子比特**：量子计算的基本单位
2. **量子门**：量子计算的基本操作
3. **量子态**：量子系统的状态描述
4. **量子测量**：从量子态获取经典信息
5. **量子纠缠**：量子系统的独特性质
6. **量子算法基础**：量子计算的基本原理
7. **量子错误纠正**：保护量子信息的方法

每个概念都提供了严格的数学定义和对应的Haskell实现，为理解量子计算理论提供了坚实的基础。

---

**最后更新**: 2024年12月  
**维护者**: 形式化知识体系项目组  
**版本**: 1.0 