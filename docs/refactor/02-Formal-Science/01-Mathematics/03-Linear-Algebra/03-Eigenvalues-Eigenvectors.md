# 特征值与特征向量理论

## 概述

特征值与特征向量是线性代数中最重要的概念之一，它们在矩阵对角化、谱理论、量子力学等领域有广泛应用。本文档提供特征值与特征向量的严格数学定义、性质证明和Haskell实现。

## 数学定义

### 特征值与特征向量

设 $T: V \to V$ 是向量空间 $V$ 上的线性变换，$\lambda \in \mathbb{F}$ 是标量，$\mathbf{v} \in V$ 是非零向量。如果：
$$T(\mathbf{v}) = \lambda\mathbf{v}$$
则称 $\lambda$ 是 $T$ 的特征值，$\mathbf{v}$ 是 $T$ 对应于特征值 $\lambda$ 的特征向量。

### 特征多项式

设 $A$ 是 $n \times n$ 矩阵，$I$ 是 $n \times n$ 单位矩阵，则：
$$p_A(\lambda) = \det(A - \lambda I)$$
称为矩阵 $A$ 的特征多项式。

特征值是特征多项式的根，即满足 $p_A(\lambda) = 0$ 的 $\lambda$ 值。

### 特征空间

设 $\lambda$ 是线性变换 $T$ 的特征值，则：
$$E_\lambda = \{\mathbf{v} \in V \mid T(\mathbf{v}) = \lambda\mathbf{v}\} = \ker(T - \lambda I)$$
称为 $T$ 对应于特征值 $\lambda$ 的特征空间。

### 代数重数与几何重数

**代数重数**：特征值 $\lambda$ 在特征多项式中作为根的重数。

**几何重数**：特征值 $\lambda$ 对应的特征空间的维数，即 $\dim(E_\lambda)$。

**定理**：几何重数 ≤ 代数重数。

### 对角化

设 $T: V \to V$ 是线性变换，如果存在 $V$ 的基 $B$ 使得 $T$ 关于基 $B$ 的矩阵是对角矩阵，则称 $T$ 是可对角化的。

等价地，$T$ 可对角化当且仅当 $V$ 有由 $T$ 的特征向量构成的基。

## Haskell实现

### 特征值与特征向量类型类

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- 特征值与特征向量类型类
class LinearTransformation t v v => EigenSystem t v where
    -- 计算特征值
    eigenvalues :: t -> [Scalar v]
    
    -- 计算特征向量
    eigenvectors :: t -> [(Scalar v, [v])]
    
    -- 计算特征空间
    eigenspace :: t -> Scalar v -> [v]
    eigenspace t lambda = 
        let (_, vectors) = head [(l, vs) | (l, vs) <- eigenvectors t, l == lambda]
        in vectors
    
    -- 代数重数
    algebraicMultiplicity :: t -> Scalar v -> Int
    algebraicMultiplicity t lambda = 
        length [l | l <- eigenvalues t, l == lambda]
    
    -- 几何重数
    geometricMultiplicity :: t -> Scalar v -> Int
    geometricMultiplicity t lambda = 
        dimension (eigenspace t lambda)
    
    -- 验证特征值-特征向量对
    verifyEigenpair :: t -> Scalar v -> v -> Bool
    verifyEigenpair t lambda v = 
        apply t v == scale lambda v

-- 矩阵特征系统
class MatrixEigenSystem m where
    -- 矩阵特征多项式
    characteristicPolynomial :: m -> Polynomial
    
    -- 矩阵特征值
    matrixEigenvalues :: m -> [Complex Double]
    
    -- 矩阵特征向量
    matrixEigenvectors :: m -> [(Complex Double, [Vector n Double])]
```

### 特征多项式计算

```haskell
-- 多项式类型
data Polynomial = Polynomial { coefficients :: [Double] }
    deriving (Eq, Show)

-- 特征多项式计算
characteristicPolynomial :: Matrix n n Double -> Polynomial
characteristicPolynomial matrix = 
    let n = matrixDimension matrix
        identity = identityMatrix n
        -- 计算 det(A - λI)
        det = determinant (subtractMatrix matrix (scaleMatrix identity lambda))
    in Polynomial (coefficientsFromDeterminant det)

-- 行列式计算
determinant :: Matrix n n Double -> Double
determinant (Matrix [[]]) = 0
determinant (Matrix [[a]]) = a
determinant matrix = 
    let n = matrixDimension matrix
        -- 拉普拉斯展开
        cofactors = [cofactor matrix 0 j | j <- [0..n-1]]
        firstRow = head (unMatrix matrix)
    in sum (zipWith (*) firstRow cofactors)

-- 余因子
cofactor :: Matrix n n Double -> Int -> Int -> Double
cofactor matrix i j = 
    let minor = minorMatrix matrix i j
        sign = (-1) ^ (i + j)
    in sign * determinant minor

-- 子矩阵
minorMatrix :: Matrix n n Double -> Int -> Int -> Matrix (n-1) (n-1) Double
minorMatrix matrix i j = 
    let rows = unMatrix matrix
        -- 删除第i行和第j列
        minorRows = [deleteAt j row | (k, row) <- zip [0..] rows, k /= i]
    in Matrix minorRows

-- 删除列表中指定位置的元素
deleteAt :: Int -> [a] -> [a]
deleteAt i xs = take i xs ++ drop (i+1) xs
```

### 特征值计算算法

```haskell
-- 幂迭代法计算主特征值
powerIteration :: Matrix n n Double -> Vector n Double -> Int -> (Double, Vector n Double)
powerIteration matrix initialVector maxIterations = 
    iteratePower matrix initialVector 0
  where
    iteratePower matrix vector iteration
        | iteration >= maxIterations = 
            let eigenvalue = rayleighQuotient matrix vector
            in (eigenvalue, vector)
        | otherwise = 
            let newVector = normalize (matrixVectorMultiply matrix vector)
                eigenvalue = rayleighQuotient matrix newVector
            in iteratePower matrix newVector (iteration + 1)

-- 瑞利商
rayleighQuotient :: Matrix n n Double -> Vector n Double -> Double
rayleighQuotient matrix vector = 
    let numerator = innerProduct (matrixVectorMultiply matrix vector) vector
        denominator = innerProduct vector vector
    in numerator / denominator

-- 向量归一化
normalize :: Vector n Double -> Vector n Double
normalize (Vector xs) = 
    let norm = sqrt (sum (map (^2) xs))
    in Vector (map (/ norm) xs)

-- QR算法计算所有特征值
qrAlgorithm :: Matrix n n Double -> Int -> [Double]
qrAlgorithm matrix maxIterations = 
    iterateQR matrix 0
  where
    iterateQR matrix iteration
        | iteration >= maxIterations = 
            -- 提取对角线元素作为特征值近似
            diagonalElements matrix
        | otherwise = 
            let (q, r) = qrDecomposition matrix
                newMatrix = matrixMultiply r q
            in iterateQR newMatrix (iteration + 1)

-- QR分解
qrDecomposition :: Matrix n n Double -> (Matrix n n Double, Matrix n n Double)
qrDecomposition matrix = 
    let columns = transpose (unMatrix matrix)
        (qColumns, rMatrix) = gramSchmidt columns
        qMatrix = Matrix (transpose qColumns)
    in (qMatrix, rMatrix)

-- 格拉姆-施密特正交化
gramSchmidt :: [[Double]] -> ([[Double]], [[Double]])
gramSchmidt columns = 
    let orthogonalized = foldl orthogonalize [] columns
        normalized = map normalizeVector orthogonalized
        rMatrix = computeRMatrix columns normalized
    in (normalized, rMatrix)

-- 正交化过程
orthogonalize :: [[Double]] -> [Double] -> [Double]
orthogonalize [] column = column
orthogonalize (q:qs) column = 
    let projection = projectOnto column q
        orthogonal = subtractVectors column projection
    in orthogonalize qs orthogonal

-- 向量投影
projectOnto :: [Double] -> [Double] -> [Double]
projectOnto u v = 
    let dot = sum (zipWith (*) u v)
        normSq = sum (map (^2) v)
        scalar = dot / normSq
    in map (* scalar) v

-- 向量减法
subtractVectors :: [Double] -> [Double] -> [Double]
subtractVectors = zipWith (-)
```

### 特征向量计算

```haskell
-- 计算特征向量
computeEigenvectors :: Matrix n n Double -> [Double] -> [(Double, [Vector n Double])]
computeEigenvectors matrix eigenvalues = 
    map (\lambda -> (lambda, eigenvectorsForEigenvalue matrix lambda)) eigenvalues

-- 计算特定特征值对应的特征向量
eigenvectorsForEigenvalue :: Matrix n n Double -> Double -> [Vector n Double]
eigenvectorsForEigenvalue matrix lambda = 
    let n = matrixDimension matrix
        identity = identityMatrix n
        -- 计算 A - λI
        shiftedMatrix = subtractMatrix matrix (scaleMatrix identity lambda)
        -- 求解 (A - λI)v = 0
        nullSpace = computeNullSpace shiftedMatrix
    in nullSpace

-- 计算零空间
computeNullSpace :: Matrix n n Double -> [Vector n Double]
computeNullSpace matrix = 
    let (rref, pivotColumns) = reducedRowEchelonForm matrix
        freeVariables = [i | i <- [0..matrixDimension matrix - 1], i `notElem` pivotColumns]
        -- 为每个自由变量构造基础解
        basisVectors = map (constructBasisVector rref pivotColumns freeVariables) freeVariables
    in basisVectors

-- 构造基础解向量
constructBasisVector :: Matrix n n Double -> [Int] -> [Int] -> Int -> Vector n Double
constructBasisVector rref pivotColumns freeVariables freeVar = 
    let n = matrixDimension rref
        vector = replicate n 0
        -- 设置自由变量为1
        vector1 = setAt vector freeVar 1
        -- 根据RREF计算其他变量
        finalVector = solveFromRREF rref pivotColumns vector1
    in Vector finalVector

-- 从RREF求解
solveFromRREF :: Matrix n n Double -> [Int] -> [Double] -> [Double]
solveFromRREF rref pivotColumns solution = 
    let rows = reverse (unMatrix rref)  -- 从下往上求解
        pivotRows = reverse pivotColumns
    in foldl solveRow solution (zip rows pivotRows)
  where
    solveRow solution (row, pivotCol) = 
        let value = solution !! pivotCol
            -- 计算其他变量的值
            newSolution = updateSolution solution row pivotCol value
        in newSolution

-- 更新解向量
updateSolution :: [Double] -> [Double] -> Int -> Double -> [Double]
updateSolution solution row pivotCol value = 
    let coefficients = zipWith (*) row solution
        sum = sum coefficients
        newValue = (value - sum) / (row !! pivotCol)
    in setAt solution pivotCol newValue

-- 设置列表中指定位置的元素
setAt :: [a] -> Int -> a -> [a]
setAt xs i x = take i xs ++ [x] ++ drop (i+1) xs
```

### 对角化

```haskell
-- 对角化类型
data Diagonalization v = Diagonalization {
    diagonalMatrix :: Matrix (Dimension v) (Dimension v) (Scalar v),
    eigenvectorMatrix :: Matrix (Dimension v) (Dimension v) (Scalar v),
    inverseEigenvectorMatrix :: Matrix (Dimension v) (Dimension v) (Scalar v)
}

-- 检查是否可对角化
isDiagonalizable :: Matrix n n Double -> Bool
isDiagonalizable matrix = 
    let eigenvalues = matrixEigenvalues matrix
        -- 检查是否有足够的线性无关特征向量
        totalEigenvectors = sum (map (geometricMultiplicity matrix) eigenvalues)
        dimension = matrixDimension matrix
    in totalEigenvectors == dimension

-- 计算对角化
diagonalize :: Matrix n n Double -> Maybe (Diagonalization (Vector n Double))
diagonalize matrix
    | not (isDiagonalizable matrix) = Nothing
    | otherwise = 
        let eigenvalues = matrixEigenvalues matrix
            eigenvectors = concatMap (eigenvectorsForEigenvalue matrix) eigenvalues
            -- 构造特征向量矩阵
            eigenvectorMatrix = Matrix (map unVector eigenvectors)
            -- 构造对角矩阵
            diagonalMatrix = constructDiagonalMatrix eigenvalues
            -- 计算逆矩阵
            inverseMatrix = matrixInverse eigenvectorMatrix
        in Just (Diagonalization diagonalMatrix eigenvectorMatrix inverseMatrix)

-- 构造对角矩阵
constructDiagonalMatrix :: [Double] -> Matrix n n Double
constructDiagonalMatrix eigenvalues = 
    let n = length eigenvalues
        diagonal = [if i == j then eigenvalues !! i else 0 | i <- [0..n-1], j <- [0..n-1]]
    in Matrix (chunksOf n diagonal)

-- 矩阵分块
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)
```

## 重要定理与证明

### 定理1：特征多项式的性质

**定理**：设 $A$ 是 $n \times n$ 矩阵，则：

1. $p_A(\lambda)$ 是 $n$ 次多项式
2. $p_A(\lambda)$ 的首项系数是 $(-1)^n$
3. $p_A(0) = \det(A)$

**证明**：

1. **次数**：$\det(A - \lambda I)$ 是 $n$ 个变量的行列式，每个变量最多出现一次，所以是 $n$ 次多项式
2. **首项系数**：展开 $\det(A - \lambda I)$ 时，包含 $\lambda^n$ 的项来自对角线的乘积 $(-1)^n \lambda^n$
3. **常数项**：$p_A(0) = \det(A - 0 \cdot I) = \det(A)$

### 定理2：几何重数 ≤ 代数重数

**定理**：设 $\lambda$ 是矩阵 $A$ 的特征值，则几何重数 ≤ 代数重数。

**证明**：

1. 设几何重数为 $k$，代数重数为 $m$
2. 存在 $k$ 个线性无关的特征向量 $\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_k$
3. 将其扩展为 $\mathbb{R}^n$ 的基 $\{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_k, \mathbf{w}_{k+1}, \ldots, \mathbf{w}_n\}$
4. 在此基下，$A$ 的矩阵形式为：
   $$\begin{bmatrix}
   \lambda I_k & B \\
   0 & C
   \end{bmatrix}$$
5. 特征多项式为 $p_A(\lambda) = (\lambda - \lambda)^k \det(C - \lambda I_{n-k})$
6. 因此 $\lambda$ 在特征多项式中至少出现 $k$ 次，即 $m \geq k$

### 定理3：对角化条件

**定理**：$n \times n$ 矩阵 $A$ 可对角化当且仅当 $A$ 有 $n$ 个线性无关的特征向量。

**证明**：

- **必要性**：如果 $A$ 可对角化，则存在可逆矩阵 $P$ 使得 $P^{-1}AP = D$，其中 $D$ 是对角矩阵
- 设 $D = \text{diag}(\lambda_1, \lambda_2, \ldots, \lambda_n)$，则 $AP = PD$
- 设 $P = [\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n]$，则 $A\mathbf{v}_i = \lambda_i\mathbf{v}_i$
- 因此 $\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n$ 是 $A$ 的特征向量，且线性无关

- **充分性**：如果 $A$ 有 $n$ 个线性无关的特征向量 $\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n$，对应的特征值为 $\lambda_1, \lambda_2, \ldots, \lambda_n$
- 设 $P = [\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n]$，$D = \text{diag}(\lambda_1, \lambda_2, \ldots, \lambda_n)$
- 则 $AP = PD$，即 $P^{-1}AP = D$，所以 $A$ 可对角化

## 应用示例

### 示例1：2×2矩阵的特征值

```haskell
-- 2×2矩阵特征值计算
example2x2Matrix :: Matrix 2 2 Double
example2x2Matrix = Matrix [[4, -1], [2, 1]]

-- 计算特征值
eigenvalues2x2 :: [Double]
eigenvalues2x2 = matrixEigenvalues example2x2Matrix

-- 计算特征向量
eigenvectors2x2 :: [(Double, [Vector 2 Double])]
eigenvectors2x2 = matrixEigenvectors example2x2Matrix

-- 验证特征值-特征向量对
verifyEigenpairs :: Bool
verifyEigenpairs = 
    all (\(lambda, vectors) -> 
        all (\v -> verifyEigenpair example2x2Matrix lambda v) vectors
    ) eigenvectors2x2
```

### 示例2：对称矩阵的谱分解

```haskell
-- 对称矩阵
symmetricMatrix :: Matrix 3 3 Double
symmetricMatrix = Matrix [
    [2, 1, 0],
    [1, 2, 1],
    [0, 1, 2]
]

-- 谱分解
spectralDecomposition :: Diagonalization (Vector 3 Double)
spectralDecomposition = 
    case diagonalize symmetricMatrix of
        Just decomp -> decomp
        Nothing -> error "Matrix not diagonalizable"

-- 验证谱分解
verifySpectralDecomposition :: Bool
verifySpectralDecomposition = 
    let (Diagonalization d p p_inv) = spectralDecomposition
        reconstructed = matrixMultiply (matrixMultiply p d) p_inv
    in matrixApproximatelyEqual symmetricMatrix reconstructed 1e-10

-- 矩阵近似相等
matrixApproximatelyEqual :: Matrix n n Double -> Matrix n n Double -> Double -> Bool
matrixApproximatelyEqual (Matrix a) (Matrix b) tolerance = 
    all (\(rowA, rowB) -> 
        all (\(x, y) -> abs (x - y) < tolerance) (zip rowA rowB)
    ) (zip a b)
```

### 示例3：马尔可夫链的稳态

```haskell
-- 马尔可夫转移矩阵
markovMatrix :: Matrix 3 3 Double
markovMatrix = Matrix [
    [0.8, 0.2, 0.0],
    [0.1, 0.7, 0.2],
    [0.0, 0.1, 0.9]
]

-- 计算稳态分布
steadyStateDistribution :: Vector 3 Double
steadyStateDistribution = 
    let eigenvalues = matrixEigenvalues markovMatrix
        -- 找到特征值1对应的特征向量
        eigenvector1 = head [vs | (lambda, vs) <- matrixEigenvectors markovMatrix, 
                                 abs (lambda - 1) < 1e-10]
        -- 归一化
        total = sum (map sum (map unVector eigenvector1))
    in Vector (map (/ total) (head (map unVector eigenvector1)))

-- 验证稳态
verifySteadyState :: Bool
verifySteadyState = 
    let steadyState = steadyStateDistribution
        nextState = matrixVectorMultiply markovMatrix steadyState
    in vectorApproximatelyEqual steadyState nextState 1e-10

-- 向量近似相等
vectorApproximatelyEqual :: Vector n Double -> Vector n Double -> Double -> Bool
vectorApproximatelyEqual (Vector a) (Vector b) tolerance = 
    all (\(x, y) -> abs (x - y) < tolerance) (zip a b)
```

## 总结

特征值与特征向量理论为理解线性变换的本质提供了强大的工具：

1. **严格的数学定义**：基于线性变换的不变子空间
2. **完整的Haskell实现**：包含多种特征值计算算法
3. **重要的理论结果**：特征多项式、对角化条件等定理
4. **实际应用示例**：马尔可夫链、谱分解等应用

这个理论框架为后续的谱理论、矩阵分析等高级概念提供了必要的理论基础。

---

**相关文档**：

- [向量空间理论](./01-Vector-Spaces.md)
- [线性变换理论](./02-Linear-Transformations.md)
- [矩阵理论](../05-Matrix-Theory/01-Matrix-Theory.md)
