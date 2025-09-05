# 矩阵基础理论

## 概述

矩阵是线性代数中的基本工具，用于表示线性变换、求解线性方程组、进行数据分析等。本文档提供矩阵的严格数学定义、基本运算、性质证明和Haskell实现。

## 数学定义

### 矩阵

设 $\mathbb{F}$ 是一个域，$m, n$ 是正整数。$m \times n$ 矩阵是 $\mathbb{F}$ 中元素的矩形数组：

$$A = \begin{bmatrix}
a_{11} & a_{12} & \cdots & a_{1n} \\
a_{21} & a_{22} & \cdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{m1} & a_{m2} & \cdots & a_{mn}
\end{bmatrix}$$

其中 $a_{ij} \in \mathbb{F}$ 是矩阵 $A$ 的第 $i$ 行第 $j$ 列元素。

### 矩阵运算

#### 矩阵加法

设 $A = [a_{ij}]$ 和 $B = [b_{ij}]$ 都是 $m \times n$ 矩阵，则：
$$A + B = [a_{ij} + b_{ij}]$$

#### 标量乘法

设 $A = [a_{ij}]$ 是 $m \times n$ 矩阵，$c \in \mathbb{F}$ 是标量，则：
$$cA = [ca_{ij}]$$

#### 矩阵乘法

设 $A = [a_{ik}]$ 是 $m \times p$ 矩阵，$B = [b_{kj}]$ 是 $p \times n$ 矩阵，则：
$$AB = [c_{ij}]$$
其中 $c_{ij} = \sum_{k=1}^{p} a_{ik}b_{kj}$

### 特殊矩阵

#### 零矩阵

所有元素都为 $0$ 的矩阵，记作 $O$ 或 $0$。

#### 单位矩阵

$n \times n$ 单位矩阵 $I_n$ 定义为：
$$I_n = \begin{bmatrix}
1 & 0 & \cdots & 0 \\
0 & 1 & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & 1
\end{bmatrix}$$

#### 对角矩阵

$n \times n$ 对角矩阵 $D = \text{diag}(d_1, d_2, \ldots, d_n)$ 定义为：
$$D = \begin{bmatrix}
d_1 & 0 & \cdots & 0 \\
0 & d_2 & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & d_n
\end{bmatrix}$$

#### 转置矩阵

设 $A = [a_{ij}]$ 是 $m \times n$ 矩阵，则 $A$ 的转置 $A^T$ 是 $n \times m$ 矩阵：
$$A^T = [a_{ji}]$$

### 矩阵的秩

矩阵 $A$ 的秩定义为 $A$ 的行向量组的最大线性无关向量个数，记作 $\text{rank}(A)$。

等价地，$\text{rank}(A)$ 是 $A$ 的列向量组的最大线性无关向量个数。

## Haskell实现

### 矩阵数据类型

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- 矩阵数据类型
data Matrix (m :: Nat) (n :: Nat) a = Matrix {
    unMatrix :: [[a]]
} deriving (Eq, Show)

-- 矩阵维度
matrixRows :: Matrix m n a -> Int
matrixRows (Matrix rows) = length rows

matrixCols :: Matrix m n a -> Int
matrixCols (Matrix rows) = length (head rows)

-- 矩阵元素访问
matrixElement :: Matrix m n a -> Int -> Int -> a
matrixElement (Matrix rows) i j = (rows !! i) !! j

-- 矩阵更新
updateMatrix :: Matrix m n a -> Int -> Int -> a -> Matrix m n a
updateMatrix (Matrix rows) i j value =
    Matrix (updateAt i (updateAt j value) (rows !! i)) rows)
  where
    updateAt :: Int -> a -> [a] -> [a]
    updateAt k x xs = take k xs ++ [x] ++ drop (k+1) xs
```

### 矩阵运算

```haskell
-- 矩阵加法
instance (Num a) => Num (Matrix m n a) where
    (+) (Matrix a) (Matrix b) =
        Matrix (zipWith (zipWith (+)) a b)

    (-) (Matrix a) (Matrix b) =
        Matrix (zipWith (zipWith (-)) a b)

    (*) = matrixMultiply

    abs = fmap abs
    signum = fmap signum
    fromInteger = error "fromInteger not implemented for Matrix"

-- 标量乘法
instance (Num a) => Num (Matrix m n a) where
    (*) scalar (Matrix rows) =
        Matrix (map (map (* scalar)) rows)

-- 矩阵乘法
matrixMultiply :: (Num a) => Matrix m k a -> Matrix k n a -> Matrix m n a
matrixMultiply (Matrix a) (Matrix b) =
    Matrix [[sum [a !! i !! k * b !! k !! j | k <- [0..length (head a)-1]]
             | j <- [0..length (head b)-1]]
            | i <- [0..length a-1]]

-- 矩阵转置
transpose :: Matrix m n a -> Matrix n m a
transpose (Matrix rows) =
    Matrix (transposeList rows)
  where
    transposeList :: [[a]] -> [[a]]
    transposeList [] = []
    transposeList ([]:_) = []
    transposeList rows =
        (map head rows) : transposeList (map tail rows)

-- 矩阵幂
matrixPower :: (Num a) => Matrix n n a -> Int -> Matrix n n a
matrixPower matrix 0 = identityMatrix (matrixRows matrix)
matrixPower matrix 1 = matrix
matrixPower matrix n
    | even n = let half = matrixPower matrix (n `div` 2)
               in half `matrixMultiply` half
    | odd n = matrix `matrixMultiply` matrixPower matrix (n-1)
```

### 特殊矩阵构造

```haskell
-- 零矩阵
zeroMatrix :: (Num a) => Int -> Int -> Matrix m n a
zeroMatrix m n = Matrix (replicate m (replicate n 0))

-- 单位矩阵
identityMatrix :: (Num a) => Int -> Matrix n n a
identityMatrix n = Matrix [[if i == j then 1 else 0 | j <- [0..n-1]] | i <- [0..n-1]]

-- 对角矩阵
diagonalMatrix :: (Num a) => [a] -> Matrix n n a
diagonalMatrix diag =
    let n = length diag
    in Matrix [[if i == j then diag !! i else 0 | j <- [0..n-1]] | i <- [0..n-1]]

-- 上三角矩阵
upperTriangular :: (Num a) => [[a]] -> Matrix n n a
upperTriangular elements =
    Matrix [[if i <= j then elements !! i !! j else 0 | j <- [0..n-1]] | i <- [0..n-1]]
  where
    n = length elements

-- 下三角矩阵
lowerTriangular :: (Num a) => [[a]] -> Matrix n n a
lowerTriangular elements =
    Matrix [[if i >= j then elements !! i !! j else 0 | j <- [0..n-1]] | i <- [0..n-1]]
  where
    n = length elements
```

### 矩阵分解

```haskell
-- LU分解
data LUDecomposition a = LU {
    lMatrix :: Matrix n n a,  -- 下三角矩阵
    uMatrix :: Matrix n n a   -- 上三角矩阵
}

-- LU分解算法
luDecomposition :: (Fractional a) => Matrix n n a -> LUDecomposition a
luDecomposition matrix =
    let n = matrixRows matrix
        (l, u) = luDecompose matrix n
    in LU l u
  where
    luDecompose :: (Fractional a) => Matrix n n a -> Int -> (Matrix n n a, Matrix n n a)
    luDecompose mat n =
        let l = identityMatrix n
            u = mat
            (finalL, finalU) = iterateLU l u n
        in (finalL, finalU)

    iterateLU :: (Fractional a) => Matrix n n a -> Matrix n n a -> Int -> (Matrix n n a, Matrix n n a)
    iterateLU l u k
        | k >= n = (l, u)
        | otherwise =
            let newL = updateL l u k
                newU = updateU l u k
            in iterateLU newL newU (k+1)

    updateL :: (Fractional a) => Matrix n n a -> Matrix n n a -> Int -> Matrix n n a
    updateL l u k =
        -- 更新L矩阵的第k列
        let lValues = [u `matrixElement` i k / u `matrixElement` k k | i <- [k+1..n-1]]
        in foldl (\l' (i, val) -> updateMatrix l' i k val) l (zip [k+1..n-1] lValues)

    updateU :: (Fractional a) => Matrix n n a -> Matrix n n a -> Int -> Matrix n n a
    updateU l u k =
        -- 更新U矩阵
        let uValues = [(i, j, u `matrixElement` i j - l `matrixElement` i k * u `matrixElement` k j)
                      | i <- [k+1..n-1], j <- [k+1..n-1]]
        in foldl (\u' (i, j, val) -> updateMatrix u' i j val) u uValues

-- QR分解
data QRDecomposition a = QR {
    qMatrix :: Matrix m n a,  -- 正交矩阵
    rMatrix :: Matrix n n a   -- 上三角矩阵
}

-- QR分解算法
qrDecomposition :: (Floating a) => Matrix m n a -> QRDecomposition a
qrDecomposition matrix =
    let columns = transpose (unMatrix matrix)
        (qColumns, rMatrix) = gramSchmidt columns
        qMatrix = Matrix (transpose qColumns)
    in QR qMatrix rMatrix

-- 格拉姆-施密特正交化
gramSchmidt :: (Floating a) => [[a]] -> ([[a]], [[a]])
gramSchmidt columns =
    let orthogonalized = foldl orthogonalize [] columns
        normalized = map normalizeVector orthogonalized
        rMatrix = computeRMatrix columns normalized
    in (normalized, rMatrix)

-- 向量正交化
orthogonalize :: (Floating a) => [[a]] -> [a] -> [a]
orthogonalize [] column = column
orthogonalize (q:qs) column =
    let projection = projectOnto column q
        orthogonal = subtractVectors column projection
    in orthogonalize qs orthogonal

-- 向量投影
projectOnto :: (Floating a) => [a] -> [a] -> [a]
projectOnto u v =
    let dot = sum (zipWith (*) u v)
        normSq = sum (map (^2) v)
        scalar = dot / normSq
    in map (* scalar) v

-- 向量归一化
normalizeVector :: (Floating a) => [a] -> [a]
normalizeVector v =
    let norm = sqrt (sum (map (^2) v))
    in map (/ norm) v

-- 计算R矩阵
computeRMatrix :: (Floating a) => [[a]] -> [[a]] -> [[a]]
computeRMatrix originalColumns qColumns =
    let n = length originalColumns
    in [[sum (zipWith (*) (originalColumns !! j) (qColumns !! i)) | j <- [0..n-1]] | i <- [0..n-1]]
```

### 矩阵性质

```haskell
-- 矩阵秩
matrixRank :: (Fractional a) => Matrix m n a -> Int
matrixRank matrix =
    let rref = reducedRowEchelonForm matrix
        pivotCount = countPivots rref
    in pivotCount

-- 行阶梯形
reducedRowEchelonForm :: (Fractional a) => Matrix m n a -> Matrix m n a
reducedRowEchelonForm matrix =
    let rows = unMatrix matrix
        (rref, _) = gaussianElimination rows
    in Matrix rref

-- 高斯消元
gaussianElimination :: (Fractional a) => [[a]] -> ([[a]], [Int])
gaussianElimination rows =
    let n = length rows
        m = length (head rows)
        (result, pivots) = eliminate rows 0 []
    in (result, pivots)
  where
    eliminate :: (Fractional a) => [[a]] -> Int -> [Int] -> ([[a]], [Int])
    eliminate currentRows row pivots
        | row >= n || row >= m = (currentRows, pivots)
        | otherwise =
            let (newRows, newPivots) = findPivot currentRows row pivots
                (eliminatedRows, newPivots') = eliminateColumn newRows row newPivots
            in eliminate eliminatedRows (row + 1) newPivots'

    findPivot :: (Fractional a) => [[a]] -> Int -> [Int] -> ([[a]], [Int])
    findPivot rows row pivots =
        let column = [rows !! i !! row | i <- [row..length rows-1]]
            maxIndex = row + maximumIndex (map abs column)
        in if abs (rows !! maxIndex !! row) > 1e-10
           then (swapRows rows row maxIndex, row:pivots)
           else (rows, pivots)

    eliminateColumn :: (Fractional a) => [[a]] -> Int -> [Int] -> ([[a]], [Int])
    eliminateColumn rows row pivots =
        let pivot = rows !! row !! row
            newRows = map (\i ->
                if i == row
                then rows !! i
                else let factor = -(rows !! i !! row) / pivot
                     in zipWith (\a b -> a + factor * b) (rows !! i) (rows !! row)
            ) [0..length rows-1]
        in (newRows, pivots)

-- 计算主元个数
countPivots :: Matrix m n a -> Int
countPivots (Matrix rows) =
    length [i | i <- [0..length rows-1],
                any (\j -> abs (rows !! i !! j) > 1e-10) [0..length (head rows)-1]]

-- 交换矩阵行
swapRows :: [[a]] -> Int -> Int -> [[a]]
swapRows rows i j =
    take i rows ++ [rows !! j] ++ drop (i+1) (take j rows) ++ [rows !! i] ++ drop (j+1) rows

-- 最大元素索引
maximumIndex :: (Ord a) => [a] -> Int
maximumIndex xs =
    let indexed = zip xs [0..]
        (_, maxIndex) = maximum indexed
    in maxIndex
```

## 重要定理与证明

### 定理1：矩阵乘法的结合律

**定理**：设 $A$ 是 $m \times p$ 矩阵，$B$ 是 $p \times q$ 矩阵，$C$ 是 $q \times n$ 矩阵，则：
$$(AB)C = A(BC)$$

**证明**：
1. 设 $(AB)C = D = [d_{ij}]$，$A(BC) = E = [e_{ij}]$
2. 计算 $d_{ij}$：
   $$d_{ij} = \sum_{k=1}^{q} (AB)_{ik} \cdot c_{kj} = \sum_{k=1}^{q} \left(\sum_{l=1}^{p} a_{il}b_{lk}\right) c_{kj} = \sum_{k=1}^{q} \sum_{l=1}^{p} a_{il}b_{lk}c_{kj}$$
3. 计算 $e_{ij}$：
   $$e_{ij} = \sum_{l=1}^{p} a_{il} \cdot (BC)_{lj} = \sum_{l=1}^{p} a_{il} \left(\sum_{k=1}^{q} b_{lk}c_{kj}\right) = \sum_{l=1}^{p} \sum_{k=1}^{q} a_{il}b_{lk}c_{kj}$$
4. 因此 $d_{ij} = e_{ij}$，所以 $(AB)C = A(BC)$

### 定理2：矩阵转置的性质

**定理**：设 $A$ 和 $B$ 是矩阵，$c$ 是标量，则：
1. $(A^T)^T = A$
2. $(A + B)^T = A^T + B^T$
3. $(cA)^T = cA^T$
4. $(AB)^T = B^T A^T$

**证明**：
1. **$(A^T)^T = A$**：直接由转置定义可得
2. **$(A + B)^T = A^T + B^T$**：
   $$(A + B)^T_{ij} = (A + B)_{ji} = A_{ji} + B_{ji} = A^T_{ij} + B^T_{ij} = (A^T + B^T)_{ij}$$
3. **$(cA)^T = cA^T$**：
   $$(cA)^T_{ij} = (cA)_{ji} = cA_{ji} = cA^T_{ij} = (cA^T)_{ij}$$
4. **$(AB)^T = B^T A^T$**：
   $$(AB)^T_{ij} = (AB)_{ji} = \sum_{k} A_{jk} B_{ki} = \sum_{k} B^T_{ik} A^T_{kj} = (B^T A^T)_{ij}$$

### 定理3：矩阵秩的性质

**定理**：设 $A$ 是 $m \times n$ 矩阵，$B$ 是 $n \times p$ 矩阵，则：
$$\text{rank}(AB) \leq \min\{\text{rank}(A), \text{rank}(B)\}$$

**证明**：
1. 设 $\text{rank}(A) = r$，$\text{rank}(B) = s$
2. $A$ 的列空间维数为 $r$，$B$ 的列空间维数为 $s$
3. $AB$ 的列是 $A$ 的列的线性组合，因此 $AB$ 的列空间是 $A$ 的列空间的子空间
4. 因此 $\text{rank}(AB) \leq \text{rank}(A)$
5. 类似地，$AB$ 的行是 $B$ 的行的线性组合，因此 $\text{rank}(AB) \leq \text{rank}(B)$
6. 所以 $\text{rank}(AB) \leq \min\{\text{rank}(A), \text{rank}(B)\}$

## 应用示例

### 示例1：线性方程组求解

```haskell
-- 线性方程组求解
solveLinearSystem :: (Fractional a) => Matrix m n a -> [a] -> Maybe [a]
solveLinearSystem coefficientMatrix constants =
    let augmentedMatrix = augmentMatrix coefficientMatrix constants
        rref = reducedRowEchelonForm augmentedMatrix
        (solution, isConsistent) = backSubstitution rref
    in if isConsistent then Just solution else Nothing

-- 增广矩阵
augmentMatrix :: Matrix m n a -> [a] -> Matrix m (n+1) a
augmentMatrix (Matrix rows) constants =
    Matrix (zipWith (\row const -> row ++ [const]) rows constants)

-- 回代求解
backSubstitution :: (Fractional a) => Matrix m n a -> ([a], Bool)
backSubstitution rref =
    let rows = unMatrix rref
        n = length (head rows) - 1  -- 减去常数列
        solution = replicate n 0
        (finalSolution, consistent) = backSubstitute rows solution n
    in (finalSolution, consistent)
  where
    backSubstitute :: (Fractional a) => [[a]] -> [a] -> Int -> ([a], Bool)
    backSubstitute rows solution row
        | row < 0 = (solution, True)
        | otherwise =
            let pivot = rows !! row !! row
                constant = rows !! row !! n
                if abs pivot < 1e-10
                then if abs constant < 1e-10
                     then backSubstitute rows solution (row-1)  -- 自由变量
                     else (solution, False)  -- 无解
                else let newSolution = updateSolution solution row rows constant pivot
                     in backSubstitute rows newSolution (row-1)

    updateSolution :: (Fractional a) => [a] -> Int -> [[a]] -> a -> a -> [a]
    updateSolution solution row rows constant pivot =
        let value = (constant - sum [rows !! row !! j * solution !! j | j <- [row+1..n-1]]) / pivot
        in take row solution ++ [value] ++ drop (row+1) solution
```

### 示例2：矩阵求逆

```haskell
-- 矩阵求逆
matrixInverse :: (Fractional a) => Matrix n n a -> Maybe (Matrix n n a)
matrixInverse matrix =
    let n = matrixRows matrix
        identity = identityMatrix n
        augmented = augmentMatrix matrix (concat (unMatrix identity))
        rref = reducedRowEchelonForm augmented
        inverse = extractInverse rref n
    in if isInvertible rref n then Just inverse else Nothing

-- 提取逆矩阵
extractInverse :: Matrix n n a -> Int -> Matrix n n a
extractInverse rref n =
    let rows = unMatrix rref
        inverseRows = [drop n row | row <- rows]
    in Matrix inverseRows

-- 检查是否可逆
isInvertible :: Matrix n n a -> Int -> Bool
isInvertible rref n =
    let rows = unMatrix rref
        diagonal = [rows !! i !! i | i <- [0..n-1]]
    in all (\x -> abs x > 1e-10) diagonal
```

### 示例3：特征值计算

```haskell
-- 特征值计算（幂迭代法）
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

-- 矩阵向量乘法
matrixVectorMultiply :: Matrix m n Double -> Vector n Double -> Vector m Double
matrixVectorMultiply (Matrix rows) (Vector xs) =
    Vector [sum (zipWith (*) row xs) | row <- rows]

-- 向量内积
innerProduct :: Vector n Double -> Vector n Double -> Double
innerProduct (Vector xs) (Vector ys) = sum (zipWith (*) xs ys)
```

## 总结

矩阵基础理论为线性代数提供了强大的计算工具：

1. **严格的数学定义**：基于域上元素的矩形数组
2. **完整的Haskell实现**：包含基本运算、分解算法等
3. **重要的理论结果**：结合律、转置性质、秩的性质等
4. **实际应用示例**：线性方程组求解、矩阵求逆、特征值计算

这个理论框架为后续的高级矩阵理论、数值分析等提供了必要的基础。

---

**相关文档**：
- [向量空间理论](../03-Linear-Algebra/01-Vector-Spaces.md)
- [线性变换理论](../03-Linear-Algebra/02-Linear-Transformations.md)
- [特征值与特征向量](../03-Linear-Algebra/03-Eigenvalues-Eigenvectors.md)
