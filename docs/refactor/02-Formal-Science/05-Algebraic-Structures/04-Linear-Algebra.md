# 线性代数基础 (Linear Algebra Foundation)

## 概述

线性代数是研究向量空间和线性变换的数学分支，在计算机科学、机器学习、图形学等领域有广泛应用。

## 1. 向量空间

### 1.1 向量空间公理

**定义 1.1 (向量空间)**
设 $V$ 是集合，$\mathbb{F}$ 是域，$V$ 上的向量空间由以下公理定义：

**加法公理：**
- 结合律：$(u + v) + w = u + (v + w)$
- 交换律：$u + v = v + u$
- 零元：存在 $0 \in V$ 使得 $v + 0 = v$
- 逆元：对每个 $v \in V$，存在 $-v \in V$ 使得 $v + (-v) = 0$

**标量乘法公理：**
- 分配律：$a(u + v) = au + av$
- 分配律：$(a + b)v = av + bv$
- 结合律：$(ab)v = a(bv)$
- 单位元：$1v = v$

### 1.2 线性无关与基

**定义 1.2 (线性无关)**
向量组 $\{v_1, v_2, \ldots, v_n\}$ 线性无关当且仅当：
$$\sum_{i=1}^n a_i v_i = 0 \Rightarrow a_i = 0 \text{ for all } i$$

**定义 1.3 (基)**
向量空间 $V$ 的基是线性无关的生成集。

**定理 1.1 (基的存在性)**
每个有限维向量空间都有基。

## 2. Haskell实现

### 2.1 向量类型

```haskell
{-# LANGUAGE GADTs, DataKinds, TypeFamilies #-}

-- 向量类型
data Vector :: Nat -> Type -> Type where
  VNil :: Vector Zero a
  VCons :: a -> Vector n a -> Vector (Succ n) a

-- 向量加法
addVector :: Num a => Vector n a -> Vector n a -> Vector n a
addVector VNil VNil = VNil
addVector (VCons x xs) (VCons y ys) = VCons (x + y) (addVector xs ys)

-- 标量乘法
scaleVector :: Num a => a -> Vector n a -> Vector n a
scaleVector _ VNil = VNil
scaleVector c (VCons x xs) = VCons (c * x) (scaleVector c xs)

-- 零向量
zeroVector :: Num a => Vector n a
zeroVector = VNil

-- 向量点积
dotProduct :: Num a => Vector n a -> Vector n a -> a
dotProduct VNil VNil = 0
dotProduct (VCons x xs) (VCons y ys) = x * y + dotProduct xs ys
```

### 2.2 矩阵类型

```haskell
-- 矩阵类型
data Matrix :: Nat -> Nat -> Type -> Type where
  MNil :: Matrix Zero n a
  MCons :: Vector n a -> Matrix m n a -> Matrix (Succ m) n a

-- 矩阵加法
addMatrix :: Num a => Matrix m n a -> Matrix m n a -> Matrix m n a
addMatrix MNil MNil = MNil
addMatrix (MCons row1 mat1) (MCons row2 mat2) = 
  MCons (addVector row1 row2) (addMatrix mat1 mat2)

-- 矩阵标量乘法
scaleMatrix :: Num a => a -> Matrix m n a -> Matrix m n a
scaleMatrix _ MNil = MNil
scaleMatrix c (MCons row mat) = 
  MCons (scaleVector c row) (scaleMatrix c mat)

-- 矩阵乘法
multMatrix :: Num a => Matrix m n a -> Matrix n p a -> Matrix m p a
multMatrix MNil _ = MNil
multMatrix (MCons row mat1) mat2 = 
  MCons (multRowMatrix row mat2) (multMatrix mat1 mat2)

-- 辅助函数：行与矩阵相乘
multRowMatrix :: Num a => Vector n a -> Matrix n p a -> Vector p a
multRowMatrix VNil MNil = VNil
multRowMatrix (VCons x xs) (MCons col mat) = 
  VCons (dotProduct (VCons x xs) col) (multRowMatrix xs mat)
```

## 3. 线性变换

### 3.1 线性变换定义

**定义 3.1 (线性变换)**
函数 $T: V \rightarrow W$ 是线性变换当且仅当：
- $T(u + v) = T(u) + T(v)$
- $T(av) = aT(v)$

**定理 3.1 (线性变换的矩阵表示)**
每个线性变换都可以用矩阵表示。

### 3.2 线性变换实现

```haskell
-- 线性变换类型
type LinearTransform v w = v -> w

-- 线性变换的组合
composeTransform :: LinearTransform v w -> LinearTransform u v -> LinearTransform u w
composeTransform f g = f . g

-- 恒等变换
idTransform :: LinearTransform v v
idTransform = id

-- 零变换
zeroTransform :: (Num a, Num b) => LinearTransform (Vector n a) (Vector m b)
zeroTransform _ = zeroVector

-- 矩阵表示线性变换
matrixTransform :: Num a => Matrix m n a -> LinearTransform (Vector n a) (Vector m a)
matrixTransform mat vec = multMatrix (MCons vec MNil) mat
```

## 4. 特征值与特征向量

### 4.1 特征值定义

**定义 4.1 (特征值与特征向量)**
对于矩阵 $A$，如果存在非零向量 $v$ 和标量 $\lambda$ 使得：
$$Av = \lambda v$$
则称 $\lambda$ 为特征值，$v$ 为对应的特征向量。

### 4.2 特征值计算

```haskell
-- 特征多项式
characteristicPolynomial :: Num a => Matrix n n a -> [a]
characteristicPolynomial mat = 
  let det = determinant mat
      trace = matrixTrace mat
  in [1, -trace, det]  -- 简化版本

-- 矩阵行列式
determinant :: Num a => Matrix n n a -> a
determinant MNil = 1
determinant (MCons row mat) = 
  sum [(-1)^i * (row !! i) * determinant (removeRowCol i mat) | i <- [0..n-1]]

-- 矩阵迹
matrixTrace :: Num a => Matrix n n a -> a
matrixTrace MNil = 0
matrixTrace (MCons row mat) = 
  head (vectorToList row) + matrixTrace mat

-- 辅助函数
vectorToList :: Vector n a -> [a]
vectorToList VNil = []
vectorToList (VCons x xs) = x : vectorToList xs

removeRowCol :: Int -> Matrix (Succ m) (Succ n) a -> Matrix m n a
removeRowCol = undefined  -- 实现省略
```

## 5. 内积空间

### 5.1 内积定义

**定义 5.1 (内积)**
内积是满足以下性质的函数 $\langle \cdot, \cdot \rangle: V \times V \rightarrow \mathbb{F}$：
- 共轭对称性：$\langle u, v \rangle = \overline{\langle v, u \rangle}$
- 线性性：$\langle au + bv, w \rangle = a\langle u, w \rangle + b\langle v, w \rangle$
- 正定性：$\langle v, v \rangle \geq 0$ 且 $\langle v, v \rangle = 0 \Leftrightarrow v = 0$

### 5.2 内积实现

```haskell
-- 内积类型类
class InnerProduct v where
  innerProduct :: v -> v -> Double

-- 向量内积实例
instance InnerProduct (Vector n Double) where
  innerProduct v1 v2 = dotProduct v1 v2

-- 范数
norm :: InnerProduct v => v -> Double
norm v = sqrt (innerProduct v v)

-- 正交性
orthogonal :: InnerProduct v => v -> v -> Bool
orthogonal v1 v2 = abs (innerProduct v1 v2) < 1e-10

-- 单位向量
unitVector :: InnerProduct v => v -> v
unitVector v = scaleVector (1 / norm v) v
```

## 6. 奇异值分解

### 6.1 SVD定义

**定理 6.1 (奇异值分解)**
对于任意矩阵 $A \in \mathbb{R}^{m \times n}$，存在正交矩阵 $U \in \mathbb{R}^{m \times m}$，$V \in \mathbb{R}^{n \times n}$ 和对角矩阵 $\Sigma \in \mathbb{R}^{m \times n}$ 使得：
$$A = U\Sigma V^T$$

### 6.2 SVD实现

```haskell
-- SVD结果类型
data SVD m n a = SVD {
  uMatrix :: Matrix m m a,
  sigmaMatrix :: Matrix m n a,
  vMatrix :: Matrix n n a
}

-- 简化的SVD算法
svd :: (Floating a, Ord a) => Matrix m n a -> SVD m n a
svd mat = 
  let -- 计算 A^T A 的特征值和特征向量
      ata = multMatrix (transpose mat) mat
      eigenvals = eigenvalues ata
      eigenvecs = eigenvectors ata
      
      -- 计算奇异值
      singularVals = map sqrt eigenvals
      
      -- 构造U矩阵
      u = constructU mat eigenvecs singularVals
      
      -- 构造V矩阵
      v = eigenvecs
      
      -- 构造Σ矩阵
      sigma = diagonalMatrix singularVals
  in SVD u sigma v

-- 辅助函数
transpose :: Matrix m n a -> Matrix n m a
transpose = undefined

eigenvalues :: Matrix n n a -> [a]
eigenvalues = undefined

eigenvectors :: Matrix n n a -> Matrix n n a
eigenvectors = undefined

constructU :: Matrix m n a -> Matrix n n a -> [a] -> Matrix m m a
constructU = undefined

diagonalMatrix :: [a] -> Matrix m n a
diagonalMatrix = undefined
```

## 7. 应用示例

### 7.1 主成分分析

```haskell
-- 主成分分析
pca :: Matrix m n Double -> (Matrix m k Double, Matrix k n Double)
pca dataMatrix = 
  let -- 中心化数据
      centered = centerMatrix dataMatrix
      
      -- 计算协方差矩阵
      covMatrix = multMatrix (transpose centered) centered
      
      -- SVD分解
      SVD u sigma v = svd centered
      
      -- 选择前k个主成分
      k = 2  -- 简化示例
      uReduced = takeColumns k u
      vReduced = takeRows k v
  in (uReduced, vReduced)

-- 辅助函数
centerMatrix :: Matrix m n Double -> Matrix m n Double
centerMatrix = undefined

takeColumns :: Int -> Matrix m n a -> Matrix m k a
takeColumns = undefined

takeRows :: Int -> Matrix m n a -> Matrix k n a
takeRows = undefined
```

### 7.2 线性回归

```haskell
-- 线性回归
linearRegression :: Matrix m n Double -> Vector m Double -> Vector n Double
linearRegression x y = 
  let -- 计算 (X^T X)^(-1) X^T y
      xtx = multMatrix (transpose x) x
      xty = multMatrix (transpose x) (MCons y MNil)
      
      -- 求解线性方程组
      coefficients = solveLinearSystem xtx xty
  in head (matrixToList coefficients)

-- 求解线性方程组
solveLinearSystem :: Matrix n n Double -> Matrix n 1 Double -> Matrix n 1 Double
solveLinearSystem = undefined

matrixToList :: Matrix m n a -> [[a]]
matrixToList = undefined
```

## 8. 结论

线性代数为计算机科学提供了重要的数学工具：

1. **向量运算**：高效的向量和矩阵运算
2. **线性变换**：描述空间变换和映射
3. **特征分析**：理解矩阵的本质性质
4. **降维技术**：主成分分析、奇异值分解
5. **机器学习**：线性回归、支持向量机等算法

线性代数的发展推动了机器学习、计算机图形学、信号处理等领域的进步，为现代计算机科学提供了坚实的数学基础。

## 参考文献

1. Strang, G. (2006). Linear algebra and its applications. Cengage Learning.
2. Axler, S. (2015). Linear algebra done right. Springer.
3. Golub, G. H., & Van Loan, C. F. (2013). Matrix computations. JHU press.
4. Trefethen, L. N., & Bau, D. (1997). Numerical linear algebra. SIAM. 