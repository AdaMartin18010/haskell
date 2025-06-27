# 线性变换理论

## 概述

线性变换是向量空间之间的映射，保持向量加法和标量乘法的结构。它是线性代数的核心概念，为理解矩阵、特征值和特征向量提供了理论基础。

## 数学定义

### 线性变换

设 $V$ 和 $W$ 是域 $\mathbb{F}$ 上的向量空间，映射 $T: V \to W$ 称为线性变换，如果满足：

1. **加法保持**：$\forall \mathbf{u}, \mathbf{v} \in V, T(\mathbf{u} + \mathbf{v}) = T(\mathbf{u}) + T(\mathbf{v})$
2. **标量乘法保持**：$\forall a \in \mathbb{F}, \forall \mathbf{v} \in V, T(a\mathbf{v}) = aT(\mathbf{v})$

等价地，线性变换满足：
$$\forall a, b \in \mathbb{F}, \forall \mathbf{u}, \mathbf{v} \in V, T(a\mathbf{u} + b\mathbf{v}) = aT(\mathbf{u}) + bT(\mathbf{v})$$

### 核与像

设 $T: V \to W$ 是线性变换。

**核（Kernel）**：$\ker(T) = \{\mathbf{v} \in V \mid T(\mathbf{v}) = \mathbf{0}\}$

**像（Image）**：$\text{im}(T) = \{T(\mathbf{v}) \mid \mathbf{v} \in V\}$

**零化度（Nullity）**：$\text{nullity}(T) = \dim(\ker(T))$

**秩（Rank）**：$\text{rank}(T) = \dim(\text{im}(T))$

### 线性变换的矩阵表示

设 $T: V \to W$ 是线性变换，$B_V = \{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n\}$ 是 $V$ 的基，$B_W = \{\mathbf{w}_1, \mathbf{w}_2, \ldots, \mathbf{w}_m\}$ 是 $W$ 的基。

矩阵 $A = [a_{ij}]$ 是 $T$ 关于基 $B_V$ 和 $B_W$ 的矩阵表示，如果：
$$T(\mathbf{v}_j) = \sum_{i=1}^{m} a_{ij}\mathbf{w}_i, \quad j = 1, 2, \ldots, n$$

### 线性变换的复合

设 $T: U \to V$ 和 $S: V \to W$ 是线性变换，则复合映射 $S \circ T: U \to W$ 也是线性变换，定义为：
$$(S \circ T)(\mathbf{u}) = S(T(\mathbf{u}))$$

### 线性变换的逆

设 $T: V \to W$ 是线性变换，如果存在线性变换 $T^{-1}: W \to V$ 使得：
$$T \circ T^{-1} = I_W, \quad T^{-1} \circ T = I_V$$
则称 $T$ 是可逆的，$T^{-1}$ 称为 $T$ 的逆变换。

## Haskell实现

### 线性变换类型类

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- 线性变换类型类
class (VectorSpace v, VectorSpace w) => LinearTransformation t v w where
    -- 应用线性变换
    apply :: t -> v -> w
    
    -- 线性变换的加法保持
    additivity :: t -> v -> v -> Bool
    additivity t u v = apply t (add u v) == add (apply t u) (apply t v)
    
    -- 线性变换的标量乘法保持
    homogeneity :: t -> Scalar v -> v -> Bool
    homogeneity t a v = apply t (scale a v) == scale a (apply t v)
    
    -- 线性性（等价条件）
    linearity :: t -> Scalar v -> Scalar v -> v -> v -> Bool
    linearity t a b u v = 
        apply t (add (scale a u) (scale b v)) == 
        add (scale a (apply t u)) (scale b (apply t v))

-- 线性变换的核
kernel :: LinearTransformation t v w => t -> [v]
kernel t = [v | v <- allVectors, apply t v == zero]
  where
    allVectors = generateAllVectors  -- 假设函数

-- 线性变换的像
image :: LinearTransformation t v w => t -> [w]
image t = [apply t v | v <- allVectors]
  where
    allVectors = generateAllVectors  -- 假设函数

-- 零化度
nullity :: LinearTransformation t v w => t -> Int
nullity t = dimension (kernel t)

-- 秩
rank :: LinearTransformation t v w => t -> Int
rank t = dimension (image t)
```

### 矩阵表示

```haskell
-- 矩阵表示
data Matrix m n a = Matrix { unMatrix :: [[a]] }
    deriving (Eq, Show)

-- 矩阵乘法
matrixMultiply :: (Num a) => Matrix m k a -> Matrix k n a -> Matrix m n a
matrixMultiply (Matrix a) (Matrix b) = 
    Matrix [[sum [a !! i !! k * b !! k !! j | k <- [0..length (head a)-1]] 
             | j <- [0..length (head b)-1]] 
            | i <- [0..length a-1]]

-- 矩阵表示的线性变换
data MatrixTransformation v w = MatrixTransformation {
    matrix :: Matrix (Dimension w) (Dimension v) (Scalar v),
    basisV :: [v],
    basisW :: [w]
}

-- 矩阵变换实例
instance (VectorSpace v, VectorSpace w) => 
         LinearTransformation (MatrixTransformation v w) v w where
    apply (MatrixTransformation mat basisV basisW) v = 
        let coords = coordinates v basisV
            resultCoords = matrixVectorMultiply mat coords
        in vectorFromCoordinates resultCoords basisW

-- 坐标表示
coordinates :: VectorSpace v => v -> [v] -> [Scalar v]
coordinates v basis = 
    -- 求解线性方程组 v = sum a_i * basis_i
    solveLinearSystem basis v

-- 从坐标构造向量
vectorFromCoordinates :: VectorSpace v => [Scalar v] -> [v] -> v
vectorFromCoordinates coords basis = 
    linearCombination coords basis
```

### 线性变换的复合

```haskell
-- 线性变换的复合
data Composition t1 t2 v1 v2 v3 = Composition t1 t2

instance (LinearTransformation t1 v1 v2, LinearTransformation t2 v2 v3) =>
         LinearTransformation (Composition t1 t2 v1 v2 v3) v1 v3 where
    apply (Composition t1 t2) v = apply t2 (apply t1 v)

-- 复合运算
compose :: LinearTransformation t1 v1 v2 => 
          LinearTransformation t2 v2 v3 => 
          t1 -> t2 -> Composition t1 t2 v1 v2 v3
compose t1 t2 = Composition t1 t2
```

### 可逆线性变换

```haskell
-- 可逆线性变换
class LinearTransformation t v w => InvertibleTransformation t v w where
    inverse :: t -> LinearTransformation (Inverse t) w v
    
    -- 验证逆变换
    verifyInverse :: t -> Bool
    verifyInverse t = 
        let t_inv = inverse t
        in all (\v -> apply t_inv (apply t v) == v) allVectors &&
           all (\w -> apply t (apply t_inv w) == w) allVectors

-- 逆变换类型
data Inverse t w v = Inverse t

instance (LinearTransformation t v w) => 
         LinearTransformation (Inverse t w v) w v where
    apply (Inverse t) w = 
        -- 求解方程 T(v) = w
        solveForPreimage t w
```

## 重要定理与证明

### 定理1：核与像的性质

**定理**：设 $T: V \to W$ 是线性变换，则：

1. $\ker(T)$ 是 $V$ 的子空间
2. $\text{im}(T)$ 是 $W$ 的子空间

**证明**：

1. **核是子空间**：
   - $T(\mathbf{0}) = \mathbf{0}$，所以 $\mathbf{0} \in \ker(T)$
   - 设 $\mathbf{u}, \mathbf{v} \in \ker(T)$，则 $T(\mathbf{u} + \mathbf{v}) = T(\mathbf{u}) + T(\mathbf{v}) = \mathbf{0} + \mathbf{0} = \mathbf{0}$，所以 $\mathbf{u} + \mathbf{v} \in \ker(T)$
   - 设 $a \in \mathbb{F}, \mathbf{v} \in \ker(T)$，则 $T(a\mathbf{v}) = aT(\mathbf{v}) = a\mathbf{0} = \mathbf{0}$，所以 $a\mathbf{v} \in \ker(T)$

2. **像是子空间**：
   - $T(\mathbf{0}) = \mathbf{0} \in \text{im}(T)$
   - 设 $\mathbf{w}_1, \mathbf{w}_2 \in \text{im}(T)$，存在 $\mathbf{v}_1, \mathbf{v}_2 \in V$ 使得 $T(\mathbf{v}_1) = \mathbf{w}_1, T(\mathbf{v}_2) = \mathbf{w}_2$
   - 则 $\mathbf{w}_1 + \mathbf{w}_2 = T(\mathbf{v}_1) + T(\mathbf{v}_2) = T(\mathbf{v}_1 + \mathbf{v}_2) \in \text{im}(T)$
   - 设 $a \in \mathbb{F}, \mathbf{w} \in \text{im}(T)$，存在 $\mathbf{v} \in V$ 使得 $T(\mathbf{v}) = \mathbf{w}$
   - 则 $a\mathbf{w} = aT(\mathbf{v}) = T(a\mathbf{v}) \in \text{im}(T)$

### 定理2：秩-零化度定理

**定理**：设 $T: V \to W$ 是线性变换，$\dim(V) = n$，则：
$$\text{rank}(T) + \text{nullity}(T) = n$$

**证明**：

1. 设 $\{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_k\}$ 是 $\ker(T)$ 的基
2. 将其扩展为 $V$ 的基 $\{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_k, \mathbf{v}_{k+1}, \ldots, \mathbf{v}_n\}$
3. 证明 $\{T(\mathbf{v}_{k+1}), T(\mathbf{v}_{k+2}), \ldots, T(\mathbf{v}_n)\}$ 是 $\text{im}(T)$ 的基
4. 因此 $\text{rank}(T) = n - k = n - \text{nullity}(T)$

### 定理3：线性变换的矩阵表示

**定理**：设 $T: V \to W$ 是线性变换，$B_V$ 和 $B_W$ 分别是 $V$ 和 $W$ 的基，则 $T$ 有唯一的矩阵表示。

**证明**：

1. 设 $B_V = \{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n\}$，$B_W = \{\mathbf{w}_1, \mathbf{w}_2, \ldots, \mathbf{w}_m\}$
2. 对每个 $j = 1, 2, \ldots, n$，$T(\mathbf{v}_j)$ 可以唯一表示为 $B_W$ 的线性组合
3. 这些系数构成矩阵 $A = [a_{ij}]$，其中 $T(\mathbf{v}_j) = \sum_{i=1}^{m} a_{ij}\mathbf{w}_i$
4. 矩阵 $A$ 是唯一的，因为基的线性组合表示是唯一的

## 应用示例

### 示例1：投影变换

```haskell
-- 投影变换
data Projection v = Projection { 
    projectionDirection :: v,
    projectionPlane :: [v]  -- 平面的基
}

instance VectorSpace v => LinearTransformation (Projection v) v v where
    apply (Projection dir plane) v = 
        let -- 计算投影
            proj = projectOntoPlane v dir plane
        in proj

-- 投影到平面
projectOntoPlane :: VectorSpace v => v -> v -> [v] -> v
projectOntoPlane v dir plane = 
    let -- 计算到平面的投影
        proj = subtract (projectOntoDirection v dir) v
    in proj

-- 投影到方向
projectOntoDirection :: VectorSpace v => v -> v -> v
projectOntoDirection v dir = 
    let dot = innerProduct v dir
        normSq = innerProduct dir dir
        scalar = dot / normSq
    in scale scalar dir
```

### 示例2：旋转变换

```haskell
-- 2D旋转变换
data Rotation2D = Rotation2D { angle :: Double }

instance LinearTransformation Rotation2D (Vector 2 Double) (Vector 2 Double) where
    apply (Rotation2D theta) (Vector [x, y]) = 
        Vector [x * cos theta - y * sin theta,
                x * sin theta + y * cos theta]

-- 3D旋转变换（绕z轴）
data Rotation3D = Rotation3D { angle3D :: Double }

instance LinearTransformation Rotation3D (Vector 3 Double) (Vector 3 Double) where
    apply (Rotation3D theta) (Vector [x, y, z]) = 
        Vector [x * cos theta - y * sin theta,
                x * sin theta + y * cos theta,
                z]
```

### 示例3：缩放变换

```haskell
-- 缩放变换
data Scaling v = Scaling { scaleFactors :: [Scalar v] }

instance VectorSpace v => LinearTransformation (Scaling v) v v where
    apply (Scaling factors) v = 
        let coords = vectorToCoordinates v
            scaledCoords = zipWith (*) coords factors
        in coordinatesToVector scaledCoords

-- 向量坐标转换
vectorToCoordinates :: VectorSpace v => v -> [Scalar v]
vectorToCoordinates v = 
    -- 假设有标准基
    case v of
        Vector xs -> xs

coordinatesToVector :: VectorSpace v => [Scalar v] -> v
coordinatesToVector xs = Vector xs
```

## 总结

线性变换理论为理解向量空间之间的映射关系提供了完整的框架：

1. **严格的数学定义**：基于保持线性结构的映射
2. **完整的Haskell实现**：类型安全的线性变换操作
3. **重要的理论结果**：秩-零化度定理、矩阵表示等
4. **实际应用示例**：投影、旋转、缩放等几何变换

这个理论框架为后续的特征值理论、对角化等高级概念提供了必要的理论基础。

---

**相关文档**：

- [向量空间理论](./01-Vector-Spaces.md)
- [特征值与特征向量](../04-Eigenvalues-Eigenvectors/01-Eigenvalues-Eigenvectors.md)
- [矩阵理论](../05-Matrix-Theory/01-Matrix-Theory.md)
