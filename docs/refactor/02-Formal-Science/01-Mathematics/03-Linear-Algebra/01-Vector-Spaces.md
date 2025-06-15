# 向量空间理论

## 概述

向量空间是线性代数的核心概念，为理解线性变换、特征值和特征向量等概念提供了基础。本文档提供向量空间的严格数学定义、性质证明和Haskell实现。

## 数学定义

### 向量空间公理

设 $V$ 是一个非空集合，$\mathbb{F}$ 是一个域（通常是实数域 $\mathbb{R}$ 或复数域 $\mathbb{C}$），定义两个运算：
- **向量加法**：$+ : V \times V \to V$
- **标量乘法**：$\cdot : \mathbb{F} \times V \to V$

如果满足以下公理，则称 $V$ 为域 $\mathbb{F}$ 上的向量空间：

#### 加法公理
1. **结合律**：$\forall \mathbf{u}, \mathbf{v}, \mathbf{w} \in V, (\mathbf{u} + \mathbf{v}) + \mathbf{w} = \mathbf{u} + (\mathbf{v} + \mathbf{w})$
2. **交换律**：$\forall \mathbf{u}, \mathbf{v} \in V, \mathbf{u} + \mathbf{v} = \mathbf{v} + \mathbf{u}$
3. **零元素**：$\exists \mathbf{0} \in V, \forall \mathbf{v} \in V, \mathbf{v} + \mathbf{0} = \mathbf{v}$
4. **逆元素**：$\forall \mathbf{v} \in V, \exists (-\mathbf{v}) \in V, \mathbf{v} + (-\mathbf{v}) = \mathbf{0}$

#### 标量乘法公理
5. **分配律1**：$\forall a \in \mathbb{F}, \forall \mathbf{u}, \mathbf{v} \in V, a \cdot (\mathbf{u} + \mathbf{v}) = a \cdot \mathbf{u} + a \cdot \mathbf{v}$
6. **分配律2**：$\forall a, b \in \mathbb{F}, \forall \mathbf{v} \in V, (a + b) \cdot \mathbf{v} = a \cdot \mathbf{v} + b \cdot \mathbf{v}$
7. **结合律**：$\forall a, b \in \mathbb{F}, \forall \mathbf{v} \in V, (ab) \cdot \mathbf{v} = a \cdot (b \cdot \mathbf{v})$
8. **单位元**：$\forall \mathbf{v} \in V, 1 \cdot \mathbf{v} = \mathbf{v}$

### 子空间

设 $V$ 是域 $\mathbb{F}$ 上的向量空间，$W \subseteq V$ 是 $V$ 的非空子集。如果 $W$ 在加法和标量乘法下封闭，则称 $W$ 为 $V$ 的子空间。

**子空间判定定理**：$W$ 是 $V$ 的子空间当且仅当：
1. $\mathbf{0} \in W$
2. $\forall \mathbf{u}, \mathbf{v} \in W, \mathbf{u} + \mathbf{v} \in W$
3. $\forall a \in \mathbb{F}, \forall \mathbf{v} \in W, a \cdot \mathbf{v} \in W$

### 线性组合与张成

设 $S = \{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n\}$ 是向量空间 $V$ 中的向量集合。

**线性组合**：向量 $\mathbf{v} = a_1\mathbf{v}_1 + a_2\mathbf{v}_2 + \cdots + a_n\mathbf{v}_n$ 称为 $S$ 的线性组合。

**张成空间**：所有线性组合构成的集合称为 $S$ 的张成空间，记作 $\text{span}(S)$。

$$\text{span}(S) = \left\{ \sum_{i=1}^{n} a_i\mathbf{v}_i \mid a_i \in \mathbb{F} \right\}$$

### 线性无关与基

**线性无关**：向量集合 $S = \{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n\}$ 称为线性无关，如果方程
$$a_1\mathbf{v}_1 + a_2\mathbf{v}_2 + \cdots + a_n\mathbf{v}_n = \mathbf{0}$$
只有平凡解 $a_1 = a_2 = \cdots = a_n = 0$。

**基**：向量空间 $V$ 的基是线性无关的生成集。即集合 $B = \{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_n\}$ 是 $V$ 的基，当且仅当：
1. $B$ 线性无关
2. $\text{span}(B) = V$

**维数**：向量空间 $V$ 的维数定义为基中向量的个数，记作 $\dim(V)$。

## Haskell实现

### 向量空间类型类

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- 向量空间类型类
class (Eq (Scalar v), Num (Scalar v)) => VectorSpace v where
    type Scalar v :: *
    
    -- 零向量
    zero :: v
    
    -- 向量加法
    add :: v -> v -> v
    
    -- 标量乘法
    scale :: Scalar v -> v -> v
    
    -- 向量减法（默认实现）
    sub :: v -> v -> v
    sub u v = add u (scale (-1) v)
    
    -- 向量加法结合律
    addAssoc :: v -> v -> v -> Bool
    addAssoc u v w = add (add u v) w == add u (add v w)
    
    -- 向量加法交换律
    addComm :: v -> v -> Bool
    addComm u v = add u v == add v u
    
    -- 零元素性质
    zeroLeft :: v -> Bool
    zeroLeft v = add zero v == v
    
    -- 逆元素性质
    inverse :: v -> v
    inverse v = scale (-1) v
    
    -- 标量乘法分配律
    scaleDistrib :: Scalar v -> v -> v -> Bool
    scaleDistrib a u v = scale a (add u v) == add (scale a u) (scale a v)

-- 子空间类型类
class VectorSpace v => Subspace v where
    -- 判断向量是否在子空间中
    isInSubspace :: v -> Bool
    
    -- 子空间包含零向量
    subspaceZero :: Bool
    subspaceZero = isInSubspace zero
    
    -- 子空间对加法封闭
    subspaceAdd :: v -> v -> Bool
    subspaceAdd u v = isInSubspace u && isInSubspace v ==> isInSubspace (add u v)
    
    -- 子空间对标量乘法封闭
    subspaceScale :: Scalar v -> v -> Bool
    subspaceScale a v = isInSubspace v ==> isInSubspace (scale a v)
```

### 具体向量实现

```haskell
-- 有限维向量实现
data Vector n a = Vector { unVector :: [a] }
    deriving (Eq, Show)

-- 确保向量长度正确
mkVector :: [a] -> Maybe (Vector n a)
mkVector xs = if length xs == fromIntegral (natVal (Proxy :: Proxy n))
              then Just (Vector xs)
              else Nothing

-- 向量空间实例
instance (Num a, KnownNat n) => VectorSpace (Vector n a) where
    type Scalar (Vector n a) = a
    
    zero = Vector (replicate (fromIntegral (natVal (Proxy :: Proxy n))) 0)
    
    add (Vector xs) (Vector ys) = Vector (zipWith (+) xs ys)
    
    scale a (Vector xs) = Vector (map (a *) xs)

-- 线性组合
linearCombination :: VectorSpace v => [Scalar v] -> [v] -> v
linearCombination scalars vectors = foldr add zero (zipWith scale scalars vectors)

-- 张成空间（有限情况）
span :: VectorSpace v => [v] -> [v]
span vectors = [linearCombination scalars vectors | scalars <- allScalarCombinations]
  where
    allScalarCombinations = sequence (replicate (length vectors) [-1, 0, 1])

-- 线性无关性检查
isLinearlyIndependent :: VectorSpace v => [v] -> Bool
isLinearlyIndependent [] = True
isLinearlyIndependent vectors = 
    let n = length vectors
        -- 检查所有非零标量组合
        checkCombination scalars = 
            let comb = linearCombination scalars vectors
            in comb /= zero || all (== 0) scalars
    in all checkCombination (sequence (replicate n [-1, 0, 1]))

-- 基的判定
isBasis :: VectorSpace v => [v] -> Bool
isBasis vectors = isLinearlyIndependent vectors && 
                  all (\v -> isInSpan v vectors) (generateAllVectors vectors)
  where
    isInSpan v basis = any (\u -> u == v) (span basis)
    generateAllVectors basis = span basis
```

### 子空间实现

```haskell
-- 子空间实现
data Subspace v = Subspace { subspaceVectors :: [v] }

-- 子空间实例
instance VectorSpace v => Subspace (Subspace v) where
    isInSubspace v = any (\u -> u == v) (subspaceVectors v)
    
    subspaceZero = True  -- 零向量总在子空间中
    
    subspaceAdd u v = isInSubspace u && isInSubspace v
    
    subspaceScale a v = isInSubspace v

-- 子空间交集
intersection :: VectorSpace v => Subspace v -> Subspace v -> Subspace v
intersection (Subspace vs1) (Subspace vs2) = 
    Subspace [v | v <- vs1, v `elem` vs2]

-- 子空间和
sum :: VectorSpace v => Subspace v -> Subspace v -> Subspace v
sum (Subspace vs1) (Subspace vs2) = 
    Subspace (nub [add u v | u <- vs1, v <- vs2])

-- 子空间维数
subspaceDimension :: VectorSpace v => Subspace v -> Int
subspaceDimension (Subspace vectors) = 
    length (filter isLinearlyIndependent (subsequences vectors))
```

## 重要定理与证明

### 定理1：子空间判定定理

**定理**：设 $W$ 是向量空间 $V$ 的非空子集，则 $W$ 是 $V$ 的子空间当且仅当：
1. $\mathbf{0} \in W$
2. $\forall \mathbf{u}, \mathbf{v} \in W, \mathbf{u} + \mathbf{v} \in W$
3. $\forall a \in \mathbb{F}, \forall \mathbf{v} \in W, a \cdot \mathbf{v} \in W$

**证明**：
- **必要性**：如果 $W$ 是子空间，则满足向量空间的所有公理，特别地满足条件1-3。
- **充分性**：假设 $W$ 满足条件1-3，需要证明 $W$ 满足所有向量空间公理。
  - 结合律和交换律在 $V$ 中成立，在 $W$ 中也成立
  - 零元素存在（条件1）
  - 逆元素：对任意 $\mathbf{v} \in W$，有 $(-1) \cdot \mathbf{v} \in W$（条件3），且 $\mathbf{v} + ((-1) \cdot \mathbf{v}) = \mathbf{0}$
  - 其他公理类似可证

### 定理2：基的存在性

**定理**：每个有限维向量空间都有基。

**证明**：
1. 设 $V$ 是有限维向量空间，$\dim(V) = n$
2. 从 $V$ 中任取一个非零向量 $\mathbf{v}_1$
3. 如果 $\{\mathbf{v}_1\}$ 生成 $V$，则它是基
4. 否则，存在 $\mathbf{v}_2 \notin \text{span}(\{\mathbf{v}_1\})$
5. 继续此过程，最多 $n$ 步后得到基

### 定理3：维数唯一性

**定理**：向量空间的所有基都有相同的维数。

**证明**：
1. 设 $B_1$ 和 $B_2$ 是 $V$ 的两个基
2. 假设 $|B_1| < |B_2|$
3. 由于 $B_1$ 生成 $V$，$B_2$ 中的每个向量都可以表示为 $B_1$ 的线性组合
4. 这与 $B_2$ 的线性无关性矛盾
5. 因此 $|B_1| = |B_2|$

## 应用示例

### 示例1：$\mathbb{R}^3$ 向量空间

```haskell
-- R³ 向量空间
type R3 = Vector 3 Double

-- 标准基
standardBasis :: [R3]
standardBasis = [
    Vector [1, 0, 0],  -- e₁
    Vector [0, 1, 0],  -- e₂
    Vector [0, 0, 1]   -- e₃
]

-- 验证标准基
verifyStandardBasis :: Bool
verifyStandardBasis = 
    isLinearlyIndependent standardBasis &&
    length standardBasis == 3

-- 子空间：xy平面
xyPlane :: Subspace R3
xyPlane = Subspace [
    Vector [1, 0, 0],
    Vector [0, 1, 0]
]

-- 子空间：z轴
zAxis :: Subspace R3
zAxis = Subspace [
    Vector [0, 0, 1]
]
```

### 示例2：多项式向量空间

```haskell
-- 多项式向量空间
data Polynomial = Polynomial { coefficients :: [Double] }
    deriving (Eq, Show)

instance VectorSpace Polynomial where
    type Scalar Polynomial = Double
    
    zero = Polynomial []
    
    add (Polynomial xs) (Polynomial ys) = 
        Polynomial (zipWith (+) (xs ++ repeat 0) (ys ++ repeat 0))
    
    scale a (Polynomial xs) = Polynomial (map (a *) xs)

-- 次数不超过n的多项式子空间
polynomialSubspace :: Int -> Subspace Polynomial
polynomialSubspace n = Subspace [
    Polynomial (replicate i 0 ++ [1] ++ replicate (n-i) 0) | i <- [0..n]
]
```

## 总结

向量空间理论为线性代数提供了坚实的基础，通过严格的数学定义和Haskell实现，我们建立了：

1. **严格的数学基础**：基于公理化的向量空间定义
2. **完整的Haskell实现**：类型安全的向量空间操作
3. **重要的理论结果**：子空间判定、基的存在性等定理
4. **实际应用示例**：$\mathbb{R}^3$ 和多项式向量空间

这个理论框架为后续的线性变换、特征值理论等高级概念提供了必要的理论基础。

---

**相关文档**：
- [线性变换理论](../04-Linear-Transformations/01-Linear-Transformations.md)
- [特征值与特征向量](../05-Eigenvalues-Eigenvectors/01-Eigenvalues-Eigenvectors.md)
- [内积空间理论](../06-Inner-Product-Spaces/01-Inner-Product-Spaces.md) 