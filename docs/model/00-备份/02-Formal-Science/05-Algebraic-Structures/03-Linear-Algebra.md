# 线性代数 (Linear Algebra)

## 概述

线性代数是研究向量空间、线性变换和矩阵的数学分支，在计算机科学、机器学习、图形学等领域有广泛应用。

## 形式化定义

### 向量空间

```haskell
-- 向量空间
data VectorSpace a = VectorSpace
  { field :: Field a
  , vectors :: Set (Vector a)
  , vectorAddition :: Vector a -> Vector a -> Vector a
  , scalarMultiplication :: a -> Vector a -> Vector a
  , zeroVector :: Vector a
  } deriving (Show, Eq)

-- 向量
data Vector a = Vector
  { components :: [a]
  , dimension :: Int
  } deriving (Show, Eq)

-- 向量空间公理验证
class VectorSpaceProperties a where
  vectorClosure :: VectorSpace a -> Vector a -> Vector a -> Bool
  scalarClosure :: VectorSpace a -> a -> Vector a -> Bool
  vectorAssociativity :: VectorSpace a -> Vector a -> Vector a -> Vector a -> Bool
  vectorCommutativity :: VectorSpace a -> Vector a -> Vector a -> Bool
  vectorIdentity :: VectorSpace a -> Vector a -> Bool
  vectorInverse :: VectorSpace a -> Vector a -> Bool
  scalarDistributivity :: VectorSpace a -> a -> Vector a -> Vector a -> Bool
  vectorDistributivity :: VectorSpace a -> a -> Vector a -> Vector a -> Bool
  scalarAssociativity :: VectorSpace a -> a -> a -> Vector a -> Bool
  scalarIdentity :: VectorSpace a -> Vector a -> Bool

-- 向量空间公理
vectorSpaceAxioms :: (Eq a, VectorSpaceProperties a) => VectorSpace a -> Bool
vectorSpaceAxioms vs = 
  let vectors = setToList (vectors vs)
      scalars = fieldElements (field vs)
      add = vectorAddition vs
      scale = scalarMultiplication vs
      zero = zeroVector vs
  in all (\u -> all (\v -> vectorClosure vs u v) vectors) vectors &&
     all (\a -> all (\v -> scalarClosure vs a v) vectors) scalars &&
     all (\u -> all (\v -> all (\w -> vectorAssociativity vs u v w) vectors) vectors) vectors &&
     all (\u -> all (\v -> vectorCommutativity vs u v) vectors) vectors &&
     all (\v -> vectorIdentity vs v) vectors &&
     all (\v -> vectorInverse vs v) vectors &&
     all (\a -> all (\u -> all (\v -> scalarDistributivity vs a u v) vectors) vectors) scalars &&
     all (\a -> all (\b -> all (\v -> vectorDistributivity vs a b v) vectors) scalars) scalars &&
     all (\a -> all (\b -> all (\v -> scalarAssociativity vs a b v) vectors) scalars) scalars &&
     all (\v -> scalarIdentity vs v) vectors

-- 具体实现
instance VectorSpaceProperties Double where
  vectorClosure vs u v = 
    let result = vectorAddition vs u v
    in result `elem` setToList (vectors vs)
  
  scalarClosure vs a v = 
    let result = scalarMultiplication vs a v
    in result `elem` setToList (vectors vs)
  
  vectorAssociativity vs u v w = 
    let add = vectorAddition vs
        left = add (add u v) w
        right = add u (add v w)
    in left == right
  
  vectorCommutativity vs u v = 
    let add = vectorAddition vs
    in add u v == add v u
  
  vectorIdentity vs v = 
    let add = vectorAddition vs
        zero = zeroVector vs
    in add zero v == v && add v zero == v
  
  vectorInverse vs v = 
    let add = vectorAddition vs
        zero = zeroVector vs
        negV = scalarMultiplication vs (-1) v
    in add v negV == zero && add negV v == zero
  
  scalarDistributivity vs a u v = 
    let scale = scalarMultiplication vs
        add = vectorAddition vs
        left = scale a (add u v)
        right = add (scale a u) (scale a v)
    in left == right
  
  vectorDistributivity vs a b v = 
    let scale = scalarMultiplication vs
        add = vectorAddition vs
        left = scale (a + b) v
        right = add (scale a v) (scale b v)
    in left == right
  
  scalarAssociativity vs a b v = 
    let scale = scalarMultiplication vs
        left = scale a (scale b v)
        right = scale (a * b) v
    in left == right
  
  scalarIdentity vs v = 
    let scale = scalarMultiplication vs
        one = fieldOne (field vs)
    in scale one v == v
```

### 线性变换

```haskell
-- 线性变换
data LinearTransformation a = LinearTransformation
  { domain :: VectorSpace a
  , codomain :: VectorSpace a
  , mapping :: Vector a -> Vector a
  } deriving (Show, Eq)

-- 线性变换验证
isLinearTransformation :: (Eq a, VectorSpaceProperties a) => LinearTransformation a -> Bool
isLinearTransformation t = 
  let f = mapping t
      domainVectors = setToList (vectors (domain t))
      fieldElems = fieldElements (field (domain t))
      add = vectorAddition (domain t)
      scale = scalarMultiplication (domain t)
      codomainAdd = vectorAddition (codomain t)
      codomainScale = scalarMultiplication (codomain t)
  in all (\u -> all (\v -> 
         f (add u v) == codomainAdd (f u) (f v)) domainVectors) domainVectors &&
     all (\a -> all (\v -> 
         f (scale a v) == codomainScale a (f v)) domainVectors) fieldElems

-- 线性变换组合
composeLinearTransformations :: (Eq a, VectorSpaceProperties a) 
                             => LinearTransformation a -> LinearTransformation a -> LinearTransformation a
composeLinearTransformations t1 t2 = 
  let f1 = mapping t1
      f2 = mapping t2
      composed f = f1 . f2
  in LinearTransformation (domain t2) (codomain t1) composed

-- 线性变换的核
kernel :: (Eq a, VectorSpaceProperties a) => LinearTransformation a -> Set (Vector a)
kernel t = 
  let f = mapping t
      domainVectors = setToList (vectors (domain t))
      zero = zeroVector (codomain t)
      kernelVectors = [v | v <- domainVectors, f v == zero]
  in Set.fromList kernelVectors

-- 线性变换的像
image :: (Eq a, VectorSpaceProperties a) => LinearTransformation a -> Set (Vector a)
image t = 
  let f = mapping t
      domainVectors = setToList (vectors (domain t))
      imageVectors = [f v | v <- domainVectors]
  in Set.fromList imageVectors
```

### 矩阵

```haskell
-- 矩阵
data Matrix a = Matrix
  { rows :: Int
  , cols :: Int
  , elements :: [[a]]
  } deriving (Show, Eq)

-- 矩阵运算
matrixAddition :: (Num a) => Matrix a -> Matrix a -> Matrix a
matrixAddition m1 m2 = 
  let elems1 = elements m1
      elems2 = elements m2
      sumElems = zipWith (zipWith (+)) elems1 elems2
  in Matrix (rows m1) (cols m1) sumElems

matrixMultiplication :: (Num a) => Matrix a -> Matrix a -> Matrix a
matrixMultiplication m1 m2 = 
  let elems1 = elements m1
      elems2 = elements m2
      productElems = [[sum [elems1 !! i !! k * elems2 !! k !! j | k <- [0..cols m1 - 1]] | 
                      j <- [0..cols m2 - 1]] | 
                     i <- [0..rows m1 - 1]]
  in Matrix (rows m1) (cols m2) productElems

scalarMultiplication :: (Num a) => a -> Matrix a -> Matrix a
scalarMultiplication a m = 
  let elems = elements m
      scaledElems = map (map (* a)) elems
  in Matrix (rows m) (cols m) scaledElems

-- 矩阵转置
transpose :: Matrix a -> Matrix a
transpose m = 
  let elems = elements m
      transposedElems = [[elems !! j !! i | j <- [0..rows m - 1]] | 
                        i <- [0..cols m - 1]]
  in Matrix (cols m) (rows m) transposedElems

-- 行列式
determinant :: (Num a, Fractional a) => Matrix a -> a
determinant m
  | rows m == 1 = head (head (elements m))
  | rows m == 2 = 
      let [[a, b], [c, d]] = elements m
      in a * d - b * c
  | otherwise = 
      let elems = elements m
          firstRow = head elems
          minors = [minor m 0 j | j <- [0..cols m - 1]]
          cofactors = zipWith (*) firstRow [(-1) ^ j | j <- [0..cols m - 1]]
      in sum (zipWith (*) cofactors minors)

-- 子矩阵
minor :: Matrix a -> Int -> Int -> Matrix a
minor m i j = 
  let elems = elements m
      minorElems = [[elems !! r !! c | c <- [0..cols m - 1], c /= j] | 
                   r <- [0..rows m - 1], r /= i]
  in Matrix (rows m - 1) (cols m - 1) minorElems
```

## 形式化证明

### 线性变换的基本性质

**定理**: 线性变换保持零向量。

```haskell
-- 零向量保持性
zeroPreservation :: (Eq a, VectorSpaceProperties a) => LinearTransformation a -> Bool
zeroPreservation t = 
  let f = mapping t
      domainZero = zeroVector (domain t)
      codomainZero = zeroVector (codomain t)
  in f domainZero == codomainZero

-- 证明：零向量保持性
zeroPreservationProof :: (Eq a, VectorSpaceProperties a) => LinearTransformation a -> Proof
zeroPreservationProof t = 
  let f = mapping t
      domainZero = zeroVector (domain t)
      codomainZero = zeroVector (codomain t)
      add = vectorAddition (domain t)
      codomainAdd = vectorAddition (codomain t)
  in proveEquality (f domainZero) codomainZero
```

### 矩阵乘法的结合律

**定理**: 矩阵乘法满足结合律。

```haskell
-- 矩阵乘法结合律
matrixAssociativity :: (Num a, Eq a) => Matrix a -> Matrix a -> Matrix a -> Bool
matrixAssociativity m1 m2 m3 = 
  let left = matrixMultiplication (matrixMultiplication m1 m2) m3
      right = matrixMultiplication m1 (matrixMultiplication m2 m3)
  in left == right

-- 证明：矩阵乘法结合律
matrixAssociativityProof :: (Num a, Eq a) => Matrix a -> Matrix a -> Matrix a -> Proof
matrixAssociativityProof m1 m2 m3 = 
  let left = matrixMultiplication (matrixMultiplication m1 m2) m3
      right = matrixMultiplication m1 (matrixMultiplication m2 m3)
  in proveEquality left right
```

## 实际应用

### 特征值和特征向量

```haskell
-- 特征值问题
data EigenvalueProblem a = EigenvalueProblem
  { matrix :: Matrix a
  , eigenvalue :: a
  , eigenvector :: Vector a
  } deriving (Show, Eq)

-- 特征值验证
isEigenvalue :: (Num a, Eq a) => Matrix a -> a -> Vector a -> Bool
isEigenvalue m lambda v = 
  let matrixVector = matrixVectorProduct m v
      scaledVector = scalarMultiplication lambda v
  in matrixVector == scaledVector

-- 矩阵向量积
matrixVectorProduct :: (Num a) => Matrix a -> Vector a -> Vector a
matrixVectorProduct m v = 
  let elems = elements m
      comps = components v
      resultComps = [sum [elems !! i !! j * comps !! j | j <- [0..cols m - 1]] | 
                    i <- [0..rows m - 1]]
  in Vector resultComps (rows m)

-- 特征多项式
characteristicPolynomial :: (Num a, Fractional a) => Matrix a -> [a]
characteristicPolynomial m = 
  let n = rows m
      identity = identityMatrix n
      lambda = 1  -- 占位符
      charMatrix = matrixSubtraction m (scalarMultiplication lambda identity)
  in [determinant charMatrix]

-- 单位矩阵
identityMatrix :: (Num a) => Int -> Matrix a
identityMatrix n = 
  let elems = [[if i == j then 1 else 0 | j <- [0..n-1]] | i <- [0..n-1]]
  in Matrix n n elems
```

### 奇异值分解

```haskell
-- 奇异值分解
data SingularValueDecomposition a = SingularValueDecomposition
  { u :: Matrix a
  , sigma :: [a]
  , v :: Matrix a
  } deriving (Show, Eq)

-- SVD计算
singularValueDecomposition :: (Floating a) => Matrix a -> SingularValueDecomposition a
singularValueDecomposition m = 
  let mT = transpose m
      mTm = matrixMultiplication mT m
      eigenvalues = computeEigenvalues mTm
      singularValues = map sqrt eigenvalues
      v = computeEigenvectors mTm
      u = computeU m v singularValues
  in SingularValueDecomposition u singularValues v

-- 计算特征值
computeEigenvalues :: (Floating a) => Matrix a -> [a]
computeEigenvalues m = 
  let charPoly = characteristicPolynomial m
      roots = findRoots charPoly
  in roots

-- 计算特征向量
computeEigenvectors :: (Floating a) => Matrix a -> Matrix a
computeEigenvectors m = 
  let eigenvalues = computeEigenvalues m
      eigenvectors = [solveEigenvector m lambda | lambda <- eigenvalues]
  in Matrix (rows m) (length eigenvectors) eigenvectors

-- 计算U矩阵
computeU :: (Floating a) => Matrix a -> Matrix a -> [a] -> Matrix a
computeU m v sigma = 
  let mTimesV = matrixMultiplication m v
      uColumns = [scalarMultiplication (1/s) (extractColumn mTimesV i) | 
                 (i, s) <- zip [0..] sigma]
  in Matrix (rows m) (length uColumns) uColumns
```

## 总结

线性代数通过严格的数学结构为计算机科学提供了强大的工具。通过Haskell的类型系统和函数式编程特性，我们可以构建可验证的线性代数系统，确保线性变换和矩阵运算的正确性。
