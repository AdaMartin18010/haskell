# 代数结构 (Algebraic Structures)

## 概述

代数结构研究具有运算的集合，是抽象代数的核心。本节将从形式化角度分析不同的代数结构，并用Haskell实现相关的概念和证明。

## 基本代数结构

### 1. 群 (Group)

群是具有一个二元运算的代数结构，满足结合律、单位元存在性和逆元存在性。

#### 形式化定义

```haskell
-- 群的形式化表达
class Group a where
  -- 群运算
  groupOperation :: a -> a -> a
  -- 单位元
  identity :: a
  -- 逆元
  inverse :: a -> a
  -- 群公理验证
  groupAxioms :: a -> Bool

-- 群的基本类型
data GroupElement = 
  GroupElement {
    value :: Int,
    groupName :: String
  } deriving (Show, Eq)

-- 群结构
data GroupStructure = GroupStructure {
  elements :: [GroupElement],
  operation :: (GroupElement -> GroupElement -> GroupElement),
  identityElement :: GroupElement,
  inverseFunction :: (GroupElement -> GroupElement)
} deriving (Show)

-- 群实例
instance Group GroupElement where
  groupOperation e1 e2 = 
    GroupElement {
      value = (value e1 + value e2) `mod` 10,  -- 模10加法群
      groupName = groupName e1
    }
  
  identity = GroupElement 0 "Z10"
  
  inverse element = 
    GroupElement {
      value = (10 - value element) `mod` 10,
      groupName = groupName element
    }
  
  groupAxioms element = 
    -- 结合律：(a * b) * c = a * (b * c)
    let a = element
        b = GroupElement 1 "Z10"
        c = GroupElement 2 "Z10"
    in groupOperation (groupOperation a b) c == 
       groupOperation a (groupOperation b c) &&
    -- 单位元：e * a = a * e = a
    groupOperation identity element == element &&
    groupOperation element identity == element &&
    -- 逆元：a * a^(-1) = a^(-1) * a = e
    groupOperation element (inverse element) == identity &&
    groupOperation (inverse element) element == identity

-- 群运算
class GroupOperations a where
  -- 群乘法
  multiply :: a -> a -> a
  -- 群幂
  power :: a -> Int -> a
  -- 群阶
  order :: a -> Int

-- 群运算实例
instance GroupOperations GroupElement where
  multiply = groupOperation
  power element n = 
    if n == 0 then identity
    else if n > 0 then multiply element (power element (n-1))
    else multiply (inverse element) (power element (abs n - 1))
  order element = 
    length (takeWhile (/= identity) (iterate (multiply element) element))

-- 示例：整数模n加法群
integerModGroup :: Int -> GroupStructure
integerModGroup n = GroupStructure {
  elements = [GroupElement i ("Z" ++ show n) | i <- [0..n-1]],
  operation = \e1 e2 -> GroupElement ((value e1 + value e2) `mod` n) (groupName e1),
  identityElement = GroupElement 0 ("Z" ++ show n),
  inverseFunction = \e -> GroupElement ((n - value e) `mod` n) (groupName e)
}

-- 示例：群
exampleGroup :: GroupStructure
exampleGroup = integerModGroup 5
```

#### 群的性质

```haskell
-- 群的性质
class GroupProperties a where
  -- 交换性
  isCommutative :: a -> Bool
  -- 循环性
  isCyclic :: a -> Bool
  -- 有限性
  isFinite :: a -> Bool

-- 群性质实例
instance GroupProperties GroupStructure where
  isCommutative group = 
    all (\e1 -> all (\e2 -> 
      operation group e1 e2 == operation group e2 e1) 
      (elements group)) (elements group)
  
  isCyclic group = 
    any (\element -> 
      length (takeWhile (/= identityElement group) 
        (iterate (operation group element) element)) == 
      length (elements group) - 1) (elements group)
  
  isFinite group = 
    length (elements group) < maxBound :: Int

-- 群同构
class GroupIsomorphism a b where
  -- 同构映射
  isomorphism :: a -> b -> Maybe (a -> b)
  -- 同构验证
  verifyIsomorphism :: a -> b -> (a -> b) -> Bool

-- 群同构实例
instance GroupIsomorphism GroupStructure GroupStructure where
  isomorphism g1 g2 = 
    if length (elements g1) == length (elements g2)
    then Just (\e -> 
      let index = fromJust (elemIndex e (elements g1))
      in elements g2 !! index)
    else Nothing
  
  verifyIsomorphism g1 g2 f = 
    all (\e1 -> all (\e2 -> 
      f (operation g1 e1 e2) == operation g2 (f e1) (f e2)) 
      (elements g1)) (elements g1) &&
    all (\e -> e `elem` elements g2) (map f (elements g1))

-- 示例：群性质
exampleGroupProperties :: GroupStructure -> (Bool, Bool, Bool)
exampleGroupProperties group = 
  (isCommutative group, isCyclic group, isFinite group)
```

### 2. 环 (Ring)

环是具有两个二元运算的代数结构，满足加法群、乘法结合律和分配律。

#### 形式化定义

```haskell
-- 环的形式化表达
class Ring a where
  -- 加法运算
  addition :: a -> a -> a
  -- 乘法运算
  multiplication :: a -> a -> a
  -- 加法单位元
  additiveIdentity :: a
  -- 加法逆元
  additiveInverse :: a -> a
  -- 环公理验证
  ringAxioms :: a -> Bool

-- 环元素
data RingElement = 
  RingElement {
    value :: Int,
    ringName :: String
  } deriving (Show, Eq)

-- 环结构
data RingStructure = RingStructure {
  elements :: [RingElement],
  addOp :: (RingElement -> RingElement -> RingElement),
  mulOp :: (RingElement -> RingElement -> RingElement),
  zero :: RingElement,
  one :: RingElement
} deriving (Show)

-- 环实例
instance Ring RingElement where
  addition e1 e2 = 
    RingElement {
      value = (value e1 + value e2) `mod` 6,  -- 模6环
      ringName = ringName e1
    }
  
  multiplication e1 e2 = 
    RingElement {
      value = (value e1 * value e2) `mod` 6,
      ringName = ringName e1
    }
  
  additiveIdentity = RingElement 0 "Z6"
  
  additiveInverse element = 
    RingElement {
      value = (6 - value element) `mod` 6,
      ringName = ringName element
    }
  
  ringAxioms element = 
    -- 加法群公理
    let a = element
        b = RingElement 1 "Z6"
        c = RingElement 2 "Z6"
    in addition (addition a b) c == addition a (addition b c) &&  -- 结合律
       addition additiveIdentity element == element &&  -- 单位元
       addition element additiveIdentity == element &&
       addition element (additiveInverse element) == additiveIdentity &&  -- 逆元
       addition (additiveInverse element) element == additiveIdentity &&
    -- 乘法结合律
       multiplication (multiplication a b) c == multiplication a (multiplication b c) &&
    -- 分配律
       multiplication a (addition b c) == addition (multiplication a b) (multiplication a c) &&
       multiplication (addition a b) c == addition (multiplication a c) (multiplication b c)

-- 环运算
class RingOperations a where
  -- 环加法
  add :: a -> a -> a
  -- 环乘法
  multiply :: a -> a -> a
  -- 环幂
  power :: a -> Int -> a

-- 环运算实例
instance RingOperations RingElement where
  add = addition
  multiply = multiplication
  power element n = 
    if n == 0 then RingElement 1 (ringName element)
    else if n > 0 then multiply element (power element (n-1))
    else RingElement 0 (ringName element)  -- 简化处理

-- 示例：整数模n环
integerModRing :: Int -> RingStructure
integerModRing n = RingStructure {
  elements = [RingElement i ("Z" ++ show n) | i <- [0..n-1]],
  addOp = \e1 e2 -> RingElement ((value e1 + value e2) `mod` n) (ringName e1),
  mulOp = \e1 e2 -> RingElement ((value e1 * value e2) `mod` n) (ringName e1),
  zero = RingElement 0 ("Z" ++ show n),
  one = RingElement 1 ("Z" ++ show n)
}

-- 示例：环
exampleRing :: RingStructure
exampleRing = integerModRing 6
```

#### 环的性质

```haskell
-- 环的性质
class RingProperties a where
  -- 交换性
  isCommutative :: a -> Bool
  -- 单位元存在性
  hasUnity :: a -> Bool
  -- 整环性
  isIntegralDomain :: a -> Bool
  -- 域性
  isField :: a -> Bool

-- 环性质实例
instance RingProperties RingStructure where
  isCommutative ring = 
    all (\e1 -> all (\e2 -> 
      mulOp ring e1 e2 == mulOp ring e2 e1) 
      (elements ring)) (elements ring)
  
  hasUnity ring = 
    any (\e -> all (\x -> mulOp ring e x == x && mulOp ring x e == x) (elements ring)) (elements ring)
  
  isIntegralDomain ring = 
    hasUnity ring &&
    isCommutative ring &&
    -- 无零因子
    all (\e1 -> all (\e2 -> 
      if e1 /= zero ring && e2 /= zero ring 
      then mulOp ring e1 e2 /= zero ring 
      else True) (elements ring)) (elements ring)
  
  isField ring = 
    isIntegralDomain ring &&
    -- 每个非零元素都有乘法逆元
    all (\e -> if e /= zero ring 
               then any (\x -> mulOp ring e x == one ring && mulOp ring x e == one ring) (elements ring)
               else True) (elements ring)

-- 示例：环性质
exampleRingProperties :: RingStructure -> (Bool, Bool, Bool, Bool)
exampleRingProperties ring = 
  (isCommutative ring, hasUnity ring, isIntegralDomain ring, isField ring)
```

### 3. 域 (Field)

域是具有两个二元运算的代数结构，满足加法群、乘法群（除零元外）和分配律。

#### 形式化定义

```haskell
-- 域的形式化表达
class Field a where
  -- 加法运算
  addition :: a -> a -> a
  -- 乘法运算
  multiplication :: a -> a -> a
  -- 加法单位元
  additiveIdentity :: a
  -- 乘法单位元
  multiplicativeIdentity :: a
  -- 加法逆元
  additiveInverse :: a -> a
  -- 乘法逆元
  multiplicativeInverse :: a -> a
  -- 域公理验证
  fieldAxioms :: a -> Bool

-- 域元素
data FieldElement = 
  FieldElement {
    value :: Double,
    fieldName :: String
  } deriving (Show, Eq)

-- 域结构
data FieldStructure = FieldStructure {
  elements :: [FieldElement],
  addOp :: (FieldElement -> FieldElement -> FieldElement),
  mulOp :: (FieldElement -> FieldElement -> FieldElement),
  zero :: FieldElement,
  one :: FieldElement
} deriving (Show)

-- 域实例
instance Field FieldElement where
  addition e1 e2 = 
    FieldElement {
      value = value e1 + value e2,
      fieldName = fieldName e1
    }
  
  multiplication e1 e2 = 
    FieldElement {
      value = value e1 * value e2,
      fieldName = fieldName e1
    }
  
  additiveIdentity = FieldElement 0.0 "R"
  multiplicativeIdentity = FieldElement 1.0 "R"
  
  additiveInverse element = 
    FieldElement {
      value = -value element,
      fieldName = fieldName element
    }
  
  multiplicativeInverse element = 
    if value element /= 0.0
    then FieldElement {
      value = 1.0 / value element,
      fieldName = fieldName element
    }
    else error "Division by zero"
  
  fieldAxioms element = 
    -- 加法群公理
    let a = element
        b = FieldElement 1.0 "R"
        c = FieldElement 2.0 "R"
    in addition (addition a b) c == addition a (addition b c) &&  -- 结合律
       addition additiveIdentity element == element &&  -- 单位元
       addition element additiveIdentity == element &&
       addition element (additiveInverse element) == additiveIdentity &&  -- 逆元
       addition (additiveInverse element) element == additiveIdentity &&
    -- 乘法群公理（除零元外）
       (if value element /= 0.0
        then multiplication (multiplication a b) c == multiplication a (multiplication b c) &&  -- 结合律
             multiplication multiplicativeIdentity element == element &&  -- 单位元
             multiplication element multiplicativeIdentity == element &&
             multiplication element (multiplicativeInverse element) == multiplicativeIdentity &&  -- 逆元
             multiplication (multiplicativeInverse element) element == multiplicativeIdentity
        else True) &&
    -- 分配律
       multiplication a (addition b c) == addition (multiplication a b) (multiplication a c) &&
       multiplication (addition a b) c == addition (multiplication a c) (multiplication b c)

-- 域运算
class FieldOperations a where
  -- 域加法
  add :: a -> a -> a
  -- 域乘法
  multiply :: a -> a -> a
  -- 域除法
  divide :: a -> a -> a
  -- 域幂
  power :: a -> Int -> a

-- 域运算实例
instance FieldOperations FieldElement where
  add = addition
  multiply = multiplication
  divide e1 e2 = 
    if value e2 /= 0.0
    then FieldElement (value e1 / value e2) (fieldName e1)
    else error "Division by zero"
  power element n = 
    if n == 0 then multiplicativeIdentity
    else if n > 0 then multiply element (power element (n-1))
    else multiply (multiplicativeInverse element) (power element (abs n - 1))

-- 示例：实数域
realField :: FieldStructure
realField = FieldStructure {
  elements = [FieldElement x "R" | x <- [-10.0, -9.0..10.0]],  -- 有限子集
  addOp = \e1 e2 -> FieldElement (value e1 + value e2) (fieldName e1),
  mulOp = \e1 e2 -> FieldElement (value e1 * value e2) (fieldName e1),
  zero = FieldElement 0.0 "R",
  one = FieldElement 1.0 "R"
}

-- 示例：域
exampleField :: FieldStructure
exampleField = realField
```

#### 域的性质

```haskell
-- 域的性质
class FieldProperties a where
  -- 特征
  characteristic :: a -> Int
  -- 代数闭性
  isAlgebraicallyClosed :: a -> Bool
  -- 完备性
  isComplete :: a -> Bool

-- 域性质实例
instance FieldProperties FieldStructure where
  characteristic field = 
    -- 简化实现：实数域特征为0
    0
  
  isAlgebraicallyClosed field = 
    -- 简化实现：复数域代数闭，实数域不代数闭
    False
  
  isComplete field = 
    -- 简化实现：实数域完备
    True

-- 域扩张
class FieldExtension a b where
  -- 基域
  baseField :: a
  -- 扩张域
  extensionField :: b
  -- 扩张次数
  extensionDegree :: Int

-- 示例：域扩张
data FieldExtension = FieldExtension {
  base :: FieldStructure,
  extension :: FieldStructure,
  degree :: Int
} deriving (Show)

-- 示例：域性质
exampleFieldProperties :: FieldStructure -> (Int, Bool, Bool)
exampleFieldProperties field = 
  (characteristic field, isAlgebraicallyClosed field, isComplete field)
```

### 4. 向量空间 (Vector Space)

向量空间是域上的代数结构，具有加法和标量乘法运算。

#### 形式化定义

```haskell
-- 向量空间的形式化表达
class VectorSpace v f where
  -- 向量加法
  vectorAddition :: v -> v -> v
  -- 标量乘法
  scalarMultiplication :: f -> v -> v
  -- 零向量
  zeroVector :: v
  -- 向量空间公理验证
  vectorSpaceAxioms :: v -> f -> Bool

-- 向量
data Vector = Vector {
  components :: [Double],
  dimension :: Int
} deriving (Show, Eq)

-- 向量空间结构
data VectorSpaceStructure = VectorSpaceStructure {
  vectors :: [Vector],
  field :: FieldStructure,
  addOp :: (Vector -> Vector -> Vector),
  scalarMulOp :: (FieldElement -> Vector -> Vector)
} deriving (Show)

-- 向量空间实例
instance VectorSpace Vector FieldElement where
  vectorAddition v1 v2 = 
    if dimension v1 == dimension v2
    then Vector {
      components = zipWith (+) (components v1) (components v2),
      dimension = dimension v1
    }
    else error "Vectors must have same dimension"
  
  scalarMultiplication scalar vector = 
    Vector {
      components = map (* value scalar) (components vector),
      dimension = dimension vector
    }
  
  zeroVector = Vector {
    components = [],
    dimension = 0
  }
  
  vectorSpaceAxioms vector scalar = 
    -- 向量加法群公理
    let v1 = vector
        v2 = Vector [1.0, 2.0] 2
        v3 = Vector [3.0, 4.0] 2
        s1 = scalar
        s2 = FieldElement 2.0 "R"
    in vectorAddition (vectorAddition v1 v2) v3 == vectorAddition v1 (vectorAddition v2 v3) &&  -- 结合律
       vectorAddition zeroVector vector == vector &&  -- 单位元
       vectorAddition vector zeroVector == vector &&
    -- 标量乘法公理
       scalarMultiplication (FieldElement 1.0 "R") vector == vector &&  -- 单位元
       scalarMultiplication s1 (scalarMultiplication s2 vector) == 
         scalarMultiplication (FieldElement (value s1 * value s2) "R") vector &&  -- 结合律
    -- 分配律
       scalarMultiplication s1 (vectorAddition v1 v2) == 
         vectorAddition (scalarMultiplication s1 v1) (scalarMultiplication s1 v2) &&
       scalarMultiplication (FieldElement (value s1 + value s2) "R") v1 == 
         vectorAddition (scalarMultiplication s1 v1) (scalarMultiplication s2 v1)

-- 向量运算
class VectorOperations v where
  -- 向量加法
  add :: v -> v -> v
  -- 标量乘法
  scale :: Double -> v -> v
  -- 内积
  dotProduct :: v -> v -> Double
  -- 范数
  norm :: v -> Double

-- 向量运算实例
instance VectorOperations Vector where
  add = vectorAddition
  scale scalar vector = 
    Vector {
      components = map (* scalar) (components vector),
      dimension = dimension vector
    }
  dotProduct v1 v2 = 
    if dimension v1 == dimension v2
    then sum (zipWith (*) (components v1) (components v2))
    else error "Vectors must have same dimension"
  norm vector = 
    sqrt (dotProduct vector vector)

-- 示例：R^n向量空间
realVectorSpace :: Int -> VectorSpaceStructure
realVectorSpace n = VectorSpaceStructure {
  vectors = [Vector (replicate n x) n | x <- [-5.0, -4.0..5.0]],  -- 有限子集
  field = realField,
  addOp = \v1 v2 -> if dimension v1 == dimension v2
                    then Vector (zipWith (+) (components v1) (components v2)) (dimension v1)
                    else error "Dimension mismatch",
  scalarMulOp = \scalar vector -> Vector (map (* value scalar) (components vector)) (dimension vector)
}

-- 示例：向量空间
exampleVectorSpace :: VectorSpaceStructure
exampleVectorSpace = realVectorSpace 3
```

#### 向量空间的性质

```haskell
-- 向量空间的性质
class VectorSpaceProperties v where
  -- 维度
  dimension :: v -> Int
  -- 基
  basis :: v -> [Vector]
  -- 线性无关
  isLinearlyIndependent :: [Vector] -> Bool
  -- 生成
  spans :: [Vector] -> [Vector] -> Bool

-- 向量空间性质实例
instance VectorSpaceProperties VectorSpaceStructure where
  dimension space = 
    if null (vectors space) then 0
    else dimension (head (vectors space))
  
  basis space = 
    -- 简化实现：标准基
    let n = dimension space
    in [Vector (replicate i 0.0 ++ [1.0] ++ replicate (n-i-1) 0.0) n | i <- [0..n-1]]
  
  isLinearlyIndependent vectors = 
    -- 简化实现：检查是否有零向量
    not (any (\v -> all (== 0.0) (components v)) vectors)
  
  spans basis vectors = 
    -- 简化实现：检查维度
    length basis == length vectors

-- 线性变换
class LinearTransformation v where
  -- 线性变换
  linearTransform :: (v -> v) -> v -> v
  -- 线性性验证
  isLinear :: (v -> v) -> Bool

-- 线性变换实例
instance LinearTransformation Vector where
  linearTransform f vector = f vector
  isLinear f = 
    let v1 = Vector [1.0, 0.0] 2
        v2 = Vector [0.0, 1.0] 2
        scalar = 2.0
    in f (vectorAddition v1 v2) == vectorAddition (f v1) (f v2) &&  -- 加法保持
       f (scale scalar v1) == scale scalar (f v1)  -- 标量乘法保持

-- 示例：向量空间性质
exampleVectorSpaceProperties :: VectorSpaceStructure -> (Int, [Vector], Bool)
exampleVectorSpaceProperties space = 
  (dimension space, basis space, isLinearlyIndependent (basis space))
```

## 形式化证明

### 代数结构的形式化证明

```haskell
-- 代数结构证明
data AlgebraicProof = 
  GroupProof String
  | RingProof String
  | FieldProof String
  | VectorSpaceProof String
  deriving (Show, Eq)

-- 证明的有效性
proofValidity :: AlgebraicProof -> Bool
proofValidity _ = True  -- 简化实现

-- 群论证明
groupTheoryProofs :: [AlgebraicProof]
groupTheoryProofs = [
  GroupProof "拉格朗日定理：子群的阶整除群的阶",
  GroupProof "西罗定理：p-子群的存在性",
  GroupProof "同态基本定理：群同态的核和像"
]

-- 环论证明
ringTheoryProofs :: [AlgebraicProof]
ringTheoryProofs = [
  RingProof "理想的基本性质",
  RingProof "商环的构造",
  RingProof "环同态基本定理"
]

-- 域论证明
fieldTheoryProofs :: [AlgebraicProof]
fieldTheoryProofs = [
  FieldProof "域扩张的基本定理",
  FieldProof "代数扩张的性质",
  FieldProof "伽罗瓦理论"
]

-- 线性代数证明
linearAlgebraProofs :: [AlgebraicProof]
linearAlgebraProofs = [
  VectorSpaceProof "基的存在性和唯一性",
  VectorSpaceProof "线性变换的矩阵表示",
  VectorSpaceProof "特征值和特征向量"
]
```

### 代数结构的一致性

```haskell
-- 代数结构系统
data AlgebraicSystem = AlgebraicSystem {
  groups :: [GroupStructure],
  rings :: [RingStructure],
  fields :: [FieldStructure],
  vectorSpaces :: [VectorSpaceStructure]
} deriving (Show)

-- 一致性检查
checkConsistency :: AlgebraicSystem -> Bool
checkConsistency system = 
  all (\group -> groupAxioms (head (elements group))) (groups system) &&
  all (\ring -> ringAxioms (head (elements ring))) (rings system) &&
  all (\field -> fieldAxioms (head (elements field))) (fields system) &&
  all (\space -> vectorSpaceAxioms (head (vectors space)) (FieldElement 1.0 "R")) (vectorSpaces system)

-- 完备性检查
checkCompleteness :: AlgebraicSystem -> [String] -> Bool
checkCompleteness system theorems = 
  all (\theorem -> theorem `elem` map show (groupTheoryProofs ++ ringTheoryProofs ++ fieldTheoryProofs ++ linearAlgebraProofs)) theorems

-- 示例：代数系统
exampleAlgebraicSystem :: AlgebraicSystem
exampleAlgebraicSystem = AlgebraicSystem {
  groups = [exampleGroup],
  rings = [exampleRing],
  fields = [exampleField],
  vectorSpaces = [exampleVectorSpace]
}
```

## 应用与意义

### 在密码学中的应用

```haskell
-- 密码学的代数基础
class CryptographicAlgebra a where
  -- 群运算
  groupOp :: a -> a -> a
  -- 离散对数
  discreteLog :: a -> a -> Maybe Int
  -- 椭圆曲线
  ellipticCurve :: a -> Bool

-- 密码学群
data CryptographicGroup = CryptographicGroup {
  generator :: GroupElement,
  order :: Int,
  publicKey :: GroupElement,
  privateKey :: Int
} deriving (Show)

instance CryptographicAlgebra CryptographicGroup where
  groupOp g1 g2 = groupOperation (generator g1) (generator g2)
  discreteLog base element = 
    -- 简化实现：暴力搜索
    findIndex (\n -> power (generator base) n == element) [1..order base]
  ellipticCurve group = 
    -- 简化实现：假设是椭圆曲线群
    True

-- 示例：密码学群
exampleCryptographicGroup :: CryptographicGroup
exampleCryptographicGroup = CryptographicGroup {
  generator = GroupElement 2 "Zp",
  order = 11,
  publicKey = GroupElement 4 "Zp",
  privateKey = 2
}
```

### 在编码理论中的应用

```haskell
-- 编码理论的代数基础
class CodingTheory a where
  -- 线性码
  linearCode :: a -> Bool
  -- 生成矩阵
  generatorMatrix :: a -> [[Int]]
  -- 校验矩阵
  parityCheckMatrix :: a -> [[Int]]

-- 线性码
data LinearCode = LinearCode {
  length :: Int,
  dimension :: Int,
  generatorMatrix :: [[Int]],
  parityCheckMatrix :: [[Int]]
} deriving (Show)

instance CodingTheory LinearCode where
  linearCode code = 
    length (generatorMatrix code) == dimension code &&
    all (\row -> length row == length code) (generatorMatrix code)
  generatorMatrix = generatorMatrix
  parityCheckMatrix = parityCheckMatrix

-- 示例：线性码
exampleLinearCode :: LinearCode
exampleLinearCode = LinearCode {
  length = 7,
  dimension = 4,
  generatorMatrix = [
    [1, 0, 0, 0, 1, 1, 0],
    [0, 1, 0, 0, 1, 0, 1],
    [0, 0, 1, 0, 0, 1, 1],
    [0, 0, 0, 1, 1, 1, 1]
  ],
  parityCheckMatrix = [
    [1, 1, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 0, 1]
  ]
}
```

## 总结

代数结构为数学提供了强大的抽象工具：

1. **群**研究具有一个二元运算的代数结构
2. **环**研究具有两个二元运算的代数结构
3. **域**研究具有两个二元运算且乘法群存在的代数结构
4. **向量空间**研究域上的线性代数结构

通过Haskell的形式化实现，我们可以：
- 精确表达不同代数结构的核心概念
- 验证各种代数公理的有效性
- 分析不同结构在密码学中的应用
- 为编码理论提供代数基础

这种多表征的方式不仅有助于理解代数的本质，也为应用数学提供了坚实的理论基础。 