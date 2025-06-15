# 群论基础

## 概述

群论是抽象代数的核心分支，研究具有二元运算的代数结构。群的概念在数学、物理、化学和计算机科学中都有广泛应用，是现代数学的重要基础。

## 形式化定义

### 群的基本定义

#### 群公理

群是一个集合 $G$ 连同二元运算 $\cdot: G \times G \to G$，满足以下公理：

1. **封闭性**：$\forall a, b \in G: a \cdot b \in G$
2. **结合律**：$\forall a, b, c \in G: (a \cdot b) \cdot c = a \cdot (b \cdot c)$
3. **单位元**：$\exists e \in G: \forall a \in G: e \cdot a = a \cdot e = a$
4. **逆元**：$\forall a \in G: \exists a^{-1} \in G: a \cdot a^{-1} = a^{-1} \cdot a = e$

```haskell
-- 群的定义
class Group g where
  -- 群运算
  (·) :: g -> g -> g
  
  -- 单位元
  identity :: g
  
  -- 逆元
  inverse :: g -> g
  
  -- 群公理验证
  isClosed :: [g] -> Bool
  isAssociative :: [g] -> Bool
  hasIdentity :: [g] -> Bool
  hasInverses :: [g] -> Bool
  
  -- 默认实现
  isClosed elements = 
    let pairs = [(a, b) | a <- elements, b <- elements]
    in all (\(a, b) -> a · b `elem` elements) pairs
    
  isAssociative elements = 
    let triples = [(a, b, c) | a <- elements, b <- elements, c <- elements]
    in all (\(a, b, c) -> (a · b) · c == a · (b · c)) triples
    
  hasIdentity elements = 
    let e = identity
    in e `elem` elements && 
       all (\a -> e · a == a && a · e == a) elements
       
  hasInverses elements = 
    all (\a -> let a' = inverse a in a' `elem` elements && 
               a · a' == identity && a' · a == identity) elements

-- 群实例
instance Group Integer where
  (·) = (+)
  identity = 0
  inverse = negate
  
instance Group Rational where
  (·) = (*)
  identity = 1
  inverse = recip
```

#### 有限群

```haskell
-- 有限群
data FiniteGroup a = FiniteGroup {
  elements :: [a],
  operation :: a -> a -> a,
  unit :: a,
  inv :: a -> a
} deriving (Show)

-- 群表
groupTable :: (Eq a, Show a) => FiniteGroup a -> [[a]]
groupTable (FiniteGroup elems op _ _) = 
  [[op a b | b <- elems] | a <- elems]

-- 群表显示
showGroupTable :: (Eq a, Show a) => FiniteGroup a -> String
showGroupTable group = 
  let table = groupTable group
      header = "  " ++ unwords (map show (elements group))
      rows = zipWith (\a row -> show a ++ " " ++ unwords (map show row)) 
                     (elements group) table
  in unlines (header : rows)

-- 克莱因四元群
kleinFourGroup :: FiniteGroup String
kleinFourGroup = FiniteGroup {
  elements = ["e", "a", "b", "c"],
  operation = \x y -> case (x, y) of
    ("e", _) -> y
    (_, "e") -> x
    ("a", "a") -> "e"
    ("a", "b") -> "c"
    ("a", "c") -> "b"
    ("b", "a") -> "c"
    ("b", "b") -> "e"
    ("b", "c") -> "a"
    ("c", "a") -> "b"
    ("c", "b") -> "a"
    ("c", "c") -> "e"
    _ -> "e",
  unit = "e",
  inv = \x -> case x of
    "e" -> "e"
    "a" -> "a"
    "b" -> "b"
    "c" -> "c"
    _ -> "e"
}
```

### 子群

#### 子群定义

```haskell
-- 子群
class (Group g) => Subgroup g where
  isSubgroup :: [g] -> Bool
  generateSubgroup :: [g] -> [g]
  
  isSubgroup subset = 
    let e = identity
    in e `elem` subset &&
       isClosed subset &&
       all (\a -> inverse a `elem` subset) subset
       
  generateSubgroup generators = 
    let initial = identity : generators
        closure = iterate (addProducts initial) initial
    in last closure
    
  where
    addProducts base current = 
      let products = [a · b | a <- current, b <- current]
      in nub (current ++ products)

-- 循环子群
cyclicSubgroup :: (Group g) => g -> [g]
cyclicSubgroup g = 
  let powers = iterate (· g) identity
      finite = takeWhile (/= identity) powers
  in identity : finite

-- 子群阶数
subgroupOrder :: (Group g) => [g] -> Int
subgroupOrder = length . nub
```

#### 正规子群

```haskell
-- 正规子群
class (Group g) => NormalSubgroup g where
  isNormal :: [g] -> Bool
  leftCoset :: [g] -> g -> [g]
  rightCoset :: [g] -> g -> [g]
  
  isNormal subgroup = 
    let allElements = getAllElements  -- 需要实现
    in all (\g -> leftCoset subgroup g == rightCoset subgroup g) allElements
    
  leftCoset subgroup g = 
    [g · h | h <- subgroup]
    
  rightCoset subgroup g = 
    [h · g | h <- subgroup]

-- 商群
quotientGroup :: (Group g) => [g] -> FiniteGroup [g]
quotientGroup normalSubgroup = 
  let cosets = generateCosets normalSubgroup
      cosetOp = \c1 c2 -> [a · b | a <- c1, b <- c2]
      cosetUnit = normalSubgroup
      cosetInv = \coset -> [inverse a | a <- coset]
  in FiniteGroup cosets cosetOp cosetUnit cosetInv

generateCosets :: (Group g) => [g] -> [[g]]
generateCosets normalSubgroup = 
  let allElements = getAllElements  -- 需要实现
      representatives = findRepresentatives allElements normalSubgroup
  in map (\g -> leftCoset normalSubgroup g) representatives
```

### 群同态

#### 同态定义

```haskell
-- 群同态
class (Group g, Group h) => GroupHomomorphism g h where
  homomorphism :: g -> h
  isHomomorphism :: (g -> h) -> Bool
  
  isHomomorphism f = 
    let allPairs = getAllPairs  -- 需要实现
    in all (\(a, b) -> f (a · b) == f a · f b) allPairs

-- 同态性质
class (Group g, Group h) => HomomorphismProperties g h where
  preservesIdentity :: (g -> h) -> Bool
  preservesInverses :: (g -> h) -> Bool
  kernel :: (g -> h) -> [g]
  image :: (g -> h) -> [h]
  
  preservesIdentity f = 
    f identity == identity
    
  preservesInverses f = 
    all (\a -> f (inverse a) == inverse (f a)) getAllElements
    
  kernel f = 
    filter (\a -> f a == identity) getAllElements
    
  image f = 
    nub [f a | a <- getAllElements]

-- 同构
class (Group g, Group h) => GroupIsomorphism g h where
  isomorphism :: g -> h
  inverseIsomorphism :: h -> g
  isIsomorphism :: (g -> h) -> Bool
  
  isIsomorphism f = 
    isHomomorphism f && isBijective f
```

## 形式化证明

### 群的基本定理

#### 定理1：单位元唯一性

群中的单位元是唯一的。

**证明**：
```haskell
-- 单位元唯一性定理的Haskell实现
identityUniquenessTheorem :: (Group g) => [g] -> Bool
identityUniquenessTheorem elements = 
  let identities = filter (\e -> all (\a -> e · a == a && a · e == a) elements) elements
  in length identities == 1

-- 形式化证明
identityUniquenessProof :: Proof
identityUniquenessProof = Apply IdentityUniqueness [
  Axiom (GroupAxiom "Identity"),
  Apply Contradiction [Axiom (IdentityAxiom "e1"), Axiom (IdentityAxiom "e2")]
]
```

#### 定理2：逆元唯一性

群中每个元素的逆元是唯一的。

**证明**：
```haskell
-- 逆元唯一性定理的Haskell实现
inverseUniquenessTheorem :: (Group g) => g -> Bool
inverseUniquenessTheorem a = 
  let inverses = filter (\a' -> a · a' == identity && a' · a == identity) getAllElements
  in length inverses == 1

-- 形式化证明
inverseUniquenessProof :: Proof
inverseUniquenessProof = Apply InverseUniqueness [
  Axiom (GroupAxiom "Inverse"),
  Apply Contradiction [Axiom (InverseAxiom "a1'"), Axiom (InverseAxiom "a2'")]
]
```

#### 定理3：拉格朗日定理

有限群的子群的阶数整除群的阶数。

**证明**：
```haskell
-- 拉格朗日定理的Haskell实现
lagrangeTheorem :: (Group g) => [g] -> [g] -> Bool
lagrangeTheorem group subgroup = 
  let groupOrder = length (nub group)
      subgroupOrder = length (nub subgroup)
  in groupOrder `mod` subgroupOrder == 0

-- 形式化证明
lagrangeProof :: Proof
lagrangeProof = Apply LagrangeTheorem [
  Axiom (FiniteGroupAxiom "G"),
  Axiom (SubgroupAxiom "H"),
  Apply CosetDecomposition [Axiom (GroupAxiom "G"), Axiom (SubgroupAxiom "H")]
]
```

## 应用示例

### 对称群

```haskell
-- 置换
data Permutation = Permutation {
  domain :: [Int],
  mapping :: [(Int, Int)]
} deriving (Show, Eq)

-- 置换组合
composePermutations :: Permutation -> Permutation -> Permutation
composePermutations p1 p2 = 
  let domain1 = domain p1
      domain2 = domain p2
      combinedDomain = nub (domain1 ++ domain2)
      combinedMapping = [(i, applyPermutation p1 (applyPermutation p2 i)) | i <- combinedDomain]
  in Permutation combinedDomain combinedMapping

applyPermutation :: Permutation -> Int -> Int
applyPermutation p i = 
  case lookup i (mapping p) of
    Just j -> j
    Nothing -> i

-- 对称群实例
instance Group Permutation where
  (·) = composePermutations
  identity = Permutation [] []
  inverse p = Permutation (domain p) (map swap (mapping p))
    where swap (a, b) = (b, a)

-- 生成置换
generatePermutation :: [Int] -> Permutation
generatePermutation cycle = 
  let n = length cycle
      mapping = zip cycle (tail cycle ++ [head cycle])
  in Permutation cycle mapping

-- 对称群S₃
symmetricGroupS3 :: FiniteGroup Permutation
symmetricGroupS3 = FiniteGroup {
  elements = [
    identity,  -- 单位置换
    generatePermutation [1, 2],  -- (1 2)
    generatePermutation [2, 3],  -- (2 3)
    generatePermutation [1, 3],  -- (1 3)
    generatePermutation [1, 2, 3],  -- (1 2 3)
    generatePermutation [1, 3, 2]   -- (1 3 2)
  ],
  operation = (·),
  unit = identity,
  inv = inverse
}
```

### 群论在密码学中的应用

```haskell
-- 离散对数问题
class (Group g) => DiscreteLogarithm g where
  discreteLog :: g -> g -> Maybe Integer
  babyStepGiantStep :: g -> g -> Maybe Integer
  
  babyStepGiantStep g h = 
    let m = ceiling (sqrt (fromIntegral (groupOrder g)))
        babySteps = [(h · (inverse g)^i, i) | i <- [0..m-1]]
        giantSteps = [(g^(m*j), j) | j <- [0..m-1]]
        matches = [(i, j) | (b, i) <- babySteps, (giant, j) <- giantSteps, b == giant]
    in case matches of
         ((i, j):_) -> Just (i + m * j)
         [] -> Nothing

-- Diffie-Hellman密钥交换
data DiffieHellman g = DiffieHellman {
  generator :: g,
  privateKey :: Integer,
  publicKey :: g
} deriving (Show)

generateKeyPair :: (Group g) => g -> Integer -> DiffieHellman g
generateKeyPair g private = 
  DiffieHellman g private (g^private)

computeSharedSecret :: (Group g) => DiffieHellman g -> g -> g
computeSharedSecret dh publicKey = 
  publicKey^(privateKey dh)

-- 椭圆曲线群
data EllipticCurve = EllipticCurve {
  a :: Integer,
  b :: Integer,
  p :: Integer
} deriving (Show, Eq)

data EllipticCurvePoint = 
    Point Integer Integer
  | PointAtInfinity
  deriving (Show, Eq)

instance Group EllipticCurvePoint where
  (·) = addEllipticCurvePoints
  identity = PointAtInfinity
  inverse PointAtInfinity = PointAtInfinity
  inverse (Point x y) = Point x (negate y)

addEllipticCurvePoints :: EllipticCurvePoint -> EllipticCurvePoint -> EllipticCurvePoint
addEllipticCurvePoints PointAtInfinity p = p
addEllipticCurvePoints p PointAtInfinity = p
addEllipticCurvePoints (Point x1 y1) (Point x2 y2) = 
  if x1 == x2 && y1 == negate y2
    then PointAtInfinity
    else 
      let lambda = if x1 == x2 
                   then ((3 * x1^2 + a) * modInverse (2 * y1) p) `mod` p
                   else ((y2 - y1) * modInverse (x2 - x1) p) `mod` p
          x3 = (lambda^2 - x1 - x2) `mod` p
          y3 = (lambda * (x1 - x3) - y1) `mod` p
      in Point x3 y3
```

## 形式化验证

### 群性质验证

```haskell
-- 群性质验证器
class GroupValidator g where
  validateGroup :: [g] -> GroupValidation
  findViolations :: [g] -> [String]
  
  validateGroup elements = GroupValidation {
    isGroup = isClosed elements && isAssociative elements && 
              hasIdentity elements && hasInverses elements,
    violations = findViolations elements,
    groupOrder = length (nub elements)
  }

data GroupValidation = GroupValidation {
  isGroup :: Bool,
  violations :: [String],
  groupOrder :: Int
} deriving (Show)

instance GroupValidator Integer where
  findViolations elements = 
    let violations = []
        violations' = if not (isClosed elements) 
                     then "Not closed under operation" : violations
                     else violations
        violations'' = if not (isAssociative elements)
                      then "Not associative" : violations'
                      else violations'
        violations''' = if not (hasIdentity elements)
                       then "No identity element" : violations''
                       else violations''
        violations'''' = if not (hasInverses elements)
                        then "Not all elements have inverses" : violations'''
                        else violations'''
    in violations''''

-- 群同构验证
class IsomorphismValidator g h where
  validateIsomorphism :: (g -> h) -> (h -> g) -> Bool
  checkBijectivity :: (g -> h) -> Bool
  
  validateIsomorphism f g = 
    isHomomorphism f && 
    isHomomorphism g && 
    checkBijectivity f &&
    checkBijectivity g
```

## 总结

群论为抽象代数提供了坚实的基础，通过Haskell的类型系统和函数式编程特性，我们可以实现严格的群论系统。这些实现不仅具有理论价值，也为密码学、物理学等应用领域提供了重要工具。

## 相关链接

- [代数结构主索引](../README.md)
- [环论](../02-Ring-Theory.md)
- [线性代数](../03-Linear-Algebra.md)
- [泛代数](../04-Universal-Algebra.md)
