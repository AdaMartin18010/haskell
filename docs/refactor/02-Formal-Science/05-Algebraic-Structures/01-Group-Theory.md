# 群论 (Group Theory)

## 概述

群论是研究代数结构的基础理论，群是具有一个二元运算的集合，满足封闭性、结合律、单位元存在性和逆元存在性。群论在计算机科学、密码学、量子计算等领域有广泛应用。

## 形式化定义

### 群的基本定义

```haskell
-- 群的基本结构
data Group a = Group
  { carrier :: Set a
  , operation :: BinaryOperation a
  , identity :: a
  , inverse :: a -> a
  } deriving (Show, Eq)

-- 二元运算
type BinaryOperation a = a -> a -> a

-- 群的性质验证
class GroupProperties a where
  closure :: Group a -> a -> a -> Bool
  associativity :: Group a -> a -> a -> a -> Bool
  identityElement :: Group a -> a -> Bool
  inverseElement :: Group a -> a -> Bool

-- 群公理验证
groupAxioms :: (Eq a, GroupProperties a) => Group a -> Bool
groupAxioms group = 
  let elements = setToList (carrier group)
      op = operation group
      e = identity group
      inv = inverse group
  in all (\x -> all (\y -> closure group x y) elements) elements &&
     all (\x -> all (\y -> all (\z -> associativity group x y z) elements) elements) elements &&
     all (\x -> identityElement group x) elements &&
     all (\x -> inverseElement group x) elements

-- 具体实现
instance GroupProperties Integer where
  closure group x y = 
    let result = operation group x y
    in result `elem` setToList (carrier group)
  
  associativity group x y z = 
    let op = operation group
        left = op (op x y) z
        right = op x (op y z)
    in left == right
  
  identityElement group x = 
    let e = identity group
        op = operation group
    in op e x == x && op x e == x
  
  inverseElement group x = 
    let inv = inverse group
        op = operation group
        e = identity group
        invX = inv x
    in op x invX == e && op invX x == e
```

### 子群

```haskell
-- 子群定义
data Subgroup a = Subgroup
  { parentGroup :: Group a
  , subset :: Set a
  } deriving (Show, Eq)

-- 子群验证
isSubgroup :: (Eq a, GroupProperties a) => Group a -> Set a -> Bool
isSubgroup group subset = 
  let elements = setToList subset
      op = operation group
      e = identity group
      inv = inverse group
  in e `elem` elements &&
     all (\x -> all (\y -> op x y `elem` elements) elements) elements &&
     all (\x -> inv x `elem` elements) elements

-- 子群生成
generateSubgroup :: (Eq a, GroupProperties a) => Group a -> [a] -> Subgroup a
generateSubgroup group generators = 
  let closure = generateClosure group generators
  in Subgroup group closure

-- 子群闭包
generateClosure :: (Eq a, GroupProperties a) => Group a -> [a] -> Set a
generateClosure group generators = 
  let e = identity group
      op = operation group
      inv = inverse group
      initial = Set.fromList (e : generators)
      closure = iterate (addProducts op) initial
      stable = findStable closure
  in stable

addProducts :: BinaryOperation a -> Set a -> Set a
addProducts op set = 
  let elements = Set.toList set
      products = [op x y | x <- elements, y <- elements]
  in Set.union set (Set.fromList products)
```

### 同态和同构

```haskell
-- 群同态
data GroupHomomorphism a b = GroupHomomorphism
  { domain :: Group a
  , codomain :: Group b
  , mapping :: a -> b
  } deriving (Show, Eq)

-- 同态验证
isHomomorphism :: (Eq a, Eq b, GroupProperties a, GroupProperties b) 
                => GroupHomomorphism a b -> Bool
isHomomorphism hom = 
  let f = mapping hom
      domainOp = operation (domain hom)
      codomainOp = operation (codomain hom)
      domainElements = setToList (carrier (domain hom))
  in all (\x -> all (\y -> 
         f (domainOp x y) == codomainOp (f x) (f y)) domainElements) domainElements

-- 群同构
data GroupIsomorphism a b = GroupIsomorphism
  { homomorphism :: GroupHomomorphism a b
  , inverseMapping :: b -> a
  } deriving (Show, Eq)

-- 同构验证
isIsomorphism :: (Eq a, Eq b, GroupProperties a, GroupProperties b) 
               => GroupIsomorphism a b -> Bool
isIsomorphism iso = 
  let hom = homomorphism iso
      f = mapping hom
      g = inverseMapping iso
      domainElements = setToList (carrier (domain hom))
      codomainElements = setToList (carrier (codomain hom))
  in isHomomorphism hom &&
     all (\x -> g (f x) == x) domainElements &&
     all (\y -> f (g y) == y) codomainElements
```

## 形式化证明

### 拉格朗日定理

**定理**: 有限群的子群的阶整除群的阶。

```haskell
-- 群阶
groupOrder :: Group a -> Int
groupOrder group = Set.size (carrier group)

-- 子群阶
subgroupOrder :: Subgroup a -> Int
subgroupOrder subgroup = Set.size (subset subgroup)

-- 拉格朗日定理
lagrangeTheorem :: (Eq a, GroupProperties a) => Group a -> Subgroup a -> Bool
lagrangeTheorem group subgroup = 
  let groupSize = groupOrder group
      subgroupSize = subgroupOrder subgroup
  in groupSize `mod` subgroupSize == 0

-- 证明：通过陪集分解
lagrangeProof :: (Eq a, GroupProperties a) => Group a -> Subgroup a -> Proof
lagrangeProof group subgroup = 
  let cosets = leftCosets group subgroup
      cosetSizes = map Set.size cosets
      totalSize = sum cosetSizes
      groupSize = groupOrder group
  in proveEquality totalSize groupSize
```

### 西罗定理

**定理**: 有限群的p-西罗子群存在且共轭。

```haskell
-- p-西罗子群
data SylowSubgroup a = SylowSubgroup
  { group :: Group a
  , prime :: Int
  , subgroup :: Subgroup a
  } deriving (Show, Eq)

-- p-西罗子群验证
isSylowSubgroup :: (Eq a, GroupProperties a) => Group a -> Subgroup a -> Int -> Bool
isSylowSubgroup group subgroup p = 
  let subgroupSize = subgroupOrder subgroup
      groupSize = groupOrder group
      maxPower = maximumPower p groupSize
  in subgroupSize == p ^ maxPower

-- 最大幂次
maximumPower :: Int -> Int -> Int
maximumPower p n = 
  let powers = [k | k <- [0..], p^k <= n, n `mod` (p^k) == 0]
  in maximum powers

-- 西罗定理
sylowTheorem :: (Eq a, GroupProperties a) => Group a -> Int -> Bool
sylowTheorem group p = 
  let sylowSubgroups = findSylowSubgroups group p
      conjugates = findConjugates group sylowSubgroups
  in not (null sylowSubgroups) && allConjugate conjugates
```

## 实际应用

### 对称群

```haskell
-- 置换
data Permutation = Permutation
  { domain :: [Int]
  , mapping :: [(Int, Int)]
  } deriving (Show, Eq)

-- 置换组合
composePermutations :: Permutation -> Permutation -> Permutation
composePermutations p1 p2 = 
  let domain1 = domain p1
      domain2 = domain p2
      mapping1 = mapping p1
      mapping2 = mapping p2
      composed = [(x, applyPermutation p1 (applyPermutation p2 x)) | x <- domain1]
  in Permutation domain1 composed

-- 应用置换
applyPermutation :: Permutation -> Int -> Int
applyPermutation perm x = 
  case lookup x (mapping perm) of
    Just y -> y
    Nothing -> x

-- 对称群
symmetricGroup :: Int -> Group Permutation
symmetricGroup n = 
  let elements = generatePermutations n
      operation = composePermutations
      identity = identityPermutation n
      inverse = inversePermutation
  in Group (Set.fromList elements) operation identity inverse

-- 生成置换
generatePermutations :: Int -> [Permutation]
generatePermutations n = 
  let domain = [1..n]
      allMappings = generateAllMappings domain
  in [Permutation domain mapping | mapping <- allMappings]
```

### 循环群

```haskell
-- 循环群
data CyclicGroup = CyclicGroup
  { generator :: Int
  , order :: Int
  } deriving (Show, Eq)

-- 循环群运算
cyclicOperation :: CyclicGroup -> Int -> Int -> Int
cyclicOperation group x y = (x + y) `mod` order group

-- 循环群逆元
cyclicInverse :: CyclicGroup -> Int -> Int
cyclicInverse group x = (order group - x) `mod` order group

-- 循环群结构
cyclicGroupStructure :: CyclicGroup -> Group Int
cyclicGroupStructure cyclic = 
  let elements = [0..order cyclic - 1]
      op = cyclicOperation cyclic
      e = 0
      inv = cyclicInverse cyclic
  in Group (Set.fromList elements) op e inv

-- 循环群同构
cyclicGroupIsomorphism :: CyclicGroup -> CyclicGroup -> Bool
cyclicGroupIsomorphism g1 g2 = 
  let order1 = order g1
      order2 = order g2
  in order1 == order2
```

## 总结

群论通过严格的代数结构为数学和计算机科学提供了强大的工具。通过Haskell的类型系统和函数式编程特性，我们可以构建可验证的群论系统，确保群的性质和定理的正确性。
