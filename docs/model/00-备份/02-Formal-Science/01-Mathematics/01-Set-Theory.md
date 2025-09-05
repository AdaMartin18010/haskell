# 集合论基础 (Set Theory Basics)

## 概述

集合论是现代数学的基础，为所有数学分支提供统一的语言和工具。本文档从形式化的角度介绍集合论的基本概念、公理系统和重要定理，并提供相应的Haskell实现。

## 1. 基本概念

### 1.1 集合的定义

**定义 1.1.1 (集合)**
集合是不同对象的无序聚集，每个对象称为集合的元素。

```haskell
-- 集合的基本表示
data Set a = 
    EmptySet
    | Singleton a
    | Union (Set a) (Set a)
    | Intersection (Set a) (Set a)
    | Difference (Set a) (Set a)
    | PowerSet (Set a)
    | CartesianProduct (Set a) (Set b)
    deriving (Show, Eq)

-- 集合类型类
class SetOperations a where
    -- 空集
    empty :: Set a
    -- 单元素集
    singleton :: a -> Set a
    -- 并集
    union :: Set a -> Set a -> Set a
    -- 交集
    intersection :: Set a -> Set a -> Set a
    -- 差集
    difference :: Set a -> Set a -> Set a
    -- 幂集
    powerSet :: Set a -> Set (Set a)
    -- 笛卡尔积
    cartesianProduct :: Set a -> Set b -> Set (a, b)
    -- 包含关系
    isSubset :: Set a -> Set a -> Bool
    -- 属于关系
    isElement :: a -> Set a -> Bool
    -- 集合大小
    cardinality :: Set a -> Cardinality
```

### 1.2 集合运算

```haskell
-- 集合运算实现
instance (Eq a) => SetOperations a where
    empty = EmptySet
    
    singleton x = Singleton x
    
    union EmptySet s = s
    union s EmptySet = s
    union (Singleton x) (Singleton y) = 
        if x == y then Singleton x else Union (Singleton x) (Singleton y)
    union s1 s2 = Union s1 s2
    
    intersection EmptySet _ = EmptySet
    intersection _ EmptySet = EmptySet
    intersection (Singleton x) (Singleton y) = 
        if x == y then Singleton x else EmptySet
    intersection s1 s2 = Intersection s1 s2
    
    difference EmptySet _ = EmptySet
    difference s EmptySet = s
    difference (Singleton x) (Singleton y) = 
        if x == y then EmptySet else Singleton x
    difference s1 s2 = Difference s1 s2
    
    powerSet EmptySet = Singleton EmptySet
    powerSet (Singleton x) = Union (Singleton EmptySet) (Singleton (Singleton x))
    powerSet s = PowerSet s
    
    cartesianProduct s1 s2 = CartesianProduct s1 s2
    
    isSubset EmptySet _ = True
    isSubset _ EmptySet = False
    isSubset (Singleton x) s = isElement x s
    isSubset s1 s2 = all (\x -> isElement x s2) (elements s1)
    
    isElement x EmptySet = False
    isElement x (Singleton y) = x == y
    isElement x (Union s1 s2) = isElement x s1 || isElement x s2
    isElement x (Intersection s1 s2) = isElement x s1 && isElement x s2
    isElement x (Difference s1 s2) = isElement x s1 && not (isElement x s2)
    isElement x (PowerSet s) = isSubset (singleton x) s
    isElement (x, y) (CartesianProduct s1 s2) = isElement x s1 && isElement y s2
    
    cardinality EmptySet = Finite 0
    cardinality (Singleton _) = Finite 1
    cardinality s = Cardinality s

-- 基数
data Cardinality = 
    Finite Integer
    | CountablyInfinite
    | UncountablyInfinite
    deriving (Show, Eq)

-- 提取集合元素
elements :: Set a -> [a]
elements EmptySet = []
elements (Singleton x) = [x]
elements (Union s1 s2) = elements s1 ++ elements s2
elements (Intersection s1 s2) = filter (\x -> isElement x s2) (elements s1)
elements (Difference s1 s2) = filter (\x -> not (isElement x s2)) (elements s1)
elements (PowerSet s) = map listToSet (subsequences (elements s))
elements (CartesianProduct s1 s2) = 
    [(x, y) | x <- elements s1, y <- elements s2]

-- 辅助函数
listToSet :: [a] -> Set a
listToSet [] = EmptySet
listToSet (x:xs) = Union (Singleton x) (listToSet xs)
```

## 2. ZFC公理系统

### 2.1 基本公理

**公理 2.1.1 (外延公理)**
两个集合相等，当且仅当它们包含相同的元素。

```haskell
-- 外延公理
extensionality :: Set a -> Set a -> Bool
extensionality s1 s2 = 
    isSubset s1 s2 && isSubset s2 s1

-- 集合相等
instance (Eq a) => Eq (Set a) where
    (==) = extensionality
```

**公理 2.1.2 (空集公理)**
存在一个不包含任何元素的集合。

```haskell
-- 空集公理
emptySetAxiom :: Set a
emptySetAxiom = EmptySet

-- 空集性质
emptySetProperties :: Set a -> Bool
emptySetProperties s = 
    cardinality s == Finite 0 &&
    not (any (\x -> isElement x s) (elements s))
```

**公理 2.1.3 (配对公理)**
对于任意两个集合，存在一个包含它们的集合。

```haskell
-- 配对公理
pairingAxiom :: a -> a -> Set a
pairingAxiom x y = Union (Singleton x) (Singleton y)

-- 有序对
orderedPair :: a -> b -> Set (Either a b)
orderedPair x y = Union (Singleton (Left x)) (Singleton (Right y))
```

**公理 2.1.4 (并集公理)**
对于任意集合族，存在一个包含所有成员元素的集合。

```haskell
-- 并集公理
unionAxiom :: [Set a] -> Set a
unionAxiom [] = EmptySet
unionAxiom (s:ss) = Union s (unionAxiom ss)

-- 广义并集
generalizedUnion :: Set (Set a) -> Set a
generalizedUnion s = unionAxiom (elements s)
```

**公理 2.1.5 (幂集公理)**
对于任意集合，存在一个包含其所有子集的集合。

```haskell
-- 幂集公理
powerSetAxiom :: Set a -> Set (Set a)
powerSetAxiom s = PowerSet s

-- 幂集性质
powerSetProperties :: Set a -> Bool
powerSetProperties s = 
    all (\subset -> isSubset subset s) (elements (powerSetAxiom s))
```

### 2.2 高级公理

**公理 2.2.1 (无穷公理)**
存在一个包含自然数的集合。

```haskell
-- 无穷公理
infinityAxiom :: Set Integer
infinityAxiom = 
    let naturals = [0..]
        naturalSet = listToSet naturals
    in naturalSet

-- 自然数集合
data NaturalNumbers = 
    NaturalNumbers 
        { zero :: Integer
        , successor :: Integer -> Integer
        , induction :: (Integer -> Bool) -> Bool
        }

-- 皮亚诺公理
peanoAxioms :: NaturalNumbers -> Bool
peanoAxioms nats = 
    let zeroIsNatural = zero nats == 0
        successorIsInjective = 
            all (\x y -> successor nats x == successor nats y -> x == y) [0..]
        inductionPrinciple = 
            induction nats (\n -> n >= 0)
    in zeroIsNatural && successorIsInjective && inductionPrinciple
```

**公理 2.2.2 (替换公理)**
对于任意函数和集合，函数的值域是集合。

```haskell
-- 替换公理
replacementAxiom :: (a -> b) -> Set a -> Set b
replacementAxiom f s = 
    let image = map f (elements s)
    in listToSet image

-- 函数图像
image :: (a -> b) -> Set a -> Set b
image f s = replacementAxiom f s

-- 逆图像
preimage :: (a -> b) -> Set b -> Set a
preimage f s = 
    let allElements = elements s
        preimageElements = filter (\x -> f x `elem` allElements) (elements s)
    in listToSet preimageElements
```

**公理 2.2.3 (正则公理)**
每个非空集合都包含一个与自身不相交的元素。

```haskell
-- 正则公理
regularityAxiom :: Set a -> Bool
regularityAxiom EmptySet = True
regularityAxiom s = 
    let elementsOfS = elements s
        hasDisjointElement = any (\x -> 
            case x of
                Singleton y -> not (isElement y s)
                _ -> True
        ) elementsOfS
    in hasDisjointElement

-- 良基关系
wellFounded :: (a -> a -> Bool) -> Set a -> Bool
wellFounded relation s = 
    let allElements = elements s
        hasMinimalElement = any (\x -> 
            not (any (\y -> relation y x) allElements)
        ) allElements
    in hasMinimalElement
```

**公理 2.2.4 (选择公理)**
对于任意非空集合族，存在一个选择函数。

```haskell
-- 选择公理
choiceAxiom :: [Set a] -> Maybe (a -> a)
choiceAxiom [] = Nothing
choiceAxiom sets = 
    let nonEmptySets = filter (\s -> cardinality s /= Finite 0) sets
        choiceFunction = \s -> 
            case elements s of
                (x:_) -> x
                [] -> error "Empty set"
    in Just choiceFunction

-- 佐恩引理
zornsLemma :: (a -> a -> Bool) -> Set a -> Maybe a
zornsLemma order s = 
    let chains = findChains order s
        maximalChains = filter (isMaximalChain order) chains
    in case maximalChains of
        (chain:_) -> Just (last (elements chain))
        [] -> Nothing

-- 寻找链
findChains :: (a -> a -> Bool) -> Set a -> [Set a]
findChains order s = 
    let allElements = elements s
        chains = filter (isChain order) (elements (powerSetAxiom s))
    in chains

-- 检查是否为链
isChain :: (a -> a -> Bool) -> Set a -> Bool
isChain order s = 
    let elementsList = elements s
        allOrdered = all (\x y -> 
            x == y || order x y || order y x
        ) (pairs elementsList)
    in allOrdered

-- 生成元素对
pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = [(x, y) | y <- xs] ++ pairs xs
```

## 3. 序数理论

### 3.1 序数定义

**定义 3.1.1 (序数)**
序数是传递的、良序的集合。

```haskell
-- 序数
data Ordinal = 
    Zero
    | Successor Ordinal
    | Limit [Ordinal]
    deriving (Show, Eq)

-- 序数运算
class OrdinalOperations a where
    -- 后继
    successor :: a -> a
    -- 极限
    limit :: [a] -> a
    -- 序数加法
    ordinalAdd :: a -> a -> a
    -- 序数乘法
    ordinalMultiply :: a -> a -> a
    -- 序数幂
    ordinalPower :: a -> a -> a

-- 序数实例
instance OrdinalOperations Ordinal where
    successor o = Successor o
    
    limit os = Limit os
    
    ordinalAdd Zero o = o
    ordinalAdd (Successor o1) o2 = Successor (ordinalAdd o1 o2)
    ordinalAdd (Limit os) o2 = Limit (map (\o -> ordinalAdd o o2) os)
    
    ordinalMultiply Zero _ = Zero
    ordinalMultiply (Successor o1) o2 = 
        ordinalAdd (ordinalMultiply o1 o2) o2
    ordinalMultiply (Limit os) o2 = 
        Limit (map (\o -> ordinalMultiply o o2) os)
    
    ordinalPower _ Zero = Successor Zero
    ordinalPower o (Successor o1) = 
        ordinalMultiply (ordinalPower o o1) o
    ordinalPower o (Limit os) = 
        Limit (map (\o1 -> ordinalPower o o1) os)
```

### 3.2 基数理论

**定义 3.2.1 (基数)**
基数是序数的等势类。

```haskell
-- 基数
data Cardinal = 
    AlephZero
    | AlephSuccessor Cardinal
    | AlephLimit [Cardinal]
    deriving (Show, Eq)

-- 基数运算
class CardinalOperations a where
    -- 基数加法
    cardinalAdd :: a -> a -> a
    -- 基数乘法
    cardinalMultiply :: a -> a -> a
    -- 基数幂
    cardinalPower :: a -> a -> a

-- 基数实例
instance CardinalOperations Cardinal where
    cardinalAdd AlephZero AlephZero = AlephZero
    cardinalAdd c1 c2 = max c1 c2  -- 对于无限基数
    
    cardinalMultiply AlephZero _ = AlephZero
    cardinalMultiply _ AlephZero = AlephZero
    cardinalMultiply c1 c2 = max c1 c2  -- 对于无限基数
    
    cardinalPower AlephZero AlephZero = AlephSuccessor AlephZero
    cardinalPower c1 c2 = 
        if c1 == AlephZero && c2 /= AlephZero
        then AlephZero
        else AlephSuccessor (max c1 c2)
```

## 4. 集合论模型

### 4.1 冯·诺伊曼宇宙

```haskell
-- 冯·诺伊曼宇宙
data VonNeumannUniverse = 
    VonNeumannUniverse 
        { stages :: [Set Ordinal]
        , cumulative :: Bool
        , transitive :: Bool
        }

-- 构造冯·诺伊曼宇宙
constructVonNeumannUniverse :: VonNeumannUniverse
constructVonNeumannUniverse = 
    let v0 = EmptySet
        v1 = powerSetAxiom v0
        v2 = powerSetAxiom v1
        -- 递归构造
        vn = recursiveConstruction v0
    in VonNeumannUniverse 
        { stages = [v0, v1, v2, vn]
        , cumulative = True
        , transitive = True
        }

-- 递归构造
recursiveConstruction :: Set Ordinal -> Set Ordinal
recursiveConstruction s = 
    let successorStage = powerSetAxiom s
        limitStage = unionAxiom (map recursiveConstruction [s])
    in Union successorStage limitStage
```

### 4.2 哥德尔宇宙

```haskell
-- 哥德尔宇宙
data GodelUniverse = 
    GodelUniverse 
        { constructibleSets :: [Set Ordinal]
        , definability :: Bool
        , absoluteness :: Bool
        }

-- 构造哥德尔宇宙
constructGodelUniverse :: GodelUniverse
constructGodelUniverse = 
    let l0 = EmptySet
        l1 = definableSubsets l0
        l2 = definableSubsets l1
        -- 递归构造
        ln = recursiveDefinableConstruction l0
    in GodelUniverse 
        { constructibleSets = [l0, l1, l2, ln]
        , definability = True
        , absoluteness = True
        }

-- 可定义子集
definableSubsets :: Set Ordinal -> Set (Set Ordinal)
definableSubsets s = 
    let allSubsets = elements (powerSetAxiom s)
        definableOnes = filter isDefinable allSubsets
    in listToSet definableOnes

-- 可定义性检查
isDefinable :: Set Ordinal -> Bool
isDefinable s = 
    -- 简化的可定义性检查
    cardinality s /= UncountablyInfinite
```

## 5. 集合论定理

### 5.1 康托尔定理

**定理 5.1.1 (康托尔定理)**
对于任意集合 $A$，$A$ 的幂集的基数严格大于 $A$ 的基数。

```haskell
-- 康托尔定理
cantorTheorem :: Set a -> Bool
cantorTheorem s = 
    let cardA = cardinality s
        cardPA = cardinality (powerSetAxiom s)
        strictInequality = case (cardA, cardPA) of
            (Finite n, Finite m) -> m > n
            (Finite _, _) -> True
            (CountablyInfinite, UncountablyInfinite) -> True
            _ -> False
    in strictInequality

-- 对角线论证
diagonalArgument :: Set a -> Set a
diagonalArgument s = 
    let allSubsets = elements (powerSetAxiom s)
        diagonalSet = filter (\x -> not (isElement x (singleton x))) allSubsets
    in listToSet diagonalSet
```

### 5.2 策梅洛定理

**定理 5.2.1 (策梅洛定理)**
每个集合都可以良序化。

```haskell
-- 策梅洛定理
zermeloTheorem :: Set a -> Bool
zermeloTheorem s = 
    let canWellOrder = case cardinality s of
            Finite _ -> True
            CountablyInfinite -> True
            UncountablyInfinite -> True  -- 需要选择公理
    in canWellOrder

-- 良序化
wellOrder :: Set a -> Maybe (a -> a -> Bool)
wellOrder s = 
    case cardinality s of
        Finite n -> Just (\x y -> x < y)  -- 简化的良序
        _ -> choiceAxiom [s] >>= \f -> Just (\x y -> f x < f y)
```

## 6. 实际应用

### 6.1 数据库理论

```haskell
-- 关系数据库
data Relation a = 
    Relation 
        { attributes :: [String]
        , tuples :: Set a
        , constraints :: [Constraint]
        }

-- 关系运算
class RelationalAlgebra a where
    -- 选择
    select :: (a -> Bool) -> Relation a -> Relation a
    -- 投影
    project :: [String] -> Relation a -> Relation a
    -- 连接
    join :: Relation a -> Relation b -> Relation (a, b)
    -- 并集
    union :: Relation a -> Relation a -> Relation a
    -- 差集
    difference :: Relation a -> Relation a -> Relation a

-- 约束
data Constraint = 
    PrimaryKey [String]
    | ForeignKey String String
    | NotNull String
    | Unique [String]
    deriving (Show, Eq)
```

### 6.2 类型系统

```haskell
-- 类型系统
class TypeSystem a where
    -- 类型检查
    typeCheck :: a -> Type -> Bool
    -- 类型推导
    typeInference :: a -> Maybe Type
    -- 类型等价
    typeEquivalence :: Type -> Type -> Bool
    -- 子类型
    subtype :: Type -> Type -> Bool

-- 类型
data Type = 
    BaseType String
    | FunctionType Type Type
    | ProductType [Type]
    | SumType [Type]
    | UniversalType String Type
    | ExistentialType String Type
    deriving (Show, Eq)
```

## 7. 总结

集合论为现代数学提供了统一的基础：

1. **公理化方法**：ZFC公理系统提供了严格的数学基础
2. **序数理论**：为超限数学提供了工具
3. **基数理论**：为无限集合的研究提供了框架
4. **模型理论**：为集合论的不同解释提供了方法

集合论在计算机科学中有广泛应用，特别是在：

- 数据库理论
- 类型系统
- 形式化方法
- 算法分析

## 导航

- [返回形式科学层](../README.md)
- [数论基础](02-Number-Theory.md)
- [代数结构](03-Algebraic-Structures.md)
- [理论层](../../03-Theory/README.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
