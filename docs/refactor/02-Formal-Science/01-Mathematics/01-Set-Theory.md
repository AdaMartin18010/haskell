# 01-Set-Theory (集合论基础)

## 概述

集合论是现代数学的基础，为所有数学分支提供统一的语言和工具。在形式化知识体系中，集合论为类型系统、逻辑推理和数学结构提供理论基础。

## 基本概念

### 1. 集合 (Set)

**定义**: 集合是不同对象的无序聚集。

**形式化表达**:
```latex
A = \{x \mid P(x)\}
```

**Haskell实现**:
```haskell
-- 集合的基本表示
data Set a = 
    EmptySet
    | Singleton a
    | Union (Set a) (Set a)
    | Intersection (Set a) (Set a)
    | Difference (Set a) (Set a)
    | Comprehension (a -> Bool)

-- 集合类
class SetOperations a where
    type Element a
    
    -- 基本操作
    empty :: a
    singleton :: Element a -> a
    union :: a -> a -> a
    intersection :: a -> a -> a
    difference :: a -> a -> a
    
    -- 关系操作
    isSubset :: a -> a -> Bool
    isElement :: Element a -> a -> Bool
    isEmpty :: a -> Bool
    cardinality :: a -> Int
```

### 2. 集合运算

**并集**: $A \cup B = \{x \mid x \in A \lor x \in B\}$

**交集**: $A \cap B = \{x \mid x \in A \land x \in B\}$

**差集**: $A \setminus B = \{x \mid x \in A \land x \notin B\}$

**Haskell实现**:
```haskell
-- 集合运算实现
instance (Eq a) => SetOperations (Set a) where
    type Element (Set a) = a
    
    empty = EmptySet
    
    singleton x = Singleton x
    
    union EmptySet s = s
    union s EmptySet = s
    union (Singleton x) s = 
        if isElement x s then s else Union (Singleton x) s
    union (Union s1 s2) s3 = Union s1 (union s2 s3)
    union s1 s2 = Union s1 s2
    
    intersection EmptySet _ = EmptySet
    intersection _ EmptySet = EmptySet
    intersection (Singleton x) s = 
        if isElement x s then Singleton x else EmptySet
    intersection (Union s1 s2) s3 = 
        union (intersection s1 s3) (intersection s2 s3)
    intersection s1 s2 = Intersection s1 s2
    
    difference EmptySet _ = EmptySet
    difference s EmptySet = s
    difference (Singleton x) s = 
        if isElement x s then EmptySet else Singleton x
    difference (Union s1 s2) s3 = 
        union (difference s1 s3) (difference s2 s3)
    difference s1 s2 = Difference s1 s2
    
    isSubset EmptySet _ = True
    isSubset _ EmptySet = False
    isSubset (Singleton x) s = isElement x s
    isSubset (Union s1 s2) s3 = 
        isSubset s1 s3 && isSubset s2 s3
    isSubset s1 s2 = all (\x -> isElement x s2) (toList s1)
    
    isElement x EmptySet = False
    isElement x (Singleton y) = x == y
    isElement x (Union s1 s2) = isElement x s1 || isElement x s2
    isElement x (Intersection s1 s2) = isElement x s1 && isElement x s2
    isElement x (Difference s1 s2) = isElement x s1 && not (isElement x s2)
    isElement x (Comprehension p) = p x
    
    isEmpty EmptySet = True
    isEmpty (Singleton _) = False
    isEmpty (Union s1 s2) = isEmpty s1 && isEmpty s2
    isEmpty (Intersection s1 s2) = isEmpty s1 || isEmpty s2
    isEmpty (Difference s1 s2) = isSubset s1 s2
    isEmpty (Comprehension p) = False  -- 假设非空
    
    cardinality EmptySet = 0
    cardinality (Singleton _) = 1
    cardinality (Union s1 s2) = 
        cardinality s1 + cardinality s2 - cardinality (intersection s1 s2)
    cardinality (Intersection s1 s2) = 
        cardinality s1 + cardinality s2 - cardinality (union s1 s2)
    cardinality (Difference s1 s2) = 
        cardinality s1 - cardinality (intersection s1 s2)
    cardinality (Comprehension _) = -1  -- 无限集
```

### 3. 集合关系

**包含关系**: $A \subseteq B \equiv \forall x (x \in A \rightarrow x \in B)$

**相等关系**: $A = B \equiv A \subseteq B \land B \subseteq A$

**真包含关系**: $A \subset B \equiv A \subseteq B \land A \neq B$

**Haskell实现**:
```haskell
-- 集合关系
instance (Eq a) => Eq (Set a) where
    s1 == s2 = isSubset s1 s2 && isSubset s2 s1

-- 真包含关系
isProperSubset :: (Eq a) => Set a -> Set a -> Bool
isProperSubset s1 s2 = isSubset s1 s2 && s1 /= s2

-- 集合相等性证明
proveSetEquality :: (Eq a) => Set a -> Set a -> Proof
proveSetEquality s1 s2 = 
    if s1 == s2 
    then Proof "Sets are equal by extensionality"
    else Proof "Sets are not equal"
```

## 集合论公理

### 1. 外延公理 (Axiom of Extensionality)

**公理**: 两个集合相等当且仅当它们包含相同的元素。

**形式化表达**:
```latex
\forall A \forall B [\forall x (x \in A \leftrightarrow x \in B) \rightarrow A = B]
```

**Haskell实现**:
```haskell
-- 外延公理
extensionalityAxiom :: (Eq a) => Set a -> Set a -> Bool
extensionalityAxiom s1 s2 = 
    (s1 == s2) == (all (\x -> isElement x s1 == isElement x s2) allElements)
  where
    allElements = union s1 s2
```

### 2. 空集公理 (Axiom of Empty Set)

**公理**: 存在一个不包含任何元素的集合。

**形式化表达**:
```latex
\exists A \forall x (x \notin A)
```

**Haskell实现**:
```haskell
-- 空集公理
emptySetAxiom :: Bool
emptySetAxiom = isEmpty empty

-- 空集唯一性
emptySetUniqueness :: (Eq a) => Set a -> Bool
emptySetUniqueness s = isEmpty s == (s == empty)
```

### 3. 配对公理 (Axiom of Pairing)

**公理**: 对于任意两个集合，存在一个包含它们的集合。

**形式化表达**:
```latex
\forall A \forall B \exists C \forall x (x \in C \leftrightarrow x = A \lor x = B)
```

**Haskell实现**:
```haskell
-- 配对公理
pairingAxiom :: a -> a -> Set a
pairingAxiom x y = union (singleton x) (singleton y)

-- 配对公理验证
verifyPairingAxiom :: (Eq a) => a -> a -> Bool
verifyPairingAxiom x y = 
    isElement x (pairingAxiom x y) && isElement y (pairingAxiom x y)
```

### 4. 并集公理 (Axiom of Union)

**公理**: 对于任意集合族，存在一个包含所有成员集合元素的集合。

**形式化表达**:
```latex
\forall F \exists A \forall x (x \in A \leftrightarrow \exists B (B \in F \land x \in B))
```

**Haskell实现**:
```haskell
-- 并集公理
unionAxiom :: [Set a] -> Set a
unionAxiom [] = empty
unionAxiom (s:ss) = union s (unionAxiom ss)

-- 并集公理验证
verifyUnionAxiom :: (Eq a) => [Set a] -> Bool
verifyUnionAxiom sets = 
    all (\s -> all (\x -> isElement x (unionAxiom sets)) (toList s)) sets
```

## 集合论定理

### 1. 德摩根定律 (De Morgan's Laws)

**定理**: 
- $(A \cup B)^c = A^c \cap B^c$
- $(A \cap B)^c = A^c \cup B^c$

**Haskell实现**:
```haskell
-- 补集操作
complement :: (Eq a) => Set a -> Set a -> Set a
complement universe s = difference universe s

-- 德摩根定律验证
deMorganLaws :: (Eq a) => Set a -> Set a -> Set a -> Bool
deMorganLaws universe a b = 
    let aComp = complement universe a
        bComp = complement universe b
        unionComp = complement universe (union a b)
        intersectionComp = complement universe (intersection a b)
    in unionComp == intersection aComp bComp &&
       intersectionComp == union aComp bComp
```

### 2. 分配律 (Distributive Laws)

**定理**:
- $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$
- $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$

**Haskell实现**:
```haskell
-- 分配律验证
distributiveLaws :: (Eq a) => Set a -> Set a -> Set a -> Bool
distributiveLaws a b c = 
    let left1 = intersection a (union b c)
        right1 = union (intersection a b) (intersection a c)
        left2 = union a (intersection b c)
        right2 = intersection (union a b) (union a c)
    in left1 == right1 && left2 == right2
```

### 3. 幂集定理 (Power Set Theorem)

**定理**: 对于任意集合A，存在一个包含A的所有子集的集合。

**形式化表达**:
```latex
\forall A \exists P \forall B (B \in P \leftrightarrow B \subseteq A)
```

**Haskell实现**:
```haskell
-- 幂集
powerSet :: (Eq a) => Set a -> Set (Set a)
powerSet EmptySet = Singleton EmptySet
powerSet (Singleton x) = 
    Union (Singleton EmptySet) (Singleton (Singleton x))
powerSet (Union s1 s2) = 
    let ps1 = powerSet s1
        ps2 = powerSet s2
    in union ps1 ps2
powerSet s = Comprehension (\subset -> isSubset subset s)

-- 幂集基数定理
powerSetCardinality :: (Eq a) => Set a -> Bool
powerSetCardinality s = 
    cardinality (powerSet s) == 2 ^ cardinality s
```

## 集合论应用

### 1. 关系理论

```haskell
-- 二元关系
type Relation a b = Set (a, b)

-- 关系操作
domain :: (Eq a, Eq b) => Relation a b -> Set a
domain rel = Comprehension (\x -> any (\(a, _) -> a == x) (toList rel))

range :: (Eq a, Eq b) => Relation a b -> Set b
range rel = Comprehension (\y -> any (\(_, b) -> b == y) (toList rel))

-- 关系合成
compose :: (Eq a, Eq b, Eq c) => Relation b c -> Relation a b -> Relation a c
compose r2 r1 = Comprehension (\(a, c) -> 
    any (\(_, b) -> any (\(b', _) -> b == b' && isElement (b, c) r2) (toList r1)) 
    (toList r1))
```

### 2. 函数理论

```haskell
-- 函数作为特殊关系
type Function a b = Relation a b

-- 函数性质
isFunction :: (Eq a, Eq b) => Function a b -> Bool
isFunction f = 
    let dom = domain f
        pairs = toList f
    in all (\x -> length [y | (a, y) <- pairs, a == x] == 1) (toList dom)

-- 函数应用
apply :: (Eq a, Eq b) => Function a b -> a -> Maybe b
apply f x = 
    let pairs = toList f
        matches = [y | (a, y) <- pairs, a == x]
    in case matches of
        [y] -> Just y
        _ -> Nothing
```

### 3. 基数理论

```haskell
-- 基数
data Cardinality = 
    Finite Int
    | Countable
    | Uncountable

-- 基数比较
compareCardinality :: Set a -> Set b -> Ordering
compareCardinality s1 s2 = 
    compare (cardinality s1) (cardinality s2)

-- 等势关系
isEquinumerous :: (Eq a, Eq b) => Set a -> Set b -> Bool
isEquinumerous s1 s2 = 
    cardinality s1 == cardinality s2
```

## 形式化证明

### 1. 集合相等性证明

```haskell
-- 集合相等性证明系统
data SetEqualityProof a = 
    ExtensionalityProof (Set a) (Set a)
    | TransitivityProof (Set a) (Set a) (Set a)
    | SymmetryProof (Set a) (Set a)

-- 证明验证
verifySetEqualityProof :: (Eq a) => SetEqualityProof a -> Bool
verifySetEqualityProof (ExtensionalityProof s1 s2) = s1 == s2
verifySetEqualityProof (TransitivityProof s1 s2 s3) = 
    s1 == s2 && s2 == s3 && s1 == s3
verifySetEqualityProof (SymmetryProof s1 s2) = 
    s1 == s2 && s2 == s1
```

### 2. 集合运算证明

```haskell
-- 集合运算证明
proveSetOperation :: (Eq a) => Set a -> Set a -> SetOperation -> Proof
proveSetOperation s1 s2 op = 
    case op of
        UnionOp -> Proof $ "Union: " ++ show (union s1 s2)
        IntersectionOp -> Proof $ "Intersection: " ++ show (intersection s1 s2)
        DifferenceOp -> Proof $ "Difference: " ++ show (difference s1 s2)

data SetOperation = UnionOp | IntersectionOp | DifferenceOp
```

## 总结

集合论为整个形式化知识体系提供了基础的语言和工具。通过严格的数学定义和Haskell实现，我们将抽象的集合概念转化为可计算、可验证的形式化系统。这种形式化表达不仅保持了数学概念的严格性，还增加了可操作性和可验证性。

---

**导航**: [返回数学基础](../README.md) | [下一节: 数论基础](../02-Number-Theory.md)  
**最后更新**: 2024年12月  
**版本**: 1.0.0 