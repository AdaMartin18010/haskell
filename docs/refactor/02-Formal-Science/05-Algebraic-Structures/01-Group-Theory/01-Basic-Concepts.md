# 群论基础概念

## 概述

群论是抽象代数的核心分支，研究具有二元运算的代数结构。本文档从形式化角度分析群的基本概念、性质和分类。

## 形式化定义

### 群的基本结构

群是一个四元组：

$$G = (S, \circ, e, \cdot^{-1})$$

其中：
- $S$ 是集合
- $\circ: S \times S \rightarrow S$ 是二元运算
- $e \in S$ 是单位元
- $\cdot^{-1}: S \rightarrow S$ 是逆元函数

### 群的公理

群必须满足以下公理：

1. **结合律**：$(a \circ b) \circ c = a \circ (b \circ c)$
2. **单位元**：$e \circ a = a \circ e = a$
3. **逆元**：$a \circ a^{-1} = a^{-1} \circ a = e$

### 群的阶

群的阶定义为：

$$|G| = |S|$$

## Haskell实现

```haskell
-- 群
data Group a = Group
  { elements :: Set a
  , operation :: a -> a -> a
  , identity :: a
  , inverse :: a -> a
  }

-- 群构建器
mkGroup :: Set a -> (a -> a -> a) -> a -> (a -> a) -> Group a
mkGroup elems op id inv = Group elems op id inv

-- 群公理验证
validateGroup :: (Eq a, Show a) => Group a -> Bool
validateGroup group = 
  let associativity = checkAssociativity group
      identity = checkIdentity group
      inverse = checkInverse group
  in associativity && identity && inverse

-- 结合律检查
checkAssociativity :: (Eq a, Show a) => Group a -> Bool
checkAssociativity group = 
  let elements = Set.toList $ elements group
      op = operation group
      triples = [(a, b, c) | a <- elements, b <- elements, c <- elements]
  in all (\(a, b, c) -> op (op a b) c == op a (op b c)) triples

-- 单位元检查
checkIdentity :: (Eq a, Show a) => Group a -> Bool
checkIdentity group = 
  let elements = Set.toList $ elements group
      op = operation group
      id = identity group
  in all (\a -> op id a == a && op a id == a) elements

-- 逆元检查
checkInverse :: (Eq a, Show a) => Group a -> Bool
checkInverse group = 
  let elements = Set.toList $ elements group
      op = operation group
      inv = inverse group
      id = identity group
  in all (\a -> op a (inv a) == id && op (inv a) a == id) elements

-- 群运算
groupOperation :: Group a -> a -> a -> a
groupOperation group = operation group

-- 群逆元
groupInverse :: Group a -> a -> a
groupInverse group = inverse group

-- 群单位元
groupIdentity :: Group a -> a
groupIdentity group = identity group
```

## 群的基本性质

### 1. 单位元唯一性

```haskell
-- 单位元唯一性定理
identityUniqueness :: (Eq a, Show a) => Group a -> Bool
identityUniqueness group = 
  let elements = Set.toList $ elements group
      op = operation group
      id = identity group
      otherIds = filter (\e -> all (\a -> op e a == a && op a e == a) elements) elements
  in length otherIds == 1 && head otherIds == id

-- 单位元唯一性证明
proveIdentityUniqueness :: (Eq a, Show a) => Group a -> Proof
proveIdentityUniqueness group = 
  let id1 = identity group
      id2 = findOtherIdentity group
      op = operation group
      proof = 
        [ "假设存在两个单位元 e1 和 e2"
        , "e1 = e1 ∘ e2 (e2是单位元)"
        , "e1 ∘ e2 = e2 (e1是单位元)"
        , "因此 e1 = e2"
        ]
  in Proof "单位元唯一性" proof
```

### 2. 逆元唯一性

```haskell
-- 逆元唯一性定理
inverseUniqueness :: (Eq a, Show a) => Group a -> Bool
inverseUniqueness group = 
  let elements = Set.toList $ elements group
      op = operation group
      inv = inverse group
      id = identity group
  in all (\a -> 
    let invA = inv a
        otherInvs = filter (\b -> op a b == id && op b a == id) elements
    in length otherInvs == 1 && head otherInvs == invA) elements

-- 逆元唯一性证明
proveInverseUniqueness :: (Eq a, Show a) => Group a -> Proof
proveInverseUniqueness group = 
  let proof = 
        [ "假设元素 a 有两个逆元 b 和 c"
        , "b = b ∘ e = b ∘ (a ∘ c) = (b ∘ a) ∘ c = e ∘ c = c"
        , "因此 b = c"
        ]
  in Proof "逆元唯一性" proof
```

### 3. 消去律

```haskell
-- 消去律
cancellationLaw :: (Eq a, Show a) => Group a -> Bool
cancellationLaw group = 
  let elements = Set.toList $ elements group
      op = operation group
      triples = [(a, b, c) | a <- elements, b <- elements, c <- elements]
      leftCancellation = all (\(a, b, c) -> 
        if op a b == op a c then b == c else True) triples
      rightCancellation = all (\(a, b, c) -> 
        if op b a == op c a then b == c else True) triples
  in leftCancellation && rightCancellation

-- 消去律证明
proveCancellationLaw :: (Eq a, Show a) => Group a -> Proof
proveCancellationLaw group = 
  let proof = 
        [ "假设 a ∘ b = a ∘ c"
        , "a⁻¹ ∘ (a ∘ b) = a⁻¹ ∘ (a ∘ c)"
        , "(a⁻¹ ∘ a) ∘ b = (a⁻¹ ∘ a) ∘ c"
        , "e ∘ b = e ∘ c"
        , "b = c"
        ]
  in Proof "消去律" proof
```

## 群的分类

### 1. 有限群与无限群

```haskell
-- 有限群
data FiniteGroup a = FiniteGroup
  { group :: Group a
  , order :: Integer
  }

-- 无限群
data InfiniteGroup a = InfiniteGroup
  { group :: Group a
  , cardinality :: Cardinality
  }

-- 群阶
groupOrder :: Group a -> Integer
groupOrder group = 
  let elements = elements group
  in fromIntegral $ Set.size elements

-- 有限群检查
isFiniteGroup :: Group a -> Bool
isFiniteGroup group = 
  let order = groupOrder group
  in order > 0 && order < maxBound

-- 无限群检查
isInfiniteGroup :: Group a -> Bool
isInfiniteGroup group = 
  not $ isFiniteGroup group
```

### 2. 交换群与非交换群

```haskell
-- 交换群
data AbelianGroup a = AbelianGroup
  { group :: Group a
  , commutativity :: Bool
  }

-- 交换性检查
isAbelian :: (Eq a, Show a) => Group a -> Bool
isAbelian group = 
  let elements = Set.toList $ elements group
      op = operation group
      pairs = [(a, b) | a <- elements, b <- elements]
  in all (\(a, b) -> op a b == op b a) pairs

-- 交换群构建器
mkAbelianGroup :: (Eq a, Show a) => Group a -> Maybe (AbelianGroup a)
mkAbelianGroup group = 
  if isAbelian group
  then Just $ AbelianGroup group True
  else Nothing

-- 非交换群
data NonAbelianGroup a = NonAbelianGroup
  { group :: Group a
  , commutativity :: Bool
  }

-- 非交换群构建器
mkNonAbelianGroup :: (Eq a, Show a) => Group a -> Maybe (NonAbelianGroup a)
mkNonAbelianGroup group = 
  if not $ isAbelian group
  then Just $ NonAbelianGroup group False
  else Nothing
```

### 3. 循环群

```haskell
-- 循环群
data CyclicGroup a = CyclicGroup
  { group :: Group a
  , generator :: a
  , cyclic :: Bool
  }

-- 生成元检查
isGenerator :: (Eq a, Show a) => Group a -> a -> Bool
isGenerator group g = 
  let elements = Set.toList $ elements group
      op = operation group
      id = identity group
      generated = generateSubgroup group g
  in Set.fromList generated == elements group

-- 生成子群
generateSubgroup :: (Eq a, Show a) => Group a -> a -> [a]
generateSubgroup group g = 
  let op = operation group
      id = identity group
      inv = inverse group
      powers = iterate (\x -> op x g) g
      negativePowers = iterate (\x -> op x (inv g)) (inv g)
  in id : takeWhile (/= id) powers ++ takeWhile (/= id) negativePowers

-- 循环群检查
isCyclic :: (Eq a, Show a) => Group a -> Bool
isCyclic group = 
  let elements = Set.toList $ elements group
  in any (\g -> isGenerator group g) elements

-- 循环群构建器
mkCyclicGroup :: (Eq a, Show a) => Group a -> Maybe (CyclicGroup a)
mkCyclicGroup group = 
  let generators = filter (\g -> isGenerator group g) (Set.toList $ elements group)
  in case generators of
       (g:_) -> Just $ CyclicGroup group g True
       [] -> Nothing
```

## 群的运算

### 1. 群幂

```haskell
-- 群幂
groupPower :: (Eq a, Show a) => Group a -> a -> Integer -> a
groupPower group a n = 
  let op = operation group
      id = identity group
      inv = inverse group
  in if n == 0
     then id
     else if n > 0
          then iterate (\x -> op x a) a !! (fromIntegral n - 1)
          else iterate (\x -> op x (inv a)) (inv a) !! (fromIntegral (-n) - 1)

-- 元素阶
elementOrder :: (Eq a, Show a) => Group a -> a -> Integer
elementOrder group a = 
  let id = identity group
      powers = iterate (\x -> groupPower group a 1) a
      order = findIndex (== id) powers
  in case order of
       Just n -> fromIntegral n
       Nothing -> 0  -- 无限阶
```

### 2. 子群

```haskell
-- 子群
data Subgroup a = Subgroup
  { parent :: Group a
  , elements :: Set a
  , subgroup :: Group a
  }

-- 子群检查
isSubgroup :: (Eq a, Show a) => Group a -> Set a -> Bool
isSubgroup parent elems = 
  let parentOp = operation parent
      parentId = identity parent
      parentInv = inverse parent
      subgroup = Group elems parentOp parentId parentInv
  in Set.isSubsetOf elems (elements parent) && validateGroup subgroup

-- 子群构建器
mkSubgroup :: (Eq a, Show a) => Group a -> Set a -> Maybe (Subgroup a)
mkSubgroup parent elems = 
  if isSubgroup parent elems
  then let parentOp = operation parent
           parentId = identity parent
           parentInv = inverse parent
           subgroup = Group elems parentOp parentId parentInv
       in Just $ Subgroup parent elems subgroup
  else Nothing

-- 平凡子群
trivialSubgroup :: Group a -> Subgroup a
trivialSubgroup group = 
  let id = identity group
      elems = Set.singleton id
      op = operation group
      inv = inverse group
      subgroup = Group elems op id inv
  in Subgroup group elems subgroup
```

## 形式化证明

### 群的基本定理

**定理**: 在群中，单位元是唯一的。

**证明**:
设 $e_1$ 和 $e_2$ 是群 $G$ 的两个单位元。

1. 由于 $e_1$ 是单位元：$e_1 \circ e_2 = e_2$
2. 由于 $e_2$ 是单位元：$e_1 \circ e_2 = e_1$
3. 因此：$e_1 = e_2$

**定理**: 在群中，每个元素的逆元是唯一的。

**证明**:
设 $a$ 是群 $G$ 的元素，$b$ 和 $c$ 是 $a$ 的两个逆元。

1. $b = b \circ e = b \circ (a \circ c) = (b \circ a) \circ c = e \circ c = c$
2. 因此：$b = c$

### 拉格朗日定理

**定理**: 有限群的子群的阶整除群的阶。

**证明**:
设 $H$ 是有限群 $G$ 的子群。

1. 定义 $G$ 上的等价关系：$a \sim b$ 当且仅当 $a^{-1}b \in H$
2. 每个等价类的元素个数等于 $|H|$
3. $G$ 被分解为不相交的等价类的并
4. 因此：$|G| = k|H|$，其中 $k$ 是等价类的个数

## 总结

群论通过形式化方法建立了代数结构的基础理论，为抽象代数和数学的其他分支提供了重要工具。通过Haskell的实现，我们可以构建可靠的群论系统，支持复杂的代数计算和证明。

## 相关链接

- [代数结构基础](../01-Basic-Concepts.md)
- [环论](../02-Ring-Theory/01-Basic-Concepts.md)
- [域论](../03-Field-Theory/01-Basic-Concepts.md) 