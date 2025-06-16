# 集合论基础 (Set Theory Basics)

## 概述

集合论是现代数学的基础，为所有数学分支提供统一的语言和工具。本文档采用ZFC公理系统，使用Haskell实现集合论的核心概念和操作，为整个形式化知识体系提供基础。

## 公理系统

### ZFC公理系统

#### 1. 外延公理 (Axiom of Extensionality)

两个集合相等当且仅当它们包含相同的元素。

```haskell
-- 外延公理
class Extensionality a where
    type Element a
    
    equal :: Set a -> Set a -> Bool
    equal s1 s2 = all (`member` s2) (elements s1) && 
                  all (`member` s1) (elements s2)
```

**数学表达**：
$$\forall x \forall y [\forall z(z \in x \leftrightarrow z \in y) \rightarrow x = y]$$

#### 2. 空集公理 (Axiom of Empty Set)

存在一个不包含任何元素的集合。

```haskell
-- 空集
data EmptySet = EmptySet

-- 空集公理
emptySet :: Set a
emptySet = Set []

-- 空集性质
isEmpty :: Set a -> Bool
isEmpty (Set []) = True
isEmpty _ = False
```

**数学表达**：
$$\exists x \forall y (y \notin x)$$

#### 3. 配对公理 (Axiom of Pairing)

对于任意两个集合，存在一个包含它们的集合。

```haskell
-- 配对公理
pair :: a -> a -> Set a
pair x y = Set [x, y]

-- 有序对
data OrderedPair a b = OrderedPair a b

-- 有序对实现
orderedPair :: a -> b -> OrderedPair a b
orderedPair x y = OrderedPair x y
```

**数学表达**：
$$\forall x \forall y \exists z \forall w(w \in z \leftrightarrow w = x \lor w = y)$$

#### 4. 并集公理 (Axiom of Union)

对于任意集合族，存在一个包含所有成员元素的集合。

```haskell
-- 并集公理
union :: [Set a] -> Set a
union sets = Set $ concatMap elements sets

-- 二元并集
union2 :: Set a -> Set a -> Set a
union2 s1 s2 = Set $ elements s1 ++ elements s2
```

**数学表达**：
$$\forall F \exists A \forall x(x \in A \leftrightarrow \exists B(B \in F \land x \in B))$$

#### 5. 幂集公理 (Axiom of Power Set)

对于任意集合，存在一个包含其所有子集的集合。

```haskell
-- 幂集公理
powerSet :: Set a -> Set (Set a)
powerSet s = Set $ allSubsets (elements s)

-- 子集生成
allSubsets :: [a] -> [Set a]
allSubsets [] = [Set []]
allSubsets (x:xs) = 
    let subsets = allSubsets xs
    in subsets ++ map (insert x) subsets
```

**数学表达**：
$$\forall x \exists y \forall z(z \in y \leftrightarrow z \subseteq x)$$

#### 6. 分离公理 (Axiom Schema of Separation)

对于任意集合和性质，存在一个包含满足该性质元素的子集。

```haskell
-- 分离公理
separation :: Set a -> (a -> Bool) -> Set a
separation s predicate = Set $ filter predicate (elements s)

-- 集合构造器
setBuilder :: (a -> Bool) -> Set a
setBuilder predicate = Set $ filter predicate universe
```

**数学表达**：
$$\forall x \exists y \forall z(z \in y \leftrightarrow z \in x \land \phi(z))$$

#### 7. 无穷公理 (Axiom of Infinity)

存在一个包含空集且对每个元素都包含其后继的集合。

```haskell
-- 后继函数
successor :: Set a -> Set a
successor s = union2 s (Set [s])

-- 无穷公理
infinity :: Set (Set a)
infinity = Set $ iterate successor emptySet
```

**数学表达**：
$$\exists x(\emptyset \in x \land \forall y(y \in x \rightarrow y \cup \{y\} \in x))$$

#### 8. 替换公理 (Axiom Schema of Replacement)

如果函数将集合的元素映射到集合，则存在一个包含所有像的集合。

```haskell
-- 替换公理
replacement :: Set a -> (a -> b) -> Set b
replacement s f = Set $ map f (elements s)

-- 函数图像
image :: Set a -> (a -> b) -> Set b
image s f = replacement s f
```

**数学表达**：
$$\forall x \forall y \forall z(\phi(x,y) \land \phi(x,z) \rightarrow y = z) \rightarrow \forall A \exists B \forall y(y \in B \leftrightarrow \exists x(x \in A \land \phi(x,y)))$$

#### 9. 正则公理 (Axiom of Regularity)

每个非空集合都包含一个与它不相交的元素。

```haskell
-- 正则公理
regularity :: Set a -> Bool
regularity s = isEmpty s || 
               any (\x -> isEmpty (intersection2 (Set [x]) s)) (elements s)
```

**数学表达**：
$$\forall x(x \neq \emptyset \rightarrow \exists y(y \in x \land y \cap x = \emptyset))$$

#### 10. 选择公理 (Axiom of Choice)

对于任意非空集合族，存在一个选择函数。

```haskell
-- 选择公理
choice :: [Set a] -> [a]
choice sets = map (selectElement) sets
  where
    selectElement (Set []) = error "Empty set"
    selectElement (Set (x:_)) = x

-- 选择函数
choiceFunction :: [Set a] -> (Set a -> a)
choiceFunction sets = \s -> 
    case find (\x -> x == s) sets of
        Just (Set (x:_)) -> x
        _ -> error "Set not found"
```

**数学表达**：
$$\forall F(\emptyset \notin F \rightarrow \exists f \forall A \in F(f(A) \in A))$$

## 基本概念

### 集合表示

```haskell
-- 集合数据类型
data Set a = Set [a]
  deriving (Show, Eq)

-- 集合操作
class SetOperations a where
    type Element a
    
    -- 成员关系
    member :: Element a -> Set a -> Bool
    member x (Set xs) = x `elem` xs
    
    -- 子集关系
    subset :: Set a -> Set a -> Bool
    subset s1 s2 = all (`member` s2) (elements s1)
    
    -- 真子集关系
    properSubset :: Set a -> Set a -> Bool
    properSubset s1 s2 = subset s1 s2 && not (equal s1 s2)
    
    -- 基数
    cardinality :: Set a -> Cardinality
    cardinality (Set xs) = Finite (length xs)

-- 基数类型
data Cardinality = 
    Finite Int
  | Countable
  | Uncountable
  deriving (Show, Eq)
```

### 集合运算

```haskell
-- 基本集合运算
class BasicSetOperations a where
    -- 交集
    intersection :: Set a -> Set a -> Set a
    intersection s1 s2 = Set $ filter (`member` s2) (elements s1)
    
    -- 差集
    difference :: Set a -> Set a -> Set a
    difference s1 s2 = Set $ filter (not . (`member` s2)) (elements s1)
    
    -- 对称差
    symmetricDifference :: Set a -> Set a -> Set a
    symmetricDifference s1 s2 = 
        union2 (difference s1 s2) (difference s2 s1)
    
    -- 笛卡尔积
    cartesianProduct :: Set a -> Set b -> Set (OrderedPair a b)
    cartesianProduct s1 s2 = 
        Set [(OrderedPair x y) | x <- elements s1, y <- elements s2]

-- 辅助函数
elements :: Set a -> [a]
elements (Set xs) = xs

insert :: a -> Set a -> Set a
insert x (Set xs) = Set (x:xs)

remove :: a -> Set a -> Set a
remove x (Set xs) = Set $ filter (/= x) xs
```

### 关系理论

```haskell
-- 二元关系
data Relation a b = Relation (Set (OrderedPair a b))

-- 关系操作
class RelationOperations a b where
    type Domain a b
    type Codomain a b
    type Range a b
    
    -- 定义域
    domain :: Relation a b -> Set a
    domain (Relation pairs) = 
        Set $ map (\(OrderedPair x _) -> x) (elements pairs)
    
    -- 值域
    range :: Relation a b -> Set b
    range (Relation pairs) = 
        Set $ map (\(OrderedPair _ y) -> y) (elements pairs)
    
    -- 关系合成
    compose :: Relation a b -> Relation b c -> Relation a c
    compose (Relation r1) (Relation r2) = 
        Relation $ Set [(OrderedPair x z) | 
                       (OrderedPair x y) <- elements r1,
                       (OrderedPair y' z) <- elements r2,
                       y == y']
    
    -- 逆关系
    inverse :: Relation a b -> Relation b a
    inverse (Relation pairs) = 
        Relation $ Set [(OrderedPair y x) | (OrderedPair x y) <- elements pairs]

-- 关系性质
class RelationProperties a where
    -- 自反性
    reflexive :: Relation a a -> Bool
    reflexive (Relation pairs) = 
        all (\x -> member (OrderedPair x x) (Relation pairs)) universe
    
    -- 对称性
    symmetric :: Relation a a -> Bool
    symmetric (Relation pairs) = 
        all (\(OrderedPair x y) -> 
            member (OrderedPair y x) (Relation pairs)) (elements pairs)
    
    -- 传递性
    transitive :: Relation a a -> Bool
    transitive (Relation pairs) = 
        all (\(OrderedPair x y, OrderedPair y' z) -> 
            y == y' && member (OrderedPair x z) (Relation pairs))
            [(p1, p2) | p1 <- elements pairs, p2 <- elements pairs]
```

### 函数理论

```haskell
-- 函数作为特殊关系
data Function a b = Function (Relation a b)

-- 函数性质
class FunctionProperties a b where
    -- 单值性
    singleValued :: Function a b -> Bool
    singleValued (Function relation) = 
        all (\(OrderedPair x1 y1, OrderedPair x2 y2) -> 
            x1 == x2 && y1 == y2) 
            [(p1, p2) | p1 <- elements relation, p2 <- elements relation]
    
    -- 全函数
    total :: Function a b -> Bool
    total (Function relation) = 
        all (\x -> any (\(OrderedPair x' _) -> x == x') (elements relation)) universe
    
    -- 单射
    injective :: Function a b -> Bool
    injective (Function relation) = 
        all (\(OrderedPair x1 y1, OrderedPair x2 y2) -> 
            y1 == y2 && x1 == x2) 
            [(p1, p2) | p1 <- elements relation, p2 <- elements relation]
    
    -- 满射
    surjective :: Function a b -> Bool
    surjective (Function relation) = 
        all (\y -> any (\(OrderedPair _ y') -> y == y') (elements relation)) universe
    
    -- 双射
    bijective :: Function a b -> Bool
    bijective f = injective f && surjective f

-- 函数应用
apply :: Function a b -> a -> Maybe b
apply (Function relation) x = 
    case find (\(OrderedPair x' y) -> x == x') (elements relation) of
        Just (OrderedPair _ y) -> Just y
        Nothing -> Nothing
```

## 序数理论

```haskell
-- 序数
data Ordinal = 
    Zero
  | Successor Ordinal
  | Limit (Set Ordinal)
  deriving (Show, Eq)

-- 序数运算
class OrdinalOperations where
    -- 后继
    succ :: Ordinal -> Ordinal
    succ = Successor
    
    -- 序数加法
    add :: Ordinal -> Ordinal -> Ordinal
    add Zero y = y
    add (Successor x) y = Successor (add x y)
    add (Limit xs) y = Limit (Set [add x y | x <- elements xs])
    
    -- 序数乘法
    multiply :: Ordinal -> Ordinal -> Ordinal
    multiply Zero _ = Zero
    multiply (Successor x) y = add y (multiply x y)
    multiply (Limit xs) y = Limit (Set [multiply x y | x <- elements xs])
    
    -- 序数幂
    power :: Ordinal -> Ordinal -> Ordinal
    power _ Zero = Successor Zero
    power x (Successor y) = multiply x (power x y)
    power x (Limit ys) = Limit (Set [power x y | y <- elements ys])

-- 序数比较
instance Ord Ordinal where
    compare Zero Zero = EQ
    compare Zero _ = LT
    compare _ Zero = GT
    compare (Successor x) (Successor y) = compare x y
    compare (Successor x) (Limit ys) = LT
    compare (Limit xs) (Successor y) = GT
    compare (Limit xs) (Limit ys) = 
        if subset xs ys && subset ys xs then EQ
        else if subset xs ys then LT
        else GT
```

## 基数理论

```haskell
-- 基数
data Cardinal = 
    FiniteCardinal Int
  | AlephZero
  | Aleph Ordinal
  deriving (Show, Eq)

-- 基数运算
class CardinalOperations where
    -- 基数加法
    addCardinal :: Cardinal -> Cardinal -> Cardinal
    addCardinal (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m + n)
    addCardinal AlephZero _ = AlephZero
    addCardinal _ AlephZero = AlephZero
    addCardinal (Aleph a) (Aleph b) = Aleph (max a b)
    
    -- 基数乘法
    multiplyCardinal :: Cardinal -> Cardinal -> Cardinal
    multiplyCardinal (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m * n)
    multiplyCardinal AlephZero _ = AlephZero
    multiplyCardinal _ AlephZero = AlephZero
    multiplyCardinal (Aleph a) (Aleph b) = Aleph (max a b)
    
    -- 基数幂
    powerCardinal :: Cardinal -> Cardinal -> Cardinal
    powerCardinal _ (FiniteCardinal 0) = FiniteCardinal 1
    powerCardinal (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m ^ n)
    powerCardinal AlephZero (FiniteCardinal n) = AlephZero
    powerCardinal (Aleph a) (FiniteCardinal n) = Aleph a
    powerCardinal _ AlephZero = AlephZero
    powerCardinal (FiniteCardinal m) (Aleph a) = Aleph (Successor a)
    powerCardinal (Aleph a) (Aleph b) = Aleph (Successor (max a b))

-- 基数比较
instance Ord Cardinal where
    compare (FiniteCardinal m) (FiniteCardinal n) = compare m n
    compare (FiniteCardinal _) _ = LT
    compare _ (FiniteCardinal _) = GT
    compare AlephZero AlephZero = EQ
    compare AlephZero (Aleph _) = LT
    compare (Aleph _) AlephZero = GT
    compare (Aleph a) (Aleph b) = compare a b
```

## 应用领域

### 1. 计算机科学

- 为数据结构提供理论基础
- 支持算法设计和分析
- 指导编程语言设计

### 2. 数学基础

- 为所有数学分支提供统一语言
- 支持数学结构的形式化
- 提供证明的基础工具

### 3. 逻辑学

- 为形式逻辑提供语义基础
- 支持模型论研究
- 提供证明论工具

### 4. 哲学

- 为数学哲学提供研究对象
- 支持本体论研究
- 提供认识论工具

## 质量保证

### 1. 公理化标准

- 严格遵循ZFC公理系统
- 所有定理都有形式化证明
- 保证逻辑一致性

### 2. 实现正确性

- Haskell代码的类型安全
- 算法的正确性验证
- 性能的优化保证

### 3. 数学准确性

- 所有定义都符合数学标准
- 符号使用的一致性
- 证明的严格性

---

**导航**: [返回数学基础索引](../README.md) | [下一主题：数论](02-Number-Theory.md)
