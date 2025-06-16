# 集合论基础 (Set Theory Basics)

## 概述

集合论是现代数学的基础，为所有数学分支提供统一的语言和工具。本文档建立严格的集合论公理系统，并提供完整的Haskell实现。

## 公理系统

### 1. 外延公理 (Axiom of Extensionality)

**公理**：两个集合相等当且仅当它们包含相同的元素。

$$\forall x \forall y [\forall z(z \in x \leftrightarrow z \in y) \rightarrow x = y]$$

**Haskell实现**：

```haskell
-- 外延公理
class Extensionality a where
    type Element a
    
    -- 集合相等性
    equal :: a -> a -> Bool
    
    -- 元素包含关系
    member :: Element a -> a -> Bool
    
    -- 外延性公理
    extensionality :: a -> a -> Bool
    extensionality x y = 
        all (\z -> member z x == member z y) allElements
        where allElements = getAllElements x y

-- 集合的基本结构
data Set a = 
    Empty
    | Singleton a
    | Union (Set a) (Set a)
    | Intersection (Set a) (Set a)
    | Complement (Set a)
    | PowerSet (Set a)
    | Comprehension (a -> Bool) (Set a)

-- 集合相等性
instance Eq a => Eq (Set a) where
    Empty == Empty = True
    Singleton x == Singleton y = x == y
    Union a b == Union c d = a == c && b == d
    _ == _ = False

-- 元素包含关系
member :: Eq a => a -> Set a -> Bool
member _ Empty = False
member x (Singleton y) = x == y
member x (Union a b) = member x a || member x b
member x (Intersection a b) = member x a && member x b
member x (Complement a) = not (member x a)
```

### 2. 空集公理 (Axiom of Empty Set)

**公理**：存在一个不包含任何元素的集合。

$$\exists x \forall y (y \notin x)$$

**Haskell实现**：

```haskell
-- 空集公理
class EmptySet a where
    -- 空集
    empty :: a
    
    -- 空集性质
    isEmpty :: a -> Bool
    
    -- 空集唯一性
    emptyUniqueness :: a -> a -> Bool

-- 空集实现
emptySet :: Set a
emptySet = Empty

-- 空集检查
isEmpty :: Set a -> Bool
isEmpty Empty = True
isEmpty _ = False

-- 空集唯一性证明
emptyUniqueness :: Set a -> Set a -> Bool
emptyUniqueness x y = 
    isEmpty x && isEmpty y ==> equal x y
    where (==>) = (&&)
```

### 3. 配对公理 (Axiom of Pairing)

**公理**：对于任意两个集合，存在一个包含它们的集合。

$$\forall x \forall y \exists z \forall w(w \in z \leftrightarrow w = x \lor w = y)$$

**Haskell实现**：

```haskell
-- 配对公理
class Pairing a where
    type Pair a
    
    -- 配对操作
    pair :: a -> a -> Pair a
    
    -- 配对性质
    pairProperty :: a -> a -> Pair a -> Bool

-- 配对实现
pair :: a -> a -> Set a
pair x y = Union (Singleton x) (Singleton y)

-- 配对性质验证
pairProperty :: Eq a => a -> a -> Set a -> Bool
pairProperty x y z = 
    member x z && member y z && 
    all (\w -> member w z == (w == x || w == y)) allElements
    where allElements = [x, y]
```

### 4. 并集公理 (Axiom of Union)

**公理**：对于任意集合族，存在一个包含所有成员集合中元素的集合。

$$\forall F \exists A \forall x(x \in A \leftrightarrow \exists B(B \in F \land x \in B))$$

**Haskell实现**：

```haskell
-- 并集公理
class UnionAxiom a where
    -- 并集操作
    union :: [a] -> a
    
    -- 并集性质
    unionProperty :: [a] -> a -> Bool

-- 并集实现
union :: [Set a] -> Set a
union [] = Empty
union [x] = x
union (x:xs) = Union x (union xs)

-- 并集性质验证
unionProperty :: Eq a => [Set a] -> Set a -> Bool
unionProperty sets result = 
    all (\x -> any (\s -> member x s) sets == member x result) allElements
    where allElements = concatMap getElements sets
          getElements Empty = []
          getElements (Singleton x) = [x]
          getElements (Union a b) = getElements a ++ getElements b
          getElements _ = []
```

### 5. 幂集公理 (Axiom of Power Set)

**公理**：对于任意集合，存在一个包含其所有子集的集合。

$$\forall x \exists y \forall z(z \in y \leftrightarrow z \subseteq x)$$

**Haskell实现**：

```haskell
-- 幂集公理
class PowerSetAxiom a where
    -- 幂集操作
    powerSet :: a -> Set a
    
    -- 幂集性质
    powerSetProperty :: a -> Set a -> Bool

-- 幂集实现
powerSet :: Set a -> Set (Set a)
powerSet Empty = Singleton Empty
powerSet (Singleton x) = Union (Singleton Empty) (Singleton (Singleton x))
powerSet (Union a b) = 
    let pa = powerSet a
        pb = powerSet b
    in Union pa pb

-- 幂集性质验证
powerSetProperty :: Eq a => Set a -> Set (Set a) -> Bool
powerSetProperty original result = 
    all (\subset -> isSubset subset original) (getElements result) &&
    all (\subset -> member subset result) (allSubsets original)
    where 
        isSubset Empty _ = True
        isSubset (Singleton x) s = member x s
        isSubset (Union a b) s = isSubset a s && isSubset b s
        isSubset _ _ = False
        
        allSubsets Empty = [Empty]
        allSubsets (Singleton x) = [Empty, Singleton x]
        allSubsets (Union a b) = 
            let sa = allSubsets a
                sb = allSubsets b
            in sa ++ sb ++ [Union s1 s2 | s1 <- sa, s2 <- sb]
```

## 集合运算

### 1. 基本运算

```haskell
-- 集合基本运算
class SetOperations a where
    -- 并集
    union :: a -> a -> a
    
    -- 交集
    intersection :: a -> a -> a
    
    -- 差集
    difference :: a -> a -> a
    
    -- 对称差
    symmetricDifference :: a -> a -> a
    
    -- 补集
    complement :: a -> a

-- 集合运算实现
union :: Set a -> Set a -> Set a
union = Union

intersection :: Set a -> Set a -> Set a
intersection = Intersection

difference :: Eq a => Set a -> Set a -> Set a
difference a b = Comprehension (\x -> member x a && not (member x b)) a

symmetricDifference :: Eq a => Set a -> Set a -> Set a
symmetricDifference a b = Union (difference a b) (difference b a)

complement :: Set a -> Set a
complement = Complement
```

### 2. 集合关系

```haskell
-- 集合关系
class SetRelations a where
    -- 包含关系
    subset :: a -> a -> Bool
    
    -- 真包含关系
    properSubset :: a -> a -> Bool
    
    -- 相等关系
    equal :: a -> a -> Bool
    
    -- 不相交
    disjoint :: a -> a -> Bool

-- 集合关系实现
subset :: Eq a => Set a -> Set a -> Bool
subset Empty _ = True
subset (Singleton x) s = member x s
subset (Union a b) s = subset a s && subset b s
subset (Intersection a b) s = subset a s && subset b s
subset _ _ = False

properSubset :: Eq a => Set a -> Set a -> Bool
properSubset a b = subset a b && not (equal a b)

equal :: Eq a => Set a -> Set a -> Bool
equal a b = subset a b && subset b a

disjoint :: Eq a => Set a -> Set a -> Bool
disjoint a b = isEmpty (intersection a b)
```

## 序数理论

### 1. 序数定义

```haskell
-- 序数理论
data Ordinal = 
    Zero
    | Successor Ordinal
    | Limit [Ordinal]

-- 序数运算
class OrdinalOperations where
    -- 后继
    successor :: Ordinal -> Ordinal
    
    -- 加法
    add :: Ordinal -> Ordinal -> Ordinal
    
    -- 乘法
    multiply :: Ordinal -> Ordinal -> Ordinal
    
    -- 幂运算
    power :: Ordinal -> Ordinal -> Ordinal

-- 序数实现
successor :: Ordinal -> Ordinal
successor = Successor

add :: Ordinal -> Ordinal -> Ordinal
add Zero y = y
add (Successor x) y = Successor (add x y)
add (Limit xs) y = Limit (map (\x -> add x y) xs)

multiply :: Ordinal -> Ordinal -> Ordinal
multiply Zero _ = Zero
multiply (Successor x) y = add (multiply x y) y
multiply (Limit xs) y = Limit (map (\x -> multiply x y) xs)

power :: Ordinal -> Ordinal -> Ordinal
power _ Zero = Successor Zero
power x (Successor y) = multiply (power x y) x
power x (Limit ys) = Limit (map (\y -> power x y) ys)
```

### 2. 基数理论

```haskell
-- 基数理论
data Cardinal = 
    FiniteCardinal Natural
    | Aleph Ordinal

-- 基数运算
class CardinalOperations where
    -- 基数加法
    cardinalAdd :: Cardinal -> Cardinal -> Cardinal
    
    -- 基数乘法
    cardinalMultiply :: Cardinal -> Cardinal -> Cardinal
    
    -- 基数幂运算
    cardinalPower :: Cardinal -> Cardinal -> Cardinal

-- 基数实现
cardinalAdd :: Cardinal -> Cardinal -> Cardinal
cardinalAdd (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m + n)
cardinalAdd (Aleph a) (Aleph b) = Aleph (max a b)
cardinalAdd _ _ = error "Mixed finite and infinite cardinals"

cardinalMultiply :: Cardinal -> Cardinal -> Cardinal
cardinalMultiply (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m * n)
cardinalMultiply (Aleph a) (Aleph b) = Aleph (max a b)
cardinalMultiply _ _ = error "Mixed finite and infinite cardinals"

cardinalPower :: Cardinal -> Cardinal -> Cardinal
cardinalPower (FiniteCardinal m) (FiniteCardinal n) = FiniteCardinal (m ^ n)
cardinalPower (Aleph a) (FiniteCardinal n) = Aleph a
cardinalPower (Aleph a) (Aleph b) = Aleph (successor (max a b))
cardinalPower _ _ = error "Invalid cardinal power operation"
```

## 选择公理

### 1. 选择公理陈述

**公理**：对于任意非空集合族，存在一个选择函数。

$$\forall F[\emptyset \notin F \rightarrow \exists f \forall A \in F(f(A) \in A)]$$

**Haskell实现**：

```haskell
-- 选择公理
class AxiomOfChoice a where
    type ChoiceFunction a
    
    -- 选择函数
    choiceFunction :: [a] -> ChoiceFunction a
    
    -- 选择公理验证
    choiceAxiom :: [a] -> ChoiceFunction a -> Bool

-- 选择函数实现
choiceFunction :: [Set a] -> a -> a
choiceFunction sets defaultElement = 
    \set -> if member defaultElement set 
            then defaultElement 
            else head (getElements set)
    where getElements Empty = [defaultElement]
          getElements (Singleton x) = [x]
          getElements (Union a b) = getElements a ++ getElements b
          getElements _ = [defaultElement]

-- 选择公理验证
choiceAxiom :: Eq a => [Set a] -> (Set a -> a) -> Bool
choiceAxiom sets choice = 
    all (\set -> not (isEmpty set) && member (choice set) set) sets
```

### 2. 选择公理的等价形式

```haskell
-- 佐恩引理
data ZornLemma = 
    ZornLemma 
        { poset :: Set a
        , chain :: Set a -> Bool
        , upperBound :: Set a -> a
        , maximalElement :: a
        }

-- 良序定理
data WellOrderingTheorem = 
    WellOrderingTheorem 
        { set :: Set a
        , ordering :: a -> a -> Ordering
        , wellOrdered :: Bool
        }

-- 乘积非空
data ProductNonEmpty = 
    ProductNonEmpty 
        { family :: [Set a]
        , product :: Set [a]
        , nonEmpty :: Bool
        }
```

## 集合论的应用

### 1. 关系理论

```haskell
-- 关系理论
data Relation a b = 
    Relation 
        { domain :: Set a
        , codomain :: Set b
        , pairs :: Set (a, b)
        }

-- 关系运算
class RelationOperations a b where
    -- 关系合成
    compose :: Relation a b -> Relation b c -> Relation a c
    
    -- 关系逆
    inverse :: Relation a b -> Relation b a
    
    -- 关系限制
    restrict :: Relation a b -> Set a -> Relation a b

-- 关系实现
compose :: Relation a b -> Relation b c -> Relation a c
compose (Relation dom1 cod1 pairs1) (Relation dom2 cod2 pairs2) = 
    Relation dom1 cod2 composedPairs
    where composedPairs = Comprehension isComposable allPairs
          allPairs = cartesianProduct (getElements dom1) (getElements cod2)
          isComposable (x, z) = 
              any (\(y1, y2) -> member (x, y1) pairs1 && member (y2, z) pairs2) 
                  (getElements cod1)

inverse :: Relation a b -> Relation b a
inverse (Relation dom cod pairs) = 
    Relation cod dom (Comprehension (\(y, x) -> member (x, y) pairs) 
                                    (cartesianProduct cod dom))
```

### 2. 函数理论

```haskell
-- 函数理论
data Function a b = 
    Function 
        { domain :: Set a
        , codomain :: Set b
        , mapping :: a -> b
        , functional :: Bool
        }

-- 函数性质
class FunctionProperties a b where
    -- 单射
    injective :: Function a b -> Bool
    
    -- 满射
    surjective :: Function a b -> Bool
    
    -- 双射
    bijective :: Function a b -> Bool
    
    -- 可逆
    invertible :: Function a b -> Bool

-- 函数性质实现
injective :: Eq b => Function a b -> Bool
injective (Function dom cod mapping _) = 
    all (\x -> all (\y -> x == y || mapping x /= mapping y) (getElements dom)) 
        (getElements dom)

surjective :: Eq b => Function a b -> Bool
surjective (Function dom cod mapping _) = 
    all (\y -> any (\x -> mapping x == y) (getElements dom)) 
        (getElements cod)

bijective :: Eq b => Function a b -> Bool
bijective f = injective f && surjective f

invertible :: Eq b => Function a b -> Bool
invertible = bijective
```

## 与类型论的关系

集合论为类型论提供基础：

```haskell
-- 集合到类型的映射
class SetToType a where
    type SetType a
    
    -- 集合到类型的转换
    setToType :: Set a -> SetType a
    
    -- 类型到集合的转换
    typeToSet :: SetType a -> Set a

-- 集合论在类型论中的应用
data TypeSet = 
    TypeSet 
        { elements :: Set Type
        , operations :: Set (Type -> Type)
        , relations :: Set (Type -> Type -> Bool)
        }
```

## 导航

- [返回数学基础](../README.md)
- [数论基础](02-Number-Theory.md)
- [代数结构](03-Algebraic-Structures.md)
- [形式逻辑](../../02-Formal-Logic/README.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
