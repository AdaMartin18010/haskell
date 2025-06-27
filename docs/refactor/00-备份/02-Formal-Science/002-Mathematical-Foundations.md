# 数学基础理论 (Mathematical Foundations)

## 📚 概述

数学基础理论为形式科学提供严格的数学基础，包括集合论、逻辑学、代数结构等核心概念。本文档建立数学基础的完整理论体系，并提供 Haskell 实现。

## 🎯 核心概念

### 1. 集合论基础

#### 1.1 集合定义

**定义 1.1.1** 集合是对象的无序聚集：

$$A = \{x \mid P(x)\}$$

其中 $P(x)$ 是谓词。

**公理 1.1.1** 外延公理：两个集合相等当且仅当它们包含相同的元素。

**公理 1.1.2** 空集公理：存在空集 $\emptyset$。

```haskell
-- 集合类型
type Set a = Data.Set.Set a

-- 集合操作
emptySet :: Set a
emptySet = Data.Set.empty

singletonSet :: a -> Set a
singletonSet = Data.Set.singleton

setUnion :: (Ord a) => Set a -> Set a -> Set a
setUnion = Data.Set.union

setIntersection :: (Ord a) => Set a -> Set a -> Set a
setIntersection = Data.Set.intersection

setDifference :: (Ord a) => Set a -> Set a -> Set a
setDifference = Data.Set.difference

setSubset :: (Ord a) => Set a -> Set a -> Bool
setSubset = Data.Set.isSubsetOf

setMember :: (Ord a) => a -> Set a -> Bool
setMember = Data.Set.member

-- 集合构造
setComprehension :: (Ord a) => (a -> Bool) -> [a] -> Set a
setComprehension pred xs = fromList [x | x <- xs, pred x]

-- 幂集
powerSet :: (Ord a) => Set a -> Set (Set a)
powerSet s = fromList [fromList subset | subset <- subsequences (toList s)]

-- 笛卡尔积
cartesianProduct :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
cartesianProduct xs ys = fromList [(x, y) | x <- toList xs, y <- toList ys]
```

#### 1.2 关系理论

**定义 1.2.1** 关系是集合的笛卡尔积的子集：

$$R \subseteq A \times B$$

**定义 1.2.2** 等价关系满足：

1. 自反性：$\forall x, xRx$
2. 对称性：$\forall x, y, xRy \Rightarrow yRx$
3. 传递性：$\forall x, y, z, xRy \land yRz \Rightarrow xRz$

```haskell
-- 关系类型
type Relation a = Set (a, a)

-- 关系操作
emptyRelation :: Relation a
emptyRelation = empty

identityRelation :: (Ord a) => Set a -> Relation a
identityRelation s = fromList [(x, x) | x <- toList s]

relationComposition :: (Ord a) => Relation a -> Relation a -> Relation a
relationComposition r1 r2 = 
  fromList [(x, z) | (x, y) <- toList r1, (y', z) <- toList r2, y == y']

-- 等价关系检查
isEquivalenceRelation :: (Ord a) => Relation a -> Set a -> Bool
isEquivalenceRelation rel domain = 
  isReflexive rel domain &&
  isSymmetric rel &&
  isTransitive rel

isReflexive :: (Ord a) => Relation a -> Set a -> Bool
isReflexive rel domain = all (\x -> (x, x) `member` rel) (toList domain)

isSymmetric :: (Ord a) => Relation a -> Bool
isSymmetric rel = all (\(x, y) -> (y, x) `member` rel) (toList rel)

isTransitive :: (Ord a) => Relation a -> Bool
isTransitive rel = 
  all (\(x, y) -> 
    all (\(y', z) -> 
      if y == y' then (x, z) `member` rel else True
    ) (toList rel)
  ) (toList rel)

-- 等价类
equivalenceClasses :: (Ord a) => Relation a -> Set a -> Set (Set a)
equivalenceClasses rel domain = 
  fromList [fromList [y | y <- toList domain, (x, y) `member` rel] | x <- toList domain]
```

### 2. 函数理论

#### 2.1 函数定义

**定义 2.1.1** 函数是满足单值性的关系：

$$f: A \rightarrow B$$

其中 $\forall x \in A, \exists! y \in B, (x, y) \in f$。

**定义 2.1.2** 函数性质：

- 单射：$\forall x_1, x_2, f(x_1) = f(x_2) \Rightarrow x_1 = x_2$
- 满射：$\forall y \in B, \exists x \in A, f(x) = y$
- 双射：既是单射又是满射

```haskell
-- 函数类型
type Function a b = a -> b

-- 函数性质检查
isInjective :: (Ord a, Ord b) => Function a b -> Set a -> Bool
isInjective f domain = 
  let pairs = [(x, f x) | x <- toList domain]
      values = [y | (_, y) <- pairs]
  in length values == length (nub values)

isSurjective :: (Ord a, Ord b) => Function a b -> Set a -> Set b -> Bool
isSurjective f domain codomain = 
  let image = fromList [f x | x <- toList domain]
  in image == codomain

isBijective :: (Ord a, Ord b) => Function a b -> Set a -> Set b -> Bool
isBijective f domain codomain = 
  isInjective f domain && isSurjective f domain codomain

-- 函数组合
functionComposition :: (b -> c) -> (a -> b) -> (a -> c)
functionComposition g f = g . f

-- 逆函数
inverseFunction :: (Ord a, Ord b) => Function a b -> Set a -> Set b -> Maybe (Function b a)
inverseFunction f domain codomain = 
  if isBijective f domain codomain
    then Just (\y -> head [x | x <- toList domain, f x == y])
    else Nothing
```

#### 2.2 高阶函数

**定义 2.2.1** 高阶函数是接受函数作为参数或返回函数的函数。

```haskell
-- 高阶函数示例
map :: (a -> b) -> [a] -> [b]
map f = foldr (\x acc -> f x : acc) []

filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\x acc -> if p x then x : acc else acc) []

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

-- 函数应用
apply :: (a -> b) -> a -> b
apply f x = f x

-- 柯里化
curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (x, y) = f x y
```

### 3. 代数结构

#### 3.1 群论

**定义 3.1.1** 群是一个四元组 $(G, \cdot, e, ^{-1})$，其中：

- $G$ 是集合
- $\cdot: G \times G \rightarrow G$ 是二元运算
- $e \in G$ 是单位元
- $^{-1}: G \rightarrow G$ 是逆元函数

满足：

1. 结合律：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. 单位元：$a \cdot e = e \cdot a = a$
3. 逆元：$a \cdot a^{-1} = a^{-1} \cdot a = e$

```haskell
-- 群类型类
class Group g where
  op :: g -> g -> g
  identity :: g
  inverse :: g -> g

-- 群性质检查
isGroup :: (Eq g, Group g) => [g] -> Bool
isGroup elements = 
  let g = fromList elements
  in all (\a -> 
    all (\b -> 
      all (\c -> op (op a b) c == op a (op b c)) (toList g)
    ) (toList g)
  ) (toList g) &&
  all (\a -> op a identity == a && op identity a == a) (toList g) &&
  all (\a -> op a (inverse a) == identity && op (inverse a) a == identity) (toList g)

-- 整数加法群实例
instance Group Integer where
  op = (+)
  identity = 0
  inverse = negate

-- 模n群
data ModN = ModN { value :: Integer, modulus :: Integer }

instance Group ModN where
  op (ModN a n) (ModN b m) = ModN ((a + b) `mod` n) n
  identity = ModN 0 1
  inverse (ModN a n) = ModN (n - a) n
```

#### 3.2 环论

**定义 3.2.1** 环是一个六元组 $(R, +, \cdot, 0, 1, -)$，其中：

- $(R, +, 0, -)$ 是阿贝尔群
- $(R, \cdot, 1)$ 是幺半群
- 分配律：$a \cdot (b + c) = a \cdot b + a \cdot c$

```haskell
-- 环类型类
class Ring r where
  add :: r -> r -> r
  multiply :: r -> r -> r
  zero :: r
  one :: r
  negate :: r -> r

-- 环性质检查
isRing :: (Eq r, Ring r) => [r] -> Bool
isRing elements = 
  let r = fromList elements
  in -- 加法群性质
     all (\a -> add a zero == a) (toList r) &&
     all (\a -> add a (negate a) == zero) (toList r) &&
     -- 乘法幺半群性质
     all (\a -> multiply a one == a) (toList r) &&
     -- 分配律
     all (\a -> 
       all (\b -> 
         all (\c -> 
           multiply a (add b c) == add (multiply a b) (multiply a c)
         ) (toList r)
       ) (toList r)
     ) (toList r)

-- 整数环实例
instance Ring Integer where
  add = (+)
  multiply = (*)
  zero = 0
  one = 1
  negate = Prelude.negate
```

### 4. 序理论

#### 4.1 偏序关系

**定义 4.1.1** 偏序关系满足：

1. 自反性：$\forall x, x \leq x$
2. 反对称性：$\forall x, y, x \leq y \land y \leq x \Rightarrow x = y$
3. 传递性：$\forall x, y, z, x \leq y \land y \leq z \Rightarrow x \leq z$

```haskell
-- 偏序类型类
class PartialOrder a where
  leq :: a -> a -> Bool

-- 偏序性质检查
isPartialOrder :: (PartialOrder a) => [a] -> Bool
isPartialOrder elements = 
  let xs = fromList elements
  in -- 自反性
     all (\x -> leq x x) (toList xs) &&
     -- 反对称性
     all (\x -> 
       all (\y -> 
         if leq x y && leq y x then x == y else True
       ) (toList xs)
     ) (toList xs) &&
     -- 传递性
     all (\x -> 
       all (\y -> 
         all (\z -> 
           if leq x y && leq y z then leq x z else True
         ) (toList xs)
       ) (toList xs)
     ) (toList xs)

-- 全序关系
class (PartialOrder a) => TotalOrder a where
  -- 全序要求任意两个元素都可比较
  compare :: a -> a -> Ordering

-- 上确界和下确界
supremum :: (PartialOrder a) => [a] -> Maybe a
supremum [] = Nothing
supremum xs = 
  let candidates = [x | x <- xs, all (\y -> leq y x) xs]
  in if null candidates then Nothing else Just (minimum candidates)

infimum :: (PartialOrder a) => [a] -> Maybe a
infimum [] = Nothing
infimum xs = 
  let candidates = [x | x <- xs, all (\y -> leq x y) xs]
  in if null candidates then Nothing else Just (maximum candidates)
```

#### 4.2 格理论

**定义 4.2.1** 格是任意两个元素都有上确界和下确界的偏序集。

```haskell
-- 格类型类
class (PartialOrder a) => Lattice a where
  join :: a -> a -> a  -- 上确界
  meet :: a -> a -> a  -- 下确界

-- 格性质检查
isLattice :: (Lattice a, Eq a) => [a] -> Bool
isLattice elements = 
  let xs = fromList elements
  in all (\x -> 
    all (\y -> 
      -- 上确界性质
      leq x (join x y) && leq y (join x y) &&
      -- 下确界性质
      leq (meet x y) x && leq (meet x y) y
    ) (toList xs)
  ) (toList xs)

-- 布尔代数
class (Lattice a) => BooleanAlgebra a where
  top :: a
  bottom :: a
  complement :: a -> a

-- 布尔代数性质
isBooleanAlgebra :: (BooleanAlgebra a, Eq a) => [a] -> Bool
isBooleanAlgebra elements = 
  let xs = fromList elements
  in all (\x -> 
    join x (complement x) == top &&
    meet x (complement x) == bottom
  ) (toList xs)
```

### 5. 范畴论基础

#### 5.1 范畴定义

**定义 5.1.1** 范畴 $\mathcal{C}$ 包含：

- 对象集 $\text{Ob}(\mathcal{C})$
- 态射集 $\text{Hom}(A, B)$
- 复合运算 $\circ$
- 单位态射 $\text{id}_A$

满足：

1. 结合律：$(f \circ g) \circ h = f \circ (g \circ h)$
2. 单位律：$\text{id}_B \circ f = f = f \circ \text{id}_A$

```haskell
-- 范畴类型
data Category obj morph = Category
  { objects :: Set obj
  , morphisms :: obj -> obj -> Set morph
  , compose :: morph -> morph -> Maybe morph
  , identity :: obj -> morph
  }

-- 范畴性质检查
isCategory :: (Ord obj, Ord morph, Eq morph) => Category obj morph -> Bool
isCategory cat = 
  -- 结合律
  all (\obj1 -> 
    all (\obj2 -> 
      all (\obj3 -> 
        all (\obj4 -> 
          all (\f -> 
            all (\g -> 
              all (\h -> 
                case (compose cat f g, compose cat g h) of
                  (Just fg, Just gh) -> 
                    case (compose cat fg h, compose cat f gh) of
                      (Just fgh1, Just fgh2) -> fgh1 == fgh2
                      _ -> False
                  _ -> True
              ) (toList (morphisms cat obj3 obj4))
            ) (toList (morphisms cat obj2 obj3))
          ) (toList (morphisms cat obj1 obj2))
        ) (toList (objects cat))
      ) (toList (objects cat))
    ) (toList (objects cat))
  ) (toList (objects cat))

-- 函子
data Functor obj1 morph1 obj2 morph2 = Functor
  { objectMap :: obj1 -> obj2
  , morphismMap :: morph1 -> morph2
  }

-- 自然变换
data NaturalTransformation obj1 morph1 obj2 morph2 = NaturalTransformation
  { sourceFunctor :: Functor obj1 morph1 obj2 morph2
  , targetFunctor :: Functor obj1 morph1 obj2 morph2
  , components :: obj1 -> morph2
  }
```

### 6. 数论基础

#### 6.1 整除理论

**定义 6.1.1** 整除关系：$a \mid b$ 当且仅当存在 $k$ 使得 $b = ka$。

```haskell
-- 整除关系
divides :: Integer -> Integer -> Bool
divides a b = b `mod` a == 0

-- 最大公约数
gcd :: Integer -> Integer -> Integer
gcd a b = if b == 0 then a else gcd b (a `mod` b)

-- 最小公倍数
lcm :: Integer -> Integer -> Integer
lcm a b = abs (a * b) `div` gcd a b

-- 欧几里得算法
euclideanAlgorithm :: Integer -> Integer -> (Integer, Integer, Integer)
euclideanAlgorithm a b = 
  if b == 0 
    then (a, 1, 0)
    else let (d, x, y) = euclideanAlgorithm b (a `mod` b)
         in (d, y, x - (a `div` b) * y)

-- 素数检查
isPrime :: Integer -> Bool
isPrime n = n > 1 && all (\i -> n `mod` i /= 0) [2..floor (sqrt (fromIntegral n))]

-- 素数生成
primes :: [Integer]
primes = 2 : [n | n <- [3,5..], isPrime n]
```

#### 6.2 同余理论

**定义 6.2.1** 同余关系：$a \equiv b \pmod{m}$ 当且仅当 $m \mid (a - b)$。

```haskell
-- 同余关系
congruent :: Integer -> Integer -> Integer -> Bool
congruent a b m = (a - b) `mod` m == 0

-- 模运算
modularAdd :: Integer -> Integer -> Integer -> Integer
modularAdd a b m = (a + b) `mod` m

modularMultiply :: Integer -> Integer -> Integer -> Integer
modularMultiply a b m = (a * b) `mod` m

modularPower :: Integer -> Integer -> Integer -> Integer
modularPower base exp modulus = 
  if exp == 0 
    then 1
    else if even exp
      then let half = modularPower base (exp `div` 2) modulus
           in (half * half) `mod` modulus
      else (base * modularPower base (exp - 1) modulus) `mod` modulus

-- 中国剩余定理
chineseRemainderTheorem :: [(Integer, Integer)] -> Integer
chineseRemainderTheorem congruences = 
  let m = product [mi | (_, mi) <- congruences]
      solution = sum [ai * mi * (mi `div` gcd mi m) | (ai, mi) <- congruences]
  in solution `mod` m
```

## 🔗 交叉引用

### 与形式语言的联系

- **集合论** → 语言集合
- **关系理论** → 语言关系
- **函数理论** → 语言映射

### 与类型理论的联系

- **范畴论** → 类型范畴
- **代数结构** → 类型代数
- **序理论** → 类型层次

### 与自动机理论的联系

- **集合论** → 状态集
- **关系理论** → 转移关系
- **函数理论** → 转移函数

## 📊 复杂度分析

### 计算复杂度

- **集合操作**: $O(n \log n)$
- **关系运算**: $O(n^2)$
- **函数计算**: $O(1)$
- **群运算**: $O(1)$

### 表达能力

- **集合论**: 基础结构
- **范畴论**: 抽象结构
- **代数**: 运算结构
- **序理论**: 层次结构

## 🎯 应用领域

### 1. 计算机科学

- 数据结构
- 算法设计
- 类型系统

### 2. 软件工程

- 程序验证
- 模型检查
- 形式方法

### 3. 人工智能

- 知识表示
- 逻辑推理
- 机器学习

## 📚 参考文献

1. Halmos, P. R. (1974). Naive Set Theory.
2. Mac Lane, S. (1998). Categories for the Working Mathematician.
3. Hungerford, T. W. (2003). Algebra.

---

**最后更新**: 2024年12月19日  
**相关文档**: [[001-Formal-Language-Theory]], [[003-Category-Theory]], [[004-Algebra]]
