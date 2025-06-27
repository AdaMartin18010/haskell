# 代数结构基础 (Algebraic Structures Foundation)

## 📚 概述

代数结构是数学的基础，为函数式编程、类型理论和形式化方法提供了重要的理论基础。本文档构建了完整的代数结构体系，从基本概念到高级应用，为后续的理论发展奠定坚实基础。

## 🎯 核心概念

### 1. 群论基础

**定义 1.1 (群)**
群是一个集合 $G$ 连同二元运算 $\cdot: G \times G \to G$，满足以下公理：

1. **结合律**：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. **单位元**：存在 $e \in G$ 使得 $e \cdot a = a \cdot e = a$
3. **逆元**：对于每个 $a \in G$，存在 $a^{-1} \in G$ 使得 $a \cdot a^{-1} = a^{-1} \cdot a = e$

**Haskell 实现：**

```haskell
-- 群类型类
class Group g where
  -- 群运算
  (<>) :: g -> g -> g
  
  -- 单位元
  identity :: g
  
  -- 逆元
  inverse :: g -> g

-- 群定律验证
groupAssoc :: Group g => g -> g -> g -> Bool
groupAssoc a b c = 
  let lhs = (a <> b) <> c
      rhs = a <> (b <> c)
  in lhs == rhs

groupIdentity :: Group g => g -> Bool
groupIdentity a = 
  let lhs = identity <> a
      rhs = a <> identity
  in lhs == a && rhs == a

groupInverse :: Group g => g -> Bool
groupInverse a = 
  let inv = inverse a
      lhs = a <> inv
      rhs = inv <> a
  in lhs == identity && rhs == identity

-- 具体群实例：整数加法群
instance Group Integer where
  (<>) = (+)
  identity = 0
  inverse = negate

-- 具体群实例：有理数乘法群（非零元素）
newtype NonZeroRational = NonZeroRational Rational

instance Group NonZeroRational where
  NonZeroRational a <> NonZeroRational b = NonZeroRational (a * b)
  identity = NonZeroRational 1
  inverse (NonZeroRational a) = NonZeroRational (recip a)
```

**定义 1.2 (阿贝尔群)**
阿贝尔群是满足交换律的群：
$$a \cdot b = b \cdot a$$

**Haskell 实现：**

```haskell
-- 阿贝尔群类型类
class Group g => AbelianGroup g where
  -- 交换律验证
  commutative :: g -> g -> Bool
  commutative a b = a <> b == b <> a

-- 整数加法群是阿贝尔群
instance AbelianGroup Integer where
  commutative = const $ const True
```

### 2. 环论基础

**定义 1.3 (环)**
环是一个集合 $R$ 连同两个二元运算 $+$ 和 $\cdot$，满足：

1. $(R, +)$ 是阿贝尔群
2. $(R, \cdot)$ 是幺半群
3. **分配律**：$a \cdot (b + c) = a \cdot b + a \cdot c$ 和 $(a + b) \cdot c = a \cdot c + b \cdot c$

**Haskell 实现：**

```haskell
-- 环类型类
class (AbelianGroup r) => Ring r where
  -- 乘法运算
  (<.>) :: r -> r -> r
  
  -- 乘法单位元
  one :: r
  
  -- 环定律验证
  ringDistributive :: r -> r -> r -> Bool
  ringDistributive a b c = 
    let lhs1 = a <.> (b <> c)
        rhs1 = (a <.> b) <> (a <.> c)
        lhs2 = (a <> b) <.> c
        rhs2 = (a <.> c) <> (b <.> c)
    in lhs1 == rhs1 && lhs2 == rhs2

-- 整数环实例
instance Ring Integer where
  (<.>) = (*)
  one = 1
  ringDistributive = const $ const $ const True
```

**定义 1.4 (域)**
域是一个环 $F$，其中非零元素在乘法下构成阿贝尔群。

**Haskell 实现：**

```haskell
-- 域类型类
class Ring f => Field f where
  -- 除法运算
  (</>) :: f -> f -> f
  
  -- 域定律验证
  fieldInverse :: f -> Bool
  fieldInverse a = 
    if a == identity then True
    else a </> a == one

-- 有理数域实例
instance Field Rational where
  a </> b = a / b
  fieldInverse a = a / a == 1
```

### 3. 模论基础

**定义 1.5 (模)**
设 $R$ 是环，$M$ 是阿贝尔群，如果存在标量乘法 $R \times M \to M$ 满足：

1. $(r + s) \cdot m = r \cdot m + s \cdot m$
2. $r \cdot (m + n) = r \cdot m + r \cdot n$
3. $(r \cdot s) \cdot m = r \cdot (s \cdot m)$
4. $1 \cdot m = m$

则称 $M$ 是 $R$-模。

**Haskell 实现：**

```haskell
-- 模类型类
class (Ring r, AbelianGroup m) => Module r m where
  -- 标量乘法
  (<*>) :: r -> m -> m
  
  -- 模定律验证
  moduleDistributive :: r -> r -> m -> Bool
  moduleDistributive r s m = 
    let lhs = (r <> s) <*> m
        rhs = (r <*> m) <> (s <*> m)
    in lhs == rhs

  moduleScalarDistributive :: r -> m -> m -> Bool
  moduleScalarDistributive r m n = 
    let lhs = r <*> (m <> n)
        rhs = (r <*> m) <> (r <*> n)
    in lhs == rhs

-- 向量空间实例（有理数上的向量）
newtype Vector = Vector [Rational]

instance AbelianGroup Vector where
  Vector v1 <> Vector v2 = Vector (zipWith (+) v1 v2)
  identity = Vector (repeat 0)
  inverse (Vector v) = Vector (map negate v)

instance Module Rational Vector where
  r <*> Vector v = Vector (map (r *) v)
```

### 4. 代数结构的高级概念

**定义 1.6 (同态)**
设 $(G, \cdot)$ 和 $(H, \circ)$ 是两个群，映射 $f: G \to H$ 是群同态，如果：
$$f(a \cdot b) = f(a) \circ f(b)$$

**Haskell 实现：**

```haskell
-- 同态类型类
class (Group g, Group h) => GroupHomomorphism g h where
  hom :: g -> h
  
  -- 同态性质验证
  homomorphism :: g -> g -> Bool
  homomorphism a b = 
    let lhs = hom (a <> b)
        rhs = hom a <> hom b
    in lhs == rhs

-- 具体同态示例：指数函数
instance GroupHomomorphism Integer Rational where
  hom n = 2 ^^ n
  
  homomorphism a b = 
    let lhs = hom (a <> b)
        rhs = hom a <> hom b
    in lhs == rhs
```

**定义 1.7 (同构)**
同态 $f: G \to H$ 是同构，如果存在同态 $g: H \to G$ 使得：
$$g \circ f = id_G, \quad f \circ g = id_H$$

**Haskell 实现：**

```haskell
-- 同构类型类
class (GroupHomomorphism g h, GroupHomomorphism h g) => GroupIsomorphism g h where
  iso :: g -> h
  isoInv :: h -> g
  
  -- 同构性质验证
  isomorphism :: g -> Bool
  isomorphism g = 
    let lhs = isoInv (iso g)
        rhs = g
    in lhs == rhs

-- 具体同构示例：整数和有理数的加法群
instance GroupIsomorphism Integer Integer where
  iso = id
  isoInv = id
  
  isomorphism = const True
```

## 🔄 重要定理

### 1. 拉格朗日定理

**定理 1.1 (拉格朗日定理)**
有限群 $G$ 的子群 $H$ 的阶整除 $G$ 的阶。

**证明：** 通过陪集分解。

```haskell
-- 子群类型
data Subgroup g = Subgroup [g]

-- 陪集类型
data Coset g = Coset g [g]

-- 拉格朗日定理验证
lagrangeTheorem :: Group g => [g] -> [g] -> Bool
lagrangeTheorem groupElements subgroupElements = 
  let groupOrder = length groupElements
      subgroupOrder = length subgroupElements
      cosets = generateCosets groupElements subgroupElements
      totalCosets = length cosets
  in groupOrder == subgroupOrder * totalCosets

-- 生成陪集
generateCosets :: Group g => [g] -> [g] -> [Coset g]
generateCosets groupElements subgroupElements = 
  let leftCosets = [Coset g subgroupElements | g <- groupElements]
      uniqueCosets = removeDuplicates leftCosets
  in uniqueCosets

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = foldr (\x acc -> if x `elem` acc then acc else x:acc) []
```

### 2. 中国剩余定理

**定理 1.2 (中国剩余定理)**
设 $m_1, m_2, \ldots, m_n$ 是两两互素的正整数，则对于任意整数 $a_1, a_2, \ldots, a_n$，存在唯一的整数 $x$ 满足：
$$x \equiv a_i \pmod{m_i}, \quad i = 1, 2, \ldots, n$$

**Haskell 实现：**

```haskell
-- 中国剩余定理
chineseRemainder :: [(Integer, Integer)] -> Integer
chineseRemainder congruences = 
  let moduli = map fst congruences
      remainders = map snd congruences
      product = foldl (*) 1 moduli
      solutions = zipWith (\m r -> 
        let mi = product `div` m
            miInv = modInverse mi m
        in (r * mi * miInv) `mod` product) moduli remainders
  in sum solutions `mod` product

-- 模逆元计算
modInverse :: Integer -> Integer -> Integer
modInverse a m = 
  let (x, _, _) = extendedGCD a m
  in (x `mod` m + m) `mod` m

-- 扩展欧几里得算法
extendedGCD :: Integer -> Integer -> (Integer, Integer, Integer)
extendedGCD a 0 = (1, 0, a)
extendedGCD a b = 
  let (x, y, d) = extendedGCD b (a `mod` b)
  in (y, x - (a `div` b) * y, d)
```

## 🎯 应用领域

### 1. 密码学

**定义 1.8 (RSA加密)**
RSA加密基于大整数分解的困难性：

1. 选择两个大素数 $p, q$
2. 计算 $n = pq$ 和 $\phi(n) = (p-1)(q-1)$
3. 选择公钥 $e$ 使得 $\gcd(e, \phi(n)) = 1$
4. 计算私钥 $d$ 使得 $ed \equiv 1 \pmod{\phi(n)}$

**Haskell 实现：**

```haskell
-- RSA密钥对
data RSAKeyPair = RSAKeyPair {
  publicKey :: (Integer, Integer),  -- (e, n)
  privateKey :: (Integer, Integer)  -- (d, n)
}

-- 生成RSA密钥对
generateRSAKeyPair :: Integer -> Integer -> RSAKeyPair
generateRSAKeyPair p q = 
  let n = p * q
      phi = (p - 1) * (q - 1)
      e = 65537  -- 常用公钥
      d = modInverse e phi
  in RSAKeyPair (e, n) (d, n)

-- RSA加密
rsaEncrypt :: (Integer, Integer) -> Integer -> Integer
rsaEncrypt (e, n) m = modExp m e n

-- RSA解密
rsaDecrypt :: (Integer, Integer) -> Integer -> Integer
rsaDecrypt (d, n) c = modExp c d n

-- 模幂运算
modExp :: Integer -> Integer -> Integer -> Integer
modExp base exp modulus = 
  let go b e acc
        | e == 0 = acc
        | odd e = go (b * b `mod` modulus) (e `div` 2) (acc * b `mod` modulus)
        | otherwise = go (b * b `mod` modulus) (e `div` 2) acc
  in go base exp 1
```

### 2. 编码理论

**定义 1.9 (线性码)**
线性码是向量空间 $F_q^n$ 的子空间。

**Haskell 实现：**

```haskell
-- 有限域元素
newtype GFElement = GFElement Integer

-- 线性码
data LinearCode = LinearCode {
  generatorMatrix :: [[GFElement]],
  parityCheckMatrix :: [[GFElement]]
}

-- 编码
encode :: LinearCode -> [GFElement] -> [GFElement]
encode code message = 
  let g = generatorMatrix code
      encoded = matrixVectorMultiply g message
  in encoded

-- 解码
decode :: LinearCode -> [GFElement] -> [GFElement]
decode code received = 
  let h = parityCheckMatrix code
      syndrome = matrixVectorMultiply h received
      errorPattern = findErrorPattern syndrome
      corrected = vectorAdd received errorPattern
  in corrected

-- 矩阵向量乘法
matrixVectorMultiply :: [[GFElement]] -> [GFElement] -> [GFElement]
matrixVectorMultiply matrix vector = 
  map (\row -> sum (zipWith (*) row vector)) matrix

-- 向量加法
vectorAdd :: [GFElement] -> [GFElement] -> [GFElement]
vectorAdd = zipWith (+)
```

## 🔗 交叉引用

- [[001-Mathematical-Ontology]] - 数学本体论基础
- [[002-Formal-Logic]] - 形式逻辑基础
- [[003-Category-Theory]] - 范畴论基础
- [[haskell/01-Basic-Concepts]] - Haskell基础概念
- [[haskell/02-Type-System]] - Haskell类型系统

## 📚 参考文献

1. Dummit, D. S., & Foote, R. M. (2004). Abstract algebra. John Wiley & Sons.
2. Hungerford, T. W. (2003). Algebra. Springer.
3. Lang, S. (2002). Algebra. Springer.
4. Artin, M. (2011). Algebra. Pearson.

---

**文档状态**：✅ 完成  
**最后更新**：2024-12-19  
**版本**：1.0
