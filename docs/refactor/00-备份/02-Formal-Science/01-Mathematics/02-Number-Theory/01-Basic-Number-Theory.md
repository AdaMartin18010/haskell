# 基础数论 - 数学基础核心

## 📚 概述

基础数论是数学的核心分支，研究整数的性质和结构。我们将建立严格的形式化理论，包括整除性、素数、同余、欧几里得算法等核心概念，并提供完整的Haskell实现。

## 🏗️ 形式化定义

### 1. 基础数论类型

```haskell
-- 整数类型
type Integer = Int

-- 自然数类型
type Natural = Integer

-- 素数类型
type Prime = Integer

-- 同余关系类型
type Congruence = (Integer, Integer, Integer) -- (a, b, m) 表示 a ≡ b (mod m)

-- 最大公约数类型
type GCD = Integer

-- 最小公倍数类型
type LCM = Integer
```

### 2. 整除性关系

```haskell
-- 整除关系
divides :: Integer -> Integer -> Bool
divides a b = b `mod` a == 0

-- 严格整除关系
strictlyDivides :: Integer -> Integer -> Bool
strictlyDivides a b = a /= 0 && b `mod` a == 0 && abs a < abs b

-- 倍数关系
isMultiple :: Integer -> Integer -> Bool
isMultiple a b = a `mod` b == 0

-- 互质关系
coprime :: Integer -> Integer -> Bool
coprime a b = gcd a b == 1
```

## 🧮 数学形式化

### 1. 整除性定义

对于整数 $a$ 和 $b$，我们说 $a$ 整除 $b$（记作 $a \mid b$），当且仅当存在整数 $k$ 使得：

$$b = a \cdot k$$

形式化表示为：

$$a \mid b \Leftrightarrow \exists k \in \mathbb{Z} : b = a \cdot k$$

### 2. 素数定义

素数 $p$ 是大于1的自然数，且只有1和自身两个正因子：

$$p \text{ 是素数 } \Leftrightarrow p > 1 \land \forall d \in \mathbb{N} : d \mid p \Rightarrow d = 1 \lor d = p$$

### 3. 同余定义

对于整数 $a$、$b$ 和正整数 $m$，我们说 $a$ 与 $b$ 模 $m$ 同余（记作 $a \equiv b \pmod{m}$），当且仅当：

$$m \mid (a - b)$$

形式化表示为：

$$a \equiv b \pmod{m} \Leftrightarrow m \mid (a - b)$$

### 4. 最大公约数定义

整数 $a$ 和 $b$ 的最大公约数 $\gcd(a,b)$ 是满足以下条件的最大正整数 $d$：

$$d \mid a \land d \mid b \land \forall c \in \mathbb{Z} : (c \mid a \land c \mid b) \Rightarrow c \leq d$$

## 🔧 Haskell实现

### 1. 基础数论函数

```haskell
-- 判断是否为素数
isPrime :: Integer -> Bool
isPrime n
    | n <= 1 = False
    | n == 2 = True
    | even n = False
    | otherwise = not $ any (\d -> n `mod` d == 0) [3, 5..floor (sqrt (fromIntegral n))]

-- 生成素数序列
primes :: [Integer]
primes = 2 : filter isPrime [3, 5..]

-- 质因数分解
primeFactors :: Integer -> [Integer]
primeFactors n = primeFactors' n primes
  where
    primeFactors' 1 _ = []
    primeFactors' n (p:ps)
        | p * p > n = [n]
        | n `mod` p == 0 = p : primeFactors' (n `div` p) (p:ps)
        | otherwise = primeFactors' n ps

-- 欧拉函数
eulerPhi :: Integer -> Integer
eulerPhi n = product [p^(k-1) * (p-1) | (p, k) <- factorize n]
  where
    factorize n = [(p, length (takeWhile (== p) (primeFactors n))) | p <- nub (primeFactors n)]
```

### 2. 同余运算

```haskell
-- 同余关系
congruent :: Integer -> Integer -> Integer -> Bool
congruent a b m = (a - b) `mod` m == 0

-- 模运算
modulo :: Integer -> Integer -> Integer
modulo a m = ((a `mod` m) + m) `mod` m

-- 模逆元
modularInverse :: Integer -> Integer -> Maybe Integer
modularInverse a m
    | gcd a m /= 1 = Nothing
    | otherwise = Just (modulo (extendedGCD a m) m)
  where
    extendedGCD a b = fst (extendedEuclidean a b)

-- 扩展欧几里得算法
extendedEuclidean :: Integer -> Integer -> (Integer, Integer, Integer)
extendedEuclidean a b = go a b 1 0 0 1
  where
    go r0 r1 s0 s1 t0 t1
        | r1 == 0 = (r0, s0, t0)
        | otherwise = go r1 r2 s1 s2 t1 t2
      where
        q = r0 `div` r1
        r2 = r0 - q * r1
        s2 = s0 - q * s1
        t2 = t0 - q * t1
```

### 3. 数论函数

```haskell
-- 约数个数
divisorCount :: Integer -> Integer
divisorCount n = product [k + 1 | (_, k) <- factorize n]
  where
    factorize n = [(p, length (takeWhile (== p) (primeFactors n))) | p <- nub (primeFactors n)]

-- 约数和
divisorSum :: Integer -> Integer
divisorSum n = product [sum [p^i | i <- [0..k]] | (p, k) <- factorize n]
  where
    factorize n = [(p, length (takeWhile (== p) (primeFactors n))) | p <- nub (primeFactors n)]

-- 完全数判断
isPerfect :: Integer -> Bool
isPerfect n = n > 0 && divisorSum n == 2 * n

-- 亲和数判断
areAmicable :: Integer -> Integer -> Bool
areAmicable a b = a /= b && divisorSum a == b && divisorSum b == a
```

### 4. 高级数论算法

```haskell
-- 中国剩余定理
chineseRemainder :: [(Integer, Integer)] -> Maybe Integer
chineseRemainder [] = Nothing
chineseRemainder [(a, m)] = Just (modulo a m)
chineseRemainder ((a1, m1):(a2, m2):rest) = do
    let (x, y, d) = extendedEuclidean m1 m2
    if d /= 1 then Nothing else do
        let m = m1 * m2
        let a = modulo (a1 * y * m2 + a2 * x * m1) m
        chineseRemainder ((a, m):rest)

-- 费马小定理
fermatLittleTheorem :: Integer -> Integer -> Bool
fermatLittleTheorem a p = isPrime p && a `mod` p /= 0 && 
                          powerMod a (p-1) p == 1

-- 快速幂模运算
powerMod :: Integer -> Integer -> Integer -> Integer
powerMod base exp modulus = go base exp 1
  where
    go _ 0 result = result
    go b e r
        | odd e = go (b * b `mod` modulus) (e `div` 2) (r * b `mod` modulus)
        | otherwise = go (b * b `mod` modulus) (e `div` 2) r

-- 米勒-拉宾素性测试
millerRabin :: Integer -> Integer -> Bool
millerRabin n a
    | n <= 1 = False
    | n == 2 = True
    | even n = False
    | otherwise = millerRabinTest n a
  where
    millerRabinTest n a = 
        let (d, s) = decompose (n - 1)
        in any (\r -> powerMod a (2^r * d) n == n - 1) [0..s-1] ||
           powerMod a d n == 1
      where
        decompose n = go n 0
          where
            go m s
                | odd m = (m, s)
                | otherwise = go (m `div` 2) (s + 1)
```

## 🎯 应用示例

### 1. 基础数论计算

```haskell
-- 基础数论计算示例
basicNumberTheoryExample :: IO ()
basicNumberTheoryExample = do
    putStrLn "=== 基础数论计算示例 ==="
    
    -- 素数判断
    let testNumbers = [2, 3, 4, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    putStrLn "素数判断:"
    mapM_ (\n -> putStrLn $ show n ++ " 是素数: " ++ show (isPrime n)) testNumbers
    
    -- 质因数分解
    let factorNumbers = [12, 24, 36, 48, 60]
    putStrLn "\n质因数分解:"
    mapM_ (\n -> putStrLn $ show n ++ " = " ++ show (primeFactors n)) factorNumbers
    
    -- 欧拉函数
    putStrLn "\n欧拉函数值:"
    mapM_ (\n -> putStrLn $ "φ(" ++ show n ++ ") = " ++ show (eulerPhi n)) [1..10]
    
    -- 完全数
    let perfectNumbers = filter isPerfect [1..1000]
    putStrLn $ "\n1000以内的完全数: " ++ show perfectNumbers
```

### 2. 同余运算示例

```haskell
-- 同余运算示例
congruenceExample :: IO ()
congruenceExample = do
    putStrLn "\n=== 同余运算示例 ==="
    
    -- 同余关系验证
    let testCases = [(17, 5, 6), (23, 11, 6), (35, 11, 8)]
    putStrLn "同余关系验证:"
    mapM_ (\(a, b, m) -> 
        putStrLn $ show a ++ " ≡ " ++ show b ++ " (mod " ++ show m ++ "): " ++ 
                  show (congruent a b m)) testCases
    
    -- 模逆元计算
    let inverseCases = [(3, 7), (5, 11), (7, 13)]
    putStrLn "\n模逆元计算:"
    mapM_ (\(a, m) -> 
        case modularInverse a m of
            Just inv -> putStrLn $ show a ++ "⁻¹ (mod " ++ show m ++ ") = " ++ show inv
            Nothing -> putStrLn $ show a ++ " 在模 " ++ show m ++ " 下无逆元") inverseCases
    
    -- 中国剩余定理
    let crtCases = [((2, 3), (3, 5), (2, 7))]
    putStrLn "\n中国剩余定理:"
    mapM_ (\((a1, m1), (a2, m2), (a3, m3)) -> 
        case chineseRemainder [(a1, m1), (a2, m2), (a3, m3)] of
            Just x -> putStrLn $ "解: x ≡ " ++ show x ++ " (mod " ++ show (m1 * m2 * m3) ++ ")"
            Nothing -> putStrLn "无解") crtCases
```

### 3. 高级数论应用

```haskell
-- 高级数论应用示例
advancedNumberTheoryExample :: IO ()
advancedNumberTheoryExample = do
    putStrLn "\n=== 高级数论应用示例 ==="
    
    -- 费马小定理验证
    let fermatCases = [(2, 3), (3, 5), (5, 7), (7, 11)]
    putStrLn "费马小定理验证:"
    mapM_ (\(a, p) -> 
        putStrLn $ show a ++ "^(" ++ show p ++ "-1) ≡ 1 (mod " ++ show p ++ "): " ++ 
                  show (fermatLittleTheorem a p)) fermatCases
    
    -- 米勒-拉宾素性测试
    let testPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    putStrLn "\n米勒-拉宾素性测试 (以2为底):"
    mapM_ (\p -> putStrLn $ show p ++ " 通过测试: " ++ show (millerRabin p 2)) testPrimes
    
    -- 亲和数对
    let amicablePairs = [(220, 284), (1184, 1210), (2620, 2924)]
    putStrLn "\n亲和数对验证:"
    mapM_ (\(a, b) -> 
        putStrLn $ show a ++ " 和 " ++ show b ++ " 是亲和数: " ++ 
                  show (areAmicable a b)) amicablePairs
```

## 🔬 形式化验证

### 1. 数论性质验证

```haskell
-- 验证数论性质
verifyNumberTheoryProperties :: IO ()
verifyNumberTheoryProperties = do
    putStrLn "=== 数论性质验证 ==="
    
    -- 验证整除性质
    let a = 12
    let b = 36
    putStrLn $ "验证: " ++ show a ++ " | " ++ show b ++ " = " ++ show (a `divides` b)
    putStrLn $ "验证: " ++ show b ++ " 是 " ++ show a ++ " 的倍数 = " ++ show (b `isMultiple` a)
    
    -- 验证互质性质
    let c = 8
    let d = 15
    putStrLn $ "验证: " ++ show c ++ " 和 " ++ show d ++ " 互质 = " ++ show (coprime c d)
    
    -- 验证同余性质
    let e = 17
    let f = 5
    let m = 6
    putStrLn $ "验证: " ++ show e ++ " ≡ " ++ show f ++ " (mod " ++ show m ++ ") = " ++ 
              show (congruent e f m)
```

### 2. 算法正确性验证

```haskell
-- 验证算法正确性
verifyAlgorithmCorrectness :: IO ()
verifyAlgorithmCorrectness = do
    putStrLn "\n=== 算法正确性验证 ==="
    
    -- 验证欧几里得算法
    let testPairs = [(48, 18), (54, 24), (72, 36)]
    putStrLn "欧几里得算法验证:"
    mapM_ (\(a, b) -> 
        let g = gcd a b
        in putStrLn $ "gcd(" ++ show a ++ ", " ++ show b ++ ") = " ++ show g ++ 
                     " (验证: " ++ show (a `mod` g == 0 && b `mod` g == 0) ++ ")") testPairs
    
    -- 验证质因数分解
    let testNumbers = [12, 24, 36, 48]
    putStrLn "\n质因数分解验证:"
    mapM_ (\n -> 
        let factors = product (primeFactors n)
        in putStrLn $ show n ++ " 的质因数分解: " ++ show (primeFactors n) ++ 
                     " (验证: " ++ show (factors == n) ++ ")") testNumbers
```

## 📊 数论函数表

| 函数 | 定义 | Haskell实现 | 时间复杂度 |
|------|------|-------------|-----------|
| 素数判断 | $p > 1 \land \forall d \mid p : d = 1 \lor d = p$ | `isPrime` | $O(\sqrt{n})$ |
| 质因数分解 | $n = \prod_{i=1}^k p_i^{e_i}$ | `primeFactors` | $O(\sqrt{n})$ |
| 欧拉函数 | $\phi(n) = n \prod_{p \mid n} (1 - \frac{1}{p})$ | `eulerPhi` | $O(\sqrt{n})$ |
| 最大公约数 | $\gcd(a,b) = \max\{d : d \mid a \land d \mid b\}$ | `gcd` | $O(\log n)$ |
| 模逆元 | $a \cdot a^{-1} \equiv 1 \pmod{m}$ | `modularInverse` | $O(\log n)$ |

## 🎯 数论应用

### 1. 密码学应用

- **RSA加密**：基于大数分解的困难性
- **椭圆曲线密码**：基于椭圆曲线上的离散对数问题
- **数字签名**：基于数论函数的单向性

### 2. 计算机科学应用

- **哈希函数**：基于模运算和素数性质
- **随机数生成**：基于线性同余和素数模
- **算法优化**：基于数论函数的性质

### 3. 数学应用

- **代数数论**：研究代数数域的结构
- **解析数论**：使用分析方法研究数论问题
- **组合数论**：研究数论中的组合问题

## 🔗 相关链接

- [代数结构](../05-Algebraic-Structures/)
- [线性代数](../03-Linear-Algebra/)
- [矩阵理论](../04-Matrix-Theory/)
- [形式逻辑](../02-Formal-Logic/)

## 📚 参考文献

1. Hardy, G. H., & Wright, E. M. (2008). *An Introduction to the Theory of Numbers*. Oxford University Press.
2. Rosen, K. H. (2011). *Elementary Number Theory and Its Applications*. Pearson.
3. Ireland, K., & Rosen, M. (1990). *A Classical Introduction to Modern Number Theory*. Springer.
4. Cohen, H. (1993). *A Course in Computational Algebraic Number Theory*. Springer.

---

**最后更新**: 2024年12月  
**作者**: 形式化知识体系项目组  
**版本**: 1.0
