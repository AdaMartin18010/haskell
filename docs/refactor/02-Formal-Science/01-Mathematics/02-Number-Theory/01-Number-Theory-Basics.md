# 数论基础 (Number Theory Basics)

## 概述

数论是研究整数性质的数学分支，是形式科学的基础。本文档从形式化角度介绍数论的基本概念、定理和算法实现。

## 形式化定义

### 基本概念

#### 1. 整除关系

对于整数 $a, b$，如果存在整数 $k$ 使得 $b = ak$，则称 $a$ 整除 $b$，记作 $a \mid b$。

形式化定义：
$$\text{divisible}(a, b) \iff \exists k \in \mathbb{Z}: b = ak$$

#### 2. 最大公约数

两个整数 $a, b$ 的最大公约数 $gcd(a, b)$ 是满足以下条件的最大正整数 $d$：

- $d \mid a$ 且 $d \mid b$
- 对于任意 $c$，如果 $c \mid a$ 且 $c \mid b$，则 $c \mid d$

#### 3. 最小公倍数

两个整数 $a, b$ 的最小公倍数 $lcm(a, b)$ 是满足以下条件的最小正整数 $m$：

- $a \mid m$ 且 $b \mid m$
- 对于任意 $c$，如果 $a \mid c$ 且 $b \mid c$，则 $m \mid c$

#### 4. 素数

正整数 $p > 1$ 是素数，当且仅当 $p$ 的正因子只有 $1$ 和 $p$ 本身。

$$\text{prime}(p) \iff p > 1 \land \forall d \in \mathbb{Z}^+: (d \mid p \implies d = 1 \lor d = p)$$

## Haskell实现

```haskell
-- 数论基础的形式化实现
module NumberTheory where

import Data.List (nub, sort)
import Data.Maybe (fromJust)
import Control.Monad (guard)

-- 整数类型
type Integer = Int

-- 整除关系
divides :: Integer -> Integer -> Bool
divides a b = b `mod` a == 0

-- 因子
factors :: Integer -> [Integer]
factors n = [d | d <- [1..n], n `mod` d == 0]

-- 真因子（不包括自身）
properFactors :: Integer -> [Integer]
properFactors n = [d | d <- [1..n-1], n `mod` d == 0]

-- 素数判定
isPrime :: Integer -> Bool
isPrime n
  | n < 2 = False
  | n == 2 = True
  | even n = False
  | otherwise = not $ any (\d -> n `mod` d == 0) [3,5..floor (sqrt (fromIntegral n))]

-- 素数列表
primes :: [Integer]
primes = 2 : [n | n <- [3,5..], isPrime n]

-- 欧几里得算法求最大公约数
gcd :: Integer -> Integer -> Integer
gcd a 0 = abs a
gcd a b = gcd b (a `mod` b)

-- 扩展欧几里得算法
extendedGcd :: Integer -> Integer -> (Integer, Integer, Integer)
extendedGcd a 0 = (a, 1, 0)
extendedGcd a b = 
  let (d, x, y) = extendedGcd b (a `mod` b)
  in (d, y, x - (a `div` b) * y)

-- 最小公倍数
lcm :: Integer -> Integer -> Integer
lcm a b = abs (a * b) `div` gcd a b

-- 贝祖定理：ax + by = gcd(a,b) 的解
bezoutCoefficients :: Integer -> Integer -> (Integer, Integer)
bezoutCoefficients a b = 
  let (_, x, y) = extendedGcd a b
  in (x, y)

-- 模逆元
modularInverse :: Integer -> Integer -> Maybe Integer
modularInverse a m
  | gcd a m /= 1 = Nothing
  | otherwise = Just $ (x `mod` m + m) `mod` m
  where
    (_, x, _) = extendedGcd a m

-- 中国剩余定理
chineseRemainder :: [(Integer, Integer)] -> Maybe Integer
chineseRemainder [] = Nothing
chineseRemainder [(a, m)] = Just a
chineseRemainder ((a1, m1):(a2, m2):rest) =
  case solveCongruence a1 m1 a2 m2 of
    Nothing -> Nothing
    Just (a, m) -> chineseRemainder ((a, m):rest)

-- 解同余方程
solveCongruence :: Integer -> Integer -> Integer -> Integer -> Maybe (Integer, Integer)
solveCongruence a1 m1 a2 m2 =
  let d = gcd m1 m2
      l = lcm m1 m2
  in if (a2 - a1) `mod` d /= 0
     then Nothing
     else Just (a1, l)

-- 欧拉函数
eulerTotient :: Integer -> Integer
eulerTotient n = fromIntegral $ length [k | k <- [1..n], gcd k n == 1]

-- 费马小定理
fermatLittleTheorem :: Integer -> Integer -> Bool
fermatLittleTheorem a p =
  isPrime p && a `mod` p /= 0 && 
  (a ^ (p - 1)) `mod` p == 1

-- 威尔逊定理
wilsonTheorem :: Integer -> Bool
wilsonTheorem p =
  isPrime p && (factorial (p - 1) + 1) `mod` p == 0

-- 阶乘
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 素数分解
primeFactorization :: Integer -> [(Integer, Integer)]
primeFactorization n = 
  let factors = primeFactors n
  in [(p, count p factors) | p <- nub factors]
  where
    count x = length . filter (== x)
    primeFactors 1 = []
    primeFactors n = 
      let factor = findFactor n
      in factor : primeFactors (n `div` factor)
    findFactor n = 
      head [d | d <- [2..floor (sqrt (fromIntegral n))], n `mod` d == 0]

-- 完全数
isPerfect :: Integer -> Bool
isPerfect n = sum (properFactors n) == n

-- 亲和数
areAmicable :: Integer -> Integer -> Bool
areAmicable a b = 
  a /= b && 
  sum (properFactors a) == b && 
  sum (properFactors b) == a

-- 梅森素数
mersennePrimes :: [Integer]
mersennePrimes = 
  [2^n - 1 | n <- [2..], isPrime n, isPrime (2^n - 1)]

-- 费马数
fermatNumbers :: [Integer]
fermatNumbers = [2^(2^n) + 1 | n <- [0..]]

-- 费马素数
fermatPrimes :: [Integer]
fermatPrimes = filter isPrime fermatNumbers

-- 孪生素数
twinPrimes :: [(Integer, Integer)]
twinPrimes = 
  [(p, p+2) | p <- primes, isPrime (p+2)]

-- 哥德巴赫猜想验证（小范围）
goldbachConjecture :: Integer -> [(Integer, Integer)]
goldbachConjecture n =
  [(p, n-p) | p <- takeWhile (<= n `div` 2) primes, isPrime (n-p)]

-- 黎曼猜想相关：素数计数函数
primeCounting :: Integer -> Integer
primeCounting n = fromIntegral $ length $ takeWhile (<= n) primes

-- 莫比乌斯函数
moebius :: Integer -> Integer
moebius n
  | n == 1 = 1
  | any (\p -> n `mod` (p*p) == 0) (map fst $ primeFactorization n) = 0
  | odd (length $ primeFactorization n) = -1
  | otherwise = 1

-- 欧拉函数乘积公式
eulerTotientProduct :: Integer -> Integer
eulerTotientProduct n = 
  product [p^(k-1) * (p-1) | (p, k) <- primeFactorization n]

-- 数论函数：约数个数
divisorCount :: Integer -> Integer
divisorCount n = 
  product [k + 1 | (_, k) <- primeFactorization n]

-- 数论函数：约数和
divisorSum :: Integer -> Integer
divisorSum n = 
  product [sum [p^i | i <- [0..k]] | (p, k) <- primeFactorization n]

-- 数论函数：欧米伽函数（不同素因子的个数）
omega :: Integer -> Integer
omega n = fromIntegral $ length $ primeFactorization n

-- 数论函数：大欧米伽函数（素因子总个数，包括重数）
bigOmega :: Integer -> Integer
bigOmega n = sum [k | (_, k) <- primeFactorization n]
```

## 形式化证明

### 定理1：欧几里得算法的正确性

**定理**：对于任意整数 $a, b$，欧几里得算法计算出的 $gcd(a, b)$ 是正确的。

**证明**：

1. 设 $d = gcd(a, b)$
2. 算法终止时 $b = 0$，此时 $gcd(a, 0) = |a|$
3. 在每次递归中，$gcd(a, b) = gcd(b, a \bmod b)$
4. 由于 $a \bmod b < b$，算法必然终止
5. 因此算法正确计算了最大公约数

### 定理2：贝祖定理

**定理**：对于任意整数 $a, b$，存在整数 $x, y$ 使得 $ax + by = gcd(a, b)$。

**证明**：

1. 使用扩展欧几里得算法
2. 基础情况：$gcd(a, 0) = a = a \cdot 1 + 0 \cdot 0$
3. 递归情况：设 $gcd(b, a \bmod b) = bx' + (a \bmod b)y'$
4. 代入 $a \bmod b = a - \lfloor a/b \rfloor b$
5. 得到 $ax + by = gcd(a, b)$

### 定理3：费马小定理

**定理**：如果 $p$ 是素数且 $a$ 不是 $p$ 的倍数，则 $a^{p-1} \equiv 1 \pmod{p}$。

**证明**：

1. 考虑集合 $S = \{a, 2a, 3a, ..., (p-1)a\}$
2. 证明 $S$ 中的元素模 $p$ 互不相同
3. 因此 $S$ 模 $p$ 是 $\{1, 2, 3, ..., p-1\}$ 的排列
4. 所以 $a \cdot 2a \cdot 3a \cdots (p-1)a \equiv 1 \cdot 2 \cdot 3 \cdots (p-1) \pmod{p}$
5. 即 $a^{p-1} \cdot (p-1)! \equiv (p-1)! \pmod{p}$
6. 由于 $(p-1)!$ 与 $p$ 互素，得到 $a^{p-1} \equiv 1 \pmod{p}$

## 应用示例

### 密码学应用

```haskell
-- RSA加密系统
data RSAKey = RSAKey
  { modulus :: Integer
  , exponent :: Integer
  } deriving Show

-- 生成RSA密钥对
generateRSAKeys :: Integer -> Integer -> (RSAKey, RSAKey)
generateRSAKeys p q =
  let n = p * q
      phi = (p - 1) * (q - 1)
      e = 65537  -- 常用公钥指数
      d = fromJust $ modularInverse e phi
  in (RSAKey n e, RSAKey n d)

-- RSA加密
rsaEncrypt :: RSAKey -> Integer -> Integer
rsaEncrypt (RSAKey n e) m = m^e `mod` n

-- RSA解密
rsaDecrypt :: RSAKey -> Integer -> Integer
rsaDecrypt (RSAKey n d) c = c^d `mod` n
```

### 随机数生成

```haskell
-- 线性同余生成器
linearCongruential :: Integer -> Integer -> Integer -> Integer -> [Integer]
linearCongruential a c m x0 = 
  x0 : linearCongruential a c m ((a * x0 + c) `mod` m)

-- 梅森旋转算法（简化版）
mersenneTwister :: Integer -> [Integer]
mersenneTwister seed = 
  let n = 624
      m = 397
      a = 0x9908b0df
      generateNumbers = iterate (\x -> (x * 1103515245 + 12345) `mod` (2^32)) seed
  in take n generateNumbers
```

## 与其他理论的关联

- **与集合论的关系**：整数集合是数论研究的基础
- **与代数结构的关系**：整数环是重要的代数结构
- **与密码学的关系**：数论是密码学的重要数学基础
- **与算法理论的关系**：数论算法是算法复杂度分析的重要案例

## 总结

数论基础通过形式化方法建立了严格的整数理论体系，为密码学、算法设计和数学研究提供了重要工具。通过Haskell的实现，我们可以验证数论定理的正确性，并应用于实际的计算问题。

## 相关链接

- [集合论基础](../01-Set-Theory/01-Set-Theory-Basics.md)
- [代数结构](../04-Algebraic-Structures.md)
- [密码学理论](../../04-Applied-Science/05-Network-Security/01-Cryptography.md)
- [算法复杂度理论](../../03-Theory/01-Programming-Language-Theory/02-Semantics-Theory/README.md)
