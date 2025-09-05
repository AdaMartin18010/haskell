# 整数理论 (Integer Theory)

## 概述

整数理论是自然数理论的扩展，研究整数的性质和结构。本节将从形式化角度分析整数理论，并用Haskell实现相关的概念、运算和定理。

## 形式化定义

### 基本概念

```haskell
-- 整数的数据类型（基于自然数的构造）
data Integer = 
    Positive Natural    -- 正整数
  | Zero               -- 零
  | Negative Natural   -- 负整数
  deriving (Show, Eq, Ord)

-- 整数的基本运算
class IntegerOperations a where
  add :: a -> a -> a
  subtract :: a -> a -> a
  multiply :: a -> a -> a
  divide :: a -> a -> Maybe a
  modulo :: a -> a -> Maybe a
  abs :: a -> a
  sign :: a -> Int

instance IntegerOperations Integer where
  add (Positive m) (Positive n) = Positive (add m n)
  add (Negative m) (Negative n) = Negative (add m n)
  add (Positive m) (Negative n) = 
    if m > n then Positive (subtract m n) else Negative (subtract n m)
  add (Negative m) (Positive n) = 
    if n > m then Positive (subtract n m) else Negative (subtract m n)
  add Zero n = n
  add n Zero = n
  
  subtract (Positive m) (Positive n) = 
    if m >= n then Positive (subtract m n) else Negative (subtract n m)
  subtract (Negative m) (Negative n) = 
    if n >= m then Negative (subtract m n) else Positive (subtract n m)
  subtract (Positive m) (Negative n) = Positive (add m n)
  subtract (Negative m) (Positive n) = Negative (add m n)
  subtract Zero (Positive n) = Negative n
  subtract Zero (Negative n) = Positive n
  subtract n Zero = n
  
  multiply (Positive m) (Positive n) = Positive (multiply m n)
  multiply (Negative m) (Negative n) = Positive (multiply m n)
  multiply (Positive m) (Negative n) = Negative (multiply m n)
  multiply (Negative m) (Positive n) = Negative (multiply m n)
  multiply Zero _ = Zero
  multiply _ Zero = Zero
  
  divide _ Zero = Nothing
  divide Zero _ = Just Zero
  divide (Positive m) (Positive n) = 
    if divides n m then Just (Positive (divide m n)) else Nothing
  divide (Negative m) (Negative n) = 
    if divides n m then Just (Positive (divide m n)) else Nothing
  divide (Positive m) (Negative n) = 
    if divides n m then Just (Negative (divide m n)) else Nothing
  divide (Negative m) (Positive n) = 
    if divides n m then Just (Negative (divide m n)) else Nothing
  
  modulo _ Zero = Nothing
  modulo Zero _ = Just Zero
  modulo (Positive m) (Positive n) = Just (Positive (modulo m n))
  modulo (Negative m) (Positive n) = 
    let r = modulo m n
    in if r == Zero then Just Zero else Just (Positive (subtract n r))
  modulo (Positive m) (Negative n) = modulo (Positive m) (Positive n)
  modulo (Negative m) (Negative n) = modulo (Negative m) (Positive n)
  
  abs (Positive n) = Positive n
  abs (Negative n) = Positive n
  abs Zero = Zero
  
  sign (Positive _) = 1
  sign (Negative _) = -1
  sign Zero = 0
```

### 整数的性质

```haskell
-- 整数的基本性质
class IntegerProperties a where
  isPositive :: a -> Bool
  isNegative :: a -> Bool
  isZero :: a -> Bool
  isNonZero :: a -> Bool
  isEven :: a -> Bool
  isOdd :: a -> Bool

instance IntegerProperties Integer where
  isPositive (Positive _) = True
  isPositive _ = False
  
  isNegative (Negative _) = True
  isNegative _ = False
  
  isZero Zero = True
  isZero _ = False
  
  isNonZero Zero = False
  isNonZero _ = True
  
  isEven Zero = True
  isEven (Positive n) = isEven n
  isEven (Negative n) = isEven n
  
  isOdd Zero = False
  isOdd (Positive n) = isOdd n
  isOdd (Negative n) = isOdd n
```

## 环结构

### 整数环

```haskell
-- 整数环的性质
class RingProperties a where
  addCommutative :: a -> a -> Bool
  addAssociative :: a -> a -> a -> Bool
  addIdentity :: a -> Bool
  addInverse :: a -> Bool
  multiplyAssociative :: a -> a -> a -> Bool
  multiplyDistributive :: a -> a -> a -> Bool
  multiplyIdentity :: a -> Bool

instance RingProperties Integer where
  addCommutative m n = add m n == add n m
  
  addAssociative m n p = add (add m n) p == add m (add n p)
  
  addIdentity n = add Zero n == n && add n Zero == n
  
  addInverse n = add n (negate n) == Zero
    where
      negate (Positive n) = Negative n
      negate (Negative n) = Positive n
      negate Zero = Zero
  
  multiplyAssociative m n p = multiply (multiply m n) p == multiply m (multiply n p)
  
  multiplyDistributive m n p = 
    multiply m (add n p) == add (multiply m n) (multiply m p)
  
  multiplyIdentity n = multiply (Positive (Succ Zero)) n == n && multiply n (Positive (Succ Zero)) == n
```

### 欧几里得环

```haskell
-- 欧几里得环的性质
class EuclideanRing a where
  euclideanNorm :: a -> Natural
  euclideanDivision :: a -> a -> (a, a)  -- (quotient, remainder)

instance EuclideanRing Integer where
  euclideanNorm (Positive n) = n
  euclideanNorm (Negative n) = n
  euclideanNorm Zero = Zero
  
  euclideanDivision a b = 
    case divide a b of
      Just q -> (q, fromJust (modulo a b))
      Nothing -> error "Division by zero"
    where
      fromJust (Just x) = x
      fromJust Nothing = error "No value"

-- 欧几里得算法
euclideanAlgorithm :: Integer -> Integer -> Integer
euclideanAlgorithm a b = 
  if b == Zero then a 
  else euclideanAlgorithm b (fromJust (modulo a b))
  where
    fromJust (Just x) = x
    fromJust Nothing = error "No value"

-- 扩展欧几里得算法
extendedEuclidean :: Integer -> Integer -> (Integer, Integer, Integer)
extendedEuclidean a b = 
  if b == Zero then (a, Positive (Succ Zero), Zero)
  else let (d, x, y) = extendedEuclidean b (fromJust (modulo a b))
       in (d, y, subtract x (multiply (fromJust (divide a b)) y))
  where
    fromJust (Just x) = x
    fromJust Nothing = error "No value"
```

## 数论函数

### 基本数论函数

```haskell
-- 整数的数论函数
class IntegerNumberTheoreticFunctions a where
  gcd :: a -> a -> a
  lcm :: a -> a -> a
  divisors :: a -> [a]
  isPrime :: a -> Bool
  primeFactors :: a -> [a]
  totient :: a -> a

instance IntegerNumberTheoreticFunctions Integer where
  gcd a b = euclideanAlgorithm (abs a) (abs b)
  
  lcm a b = 
    case (divide (multiply (abs a) (abs b)) (gcd a b)) of
      Just result -> result
      Nothing -> error "Division by zero"
  
  divisors n = 
    let absN = abs n
        positiveDivisors = [Positive d | d <- divisors absN]
        negativeDivisors = [Negative d | d <- divisors absN]
    in if n == Zero then [] else positiveDivisors ++ negativeDivisors
    where
      divisors Zero = []
      divisors (Positive n) = [Positive d | d <- divisors n]
      divisors (Negative n) = [Positive d | d <- divisors n]
  
  isPrime (Positive n) = isPrime n
  isPrime (Negative n) = isPrime n
  isPrime Zero = False
  
  primeFactors n = 
    let absN = abs n
        factors = primeFactors absN
    in if sign n == -1 then map negate factors else factors
    where
      negate (Positive n) = Negative n
      negate (Negative n) = Positive n
      negate Zero = Zero
  
  totient n = 
    let absN = abs n
        result = totient absN
    in if n < Zero then result else result
    where
      totient Zero = Zero
      totient (Positive n) = Positive (totient n)
      totient (Negative n) = Positive (totient n)
```

### 同余理论

```haskell
-- 同余关系
class CongruenceTheory a where
  congruent :: a -> a -> a -> Bool
  congruenceClass :: a -> a -> [a]
  chineseRemainder :: [(a, a)] -> Maybe a

instance CongruenceTheory Integer where
  congruent a b m = 
    case modulo (subtract a b) m of
      Just r -> r == Zero
      Nothing -> False
  
  congruenceClass a m = 
    [a + multiply k m | k <- integers]
    where
      integers = [Positive n | n <- naturals] ++ [Zero] ++ [Negative n | n <- naturals]
      naturals = iterate Succ Zero
  
  chineseRemainder [] = Just Zero
  chineseRemainder [(a, m)] = Just a
  chineseRemainder ((a1, m1):(a2, m2):rest) = 
    case extendedEuclidean m1 m2 of
      (d, x, y) -> 
        if d == Positive (Succ Zero) then
          let solution = add a1 (multiply (multiply x (subtract a2 a1)) m1)
              newModulus = multiply m1 m2
          in chineseRemainder ((solution, newModulus):rest)
        else Nothing
```

## 形式化验证

### 一致性检查

```haskell
-- 检查整数理论的一致性
checkIntegerConsistency :: IO ()
checkIntegerConsistency = do
  putStrLn "=== 整数理论一致性检查 ==="
  
  let a = Positive (Succ (Succ Zero))  -- 2
      b = Negative (Succ Zero)         -- -1
      c = Positive (Succ (Succ (Succ Zero)))  -- 3
  
  -- 检查环性质
  putStrLn $ "加法交换律: " ++ show (addCommutative a b)
  putStrLn $ "加法结合律: " ++ show (addAssociative a b c)
  putStrLn $ "加法单位元: " ++ show (addIdentity a)
  putStrLn $ "加法逆元: " ++ show (addInverse a)
  putStrLn $ "乘法结合律: " ++ show (multiplyAssociative a b c)
  putStrLn $ "乘法分配律: " ++ show (multiplyDistributive a b c)
  
  -- 检查欧几里得环性质
  putStrLn $ "欧几里得范数: " ++ show (euclideanNorm a)
  putStrLn $ "欧几里得除法: " ++ show (euclideanDivision a c)
```

### 完备性检查

```haskell
-- 检查整数理论的完备性
checkIntegerCompleteness :: IO ()
checkIntegerCompleteness = do
  putStrLn "=== 整数理论完备性检查 ==="
  
  -- 检查基本运算的完备性
  let integers = [Zero, Positive (Succ Zero), Negative (Succ Zero)]
      allPairs = [(a, b) | a <- integers, b <- integers]
  
  putStrLn $ "加法运算完备性: " ++ show (all (\(a, b) -> addCommutative a b) allPairs)
  putStrLn $ "乘法运算完备性: " ++ show (all (\(a, b) -> multiplyAssociative a b (Positive (Succ Zero))) allPairs)
  
  -- 检查数论函数
  putStrLn $ "GCD函数完备性: " ++ show (gcd (Positive (Succ (Succ Zero))) (Positive (Succ (Succ (Succ Zero)))) == Positive (Succ Zero))
  putStrLn $ "LCM函数完备性: " ++ show (lcm (Positive (Succ (Succ Zero))) (Positive (Succ (Succ (Succ Zero)))) == Positive (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))
```

### 正确性检查

```haskell
-- 检查整数理论的正确性
checkIntegerCorrectness :: IO ()
checkIntegerCorrectness = do
  putStrLn "=== 整数理论正确性检查 ==="
  
  let a = Positive (Succ (Succ Zero))  -- 2
      b = Negative (Succ Zero)         -- -1
      c = Positive (Succ (Succ (Succ Zero)))  -- 3
  
  -- 检查基本运算
  putStrLn $ "2 + (-1) = 1: " ++ show (add a b == Positive (Succ Zero))
  putStrLn $ "2 * (-1) = -2: " ++ show (multiply a b == Negative (Succ (Succ Zero)))
  putStrLn $ "|(-3)| = 3: " ++ show (abs (Negative (Succ (Succ (Succ Zero)))) == Positive (Succ (Succ (Succ Zero))))
  
  -- 检查数论函数
  putStrLn $ "gcd(6,9) = 3: " ++ show (gcd (Positive (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))) (Positive (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))) == Positive (Succ (Succ (Succ Zero))))
  putStrLn $ "lcm(4,6) = 12: " ++ show (lcm (Positive (Succ (Succ (Succ (Succ Zero))))) (Positive (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))) == Positive (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))))
```

## 应用示例

### 线性同余方程

```haskell
-- 线性同余方程求解
solveLinearCongruence :: Integer -> Integer -> Integer -> Maybe Integer
solveLinearCongruence a b m = 
  case extendedEuclidean a m of
    (d, x, _) -> 
      if congruent (multiply d b) Zero m then
        Just (modulo (multiply x b) m)
      else Nothing
  where
    modulo a m = fromJust (modulo a m)
    fromJust (Just x) = x
    fromJust Nothing = error "No value"

-- 示例：求解 3x ≡ 2 (mod 7)
linearCongruenceExample :: Maybe Integer
linearCongruenceExample = 
  solveLinearCongruence (Positive (Succ (Succ (Succ Zero)))) (Positive (Succ (Succ Zero))) (Positive (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))
```

### 中国剩余定理

```haskell
-- 中国剩余定理的应用
chineseRemainderExample :: Maybe Integer
chineseRemainderExample = 
  chineseRemainder [
    (Positive (Succ Zero), Positive (Succ (Succ (Succ Zero)))),  -- x ≡ 1 (mod 3)
    (Positive (Succ (Succ Zero)), Positive (Succ (Succ (Succ (Succ (Succ Zero)))))),  -- x ≡ 2 (mod 5)
    (Positive (Succ (Succ (Succ Zero))), Positive (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))  -- x ≡ 3 (mod 7)
  ]
```

### 费马小定理

```haskell
-- 费马小定理
fermatLittleTheorem :: Integer -> Integer -> Bool
fermatLittleTheorem p a = 
  if isPrime p && isNonZero a && not (congruent a Zero p)
  then congruent (power a (subtract p (Positive (Succ Zero)))) (Positive (Succ Zero)) p
  else True
  where
    power a Zero = Positive (Succ Zero)
    power a (Positive n) = multiply a (power a (subtract (Positive n) (Positive (Succ Zero))))
    power a (Negative n) = error "Negative exponent not supported for integers"
```

## 总结

整数理论通过形式化方法建立了严格的数学结构：

1. **环结构**：整数构成一个交换环
2. **欧几里得环**：整数构成一个欧几里得环
3. **数论函数**：GCD、LCM、欧拉函数等
4. **同余理论**：模运算和同余关系
5. **中国剩余定理**：同余方程组的求解

通过Haskell的形式化实现，我们可以：

- 严格定义整数的概念和运算
- 验证环性质和欧几里得环性质
- 实现数论算法
- 求解同余方程

这种形式化方法不仅澄清了数学概念，还为数论研究提供了精确的分析工具。

---

**相关链接**：

- [自然数理论](../01-Natural-Numbers.md)
- [有理数理论](../03-Rational-Theory.md)
- [实数理论](../04-Real-Theory.md)
- [复数理论](../05-Complex-Theory.md)
