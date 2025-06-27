# 密码学 - 形式化理论与Haskell实现

## 📋 概述

密码学是研究信息安全技术的学科，包括加密、解密、数字签名、密钥管理等核心技术。本文档从形式化角度建立密码学的完整理论体系。

## 🎯 核心概念

### 1. 密码学基础

#### 形式化定义

**定义 1.1 (密码系统)** 密码系统是一个五元组 $\mathcal{C} = (M, C, K, E, D)$，其中：

- $M$ 是明文空间
- $C$ 是密文空间
- $K$ 是密钥空间
- $E: K \times M \to C$ 是加密函数
- $D: K \times C \to M$ 是解密函数

满足：$\forall k \in K, \forall m \in M, D(k, E(k, m)) = m$

**定义 1.2 (完美保密性)** 密码系统具有完美保密性当且仅当：
$$\forall m_0, m_1 \in M, \forall c \in C, P(M = m_0 | C = c) = P(M = m_1 | C = c)$$

#### Haskell实现

```haskell
{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Cryptography.Core where

import Data.Char (ord, chr)
import Data.List (zipWith)
import System.Random (Random, random, randomR, mkStdGen)
import Data.Bits (xor, shiftL, shiftR, (.&.), (.|.))

-- 密码系统
data Cryptosystem m c k = Cryptosystem
  { encrypt :: k -> m -> c
  , decrypt :: k -> c -> m
  , keySpace :: [k]
  , messageSpace :: [m]
  , cipherSpace :: [c]
  } deriving (Show)

-- 验证密码系统正确性
validateCryptosystem :: (Eq m, Eq c, Eq k) => 
  Cryptosystem m c k -> Bool
validateCryptosystem cs =
  all (\key -> all (\msg -> 
    decrypt cs key (encrypt cs key msg) == msg) 
    cs.messageSpace) cs.keySpace

-- 完美保密性检查
perfectSecrecy :: (Eq m, Eq c, Eq k) => 
  Cryptosystem m c k -> 
  (k -> Double) ->  -- 密钥分布
  (m -> Double) ->  -- 明文分布
  Bool
perfectSecrecy cs keyDist msgDist =
  let allMessages = cs.messageSpace
      allCiphers = cs.cipherSpace
      allKeys = cs.keySpace
      
      -- 计算条件概率
      conditionalProb msg cipher =
        let numerator = sum [keyDist key | key <- allKeys, 
                                         encrypt cs key msg == cipher]
            denominator = sum [keyDist key * msgDist m | key <- allKeys, 
                                                       m <- allMessages,
                                                       encrypt cs key m == cipher]
        in if denominator > 0 then numerator / denominator else 0
      
      -- 检查所有消息对和密文
      checkSecrecy = all (\cipher -> 
        let probs = [conditionalProb msg cipher | msg <- allMessages]
        in all (\p -> abs (p - head probs) < 1e-10) probs) allCiphers
  in checkSecrecy
```

### 2. 对称密码

#### 形式化定义

**定义 1.3 (对称密码)** 对称密码是满足 $E(k, m) = D(k, m)$ 的密码系统。

**定义 1.4 (分组密码)** 分组密码将明文分成固定长度的块进行加密：
$$E: \{0,1\}^n \times \{0,1\}^l \to \{0,1\}^l$$

#### Haskell实现

```haskell
module Cryptography.Symmetric where

import Cryptography.Core
import Data.Bits (xor, rotateL, rotateR)
import Data.Word (Word32, Word64)
import Data.List (foldl')

-- 凯撒密码
caesarCipher :: Int -> String -> String
caesarCipher shift = map (\c -> 
  if c >= 'a' && c <= 'z'
  then chr (((ord c - ord 'a' + shift) `mod` 26) + ord 'a')
  else if c >= 'A' && c <= 'Z'
  then chr (((ord c - ord 'A' + shift) `mod` 26) + ord 'A')
  else c)

-- 维吉尼亚密码
vigenereCipher :: String -> String -> String
vigenereCipher key text = zipWith shift text (cycle key)
  where
    shift c k = 
      if c >= 'a' && c <= 'z'
      then chr (((ord c - ord 'a' + ord k - ord 'a') `mod` 26) + ord 'a')
      else if c >= 'A' && c <= 'Z'
      then chr (((ord c - ord 'A' + ord k - ord 'A') `mod` 26) + ord 'A')
      else c

-- XOR密码
xorCipher :: String -> String -> String
xorCipher key text = zipWith xor text (cycle key)
  where
    xor c k = chr (ord c `xor` ord k)

-- 简单分组密码
data BlockCipher = BlockCipher
  { blockSize :: Int
  , rounds :: Int
  , roundKeys :: [Word32]
  } deriving (Show)

-- 创建分组密码
createBlockCipher :: Int -> Int -> Word32 -> BlockCipher
createBlockCipher blockSize rounds seed =
  let gen = mkStdGen (fromIntegral seed)
      roundKeys = take rounds [fst (randomR (0, maxBound) gen) | _ <- [1..]]
  in BlockCipher blockSize rounds roundKeys

-- Feistel网络
feistelNetwork :: (Word32 -> Word32 -> Word32) -> Word32 -> Word32 -> Word32 -> Word32
feistelNetwork roundFunction key left right =
  let newLeft = right
      newRight = left `xor` roundFunction key right
  in (newLeft, newRight)

-- 简化的轮函数
simpleRoundFunction :: Word32 -> Word32 -> Word32
simpleRoundFunction key data_ = 
  rotateL (data_ + key) 7 `xor` key

-- 加密分组
encryptBlock :: BlockCipher -> Word64 -> Word64
encryptBlock cipher block =
  let left = fromIntegral (block `shiftR` 32)
      right = fromIntegral (block .&. 0xFFFFFFFF)
      (finalLeft, finalRight) = foldl' 
        (\(l, r) key -> feistelNetwork simpleRoundFunction key l r)
        (left, right) cipher.roundKeys
  in (fromIntegral finalLeft `shiftL` 32) .|. fromIntegral finalRight

-- 解密分组
decryptBlock :: BlockCipher -> Word64 -> Word64
decryptBlock cipher block =
  let left = fromIntegral (block `shiftR` 32)
      right = fromIntegral (block .&. 0xFFFFFFFF)
      (finalLeft, finalRight) = foldl' 
        (\(l, r) key -> feistelNetwork simpleRoundFunction key l r)
        (left, right) (reverse cipher.roundKeys)
  in (fromIntegral finalLeft `shiftL` 32) .|. fromIntegral finalRight

-- 分组密码模式
data BlockMode = 
  ECB |  -- 电子密码本模式
  CBC |  -- 密码分组链接模式
  CFB |  -- 密文反馈模式
  OFB   -- 输出反馈模式
  deriving (Show)

-- ECB模式加密
ecbEncrypt :: BlockCipher -> [Word64] -> [Word64]
ecbEncrypt cipher = map (encryptBlock cipher)

-- CBC模式加密
cbcEncrypt :: BlockCipher -> Word64 -> [Word64] -> [Word64]
cbcEncrypt cipher iv plaintext =
  let encryptWithIV prevCipher block =
        let xored = block `xor` prevCipher
            ciphertext = encryptBlock cipher xored
        in (ciphertext, ciphertext)
      (ciphertexts, _) = foldl' 
        (\(results, prev) block -> 
          let (ciphertext, newPrev) = encryptWithIV prev block
          in (results ++ [ciphertext], newPrev))
        ([], iv) plaintext
  in ciphertexts

-- CBC模式解密
cbcDecrypt :: BlockCipher -> Word64 -> [Word64] -> [Word64]
cbcDecrypt cipher iv ciphertext =
  let decryptWithIV prevCipher ciphertext =
        let decrypted = decryptBlock cipher ciphertext
            plaintext = decrypted `xor` prevCipher
        in plaintext
      plaintexts = zipWith decryptWithIV (iv : ciphertext) ciphertext
  in plaintexts
```

### 3. 公钥密码

#### 形式化定义

**定义 1.5 (公钥密码)** 公钥密码系统包含：

- 密钥生成算法：$Gen(1^n) \to (pk, sk)$
- 加密算法：$Enc(pk, m) \to c$
- 解密算法：$Dec(sk, c) \to m$

**定义 1.6 (RSA密码)** RSA密码基于大整数分解问题：

- 选择两个大素数 $p, q$
- 计算 $n = pq, \phi(n) = (p-1)(q-1)$
- 选择 $e$ 使得 $\gcd(e, \phi(n)) = 1$
- 计算 $d = e^{-1} \bmod \phi(n)$
- 公钥：$(n, e)$，私钥：$(n, d)$

#### Haskell实现

```haskell
module Cryptography.PublicKey where

import Cryptography.Core
import Data.List (find)
import System.Random (randomR, mkStdGen)

-- RSA密钥对
data RSAKeyPair = RSAKeyPair
  { publicKey :: (Integer, Integer)  -- (n, e)
  , privateKey :: (Integer, Integer) -- (n, d)
  } deriving (Show)

-- 生成RSA密钥对
generateRSAKeys :: Integer -> Integer -> Integer -> RSAKeyPair
generateRSAKeys p q e =
  let n = p * q
      phi = (p - 1) * (q - 1)
      d = modInverse e phi
  in RSAKeyPair (n, e) (n, d)

-- 模逆元计算
modInverse :: Integer -> Integer -> Integer
modInverse a m = 
  let (x, _, _) = extendedGCD a m
  in if x < 0 then x + m else x

-- 扩展欧几里得算法
extendedGCD :: Integer -> Integer -> (Integer, Integer, Integer)
extendedGCD a b
  | b == 0 = (a, 1, 0)
  | otherwise = 
      let (d, x, y) = extendedGCD b (a `mod` b)
      in (d, y, x - (a `div` b) * y)

-- RSA加密
rsaEncrypt :: RSAKeyPair -> Integer -> Integer
rsaEncrypt keys message =
  let (n, e) = publicKey keys
  in modPow message e n

-- RSA解密
rsaDecrypt :: RSAKeyPair -> Integer -> Integer
rsaDecrypt keys ciphertext =
  let (n, d) = privateKey keys
  in modPow ciphertext d n

-- 模幂运算
modPow :: Integer -> Integer -> Integer -> Integer
modPow base exponent modulus = 
  modPowHelper base exponent modulus 1
  where
    modPowHelper _ 0 _ result = result
    modPowHelper base exponent modulus result =
      let newResult = if odd exponent 
                      then (result * base) `mod` modulus 
                      else result
          newBase = (base * base) `mod` modulus
          newExponent = exponent `div` 2
      in modPowHelper newBase newExponent modulus newResult

-- 检查是否为素数
isPrime :: Integer -> Bool
isPrime n
  | n < 2 = False
  | n == 2 = True
  | even n = False
  | otherwise = millerRabinTest n 10

-- Miller-Rabin素性测试
millerRabinTest :: Integer -> Int -> Bool
millerRabinTest n k =
  let (s, d) = factorize2 n
      testWitness a =
        let x = modPow a d n
        in if x == 1 || x == n - 1
           then True
           else checkWitness x (s - 1)
      checkWitness x 0 = False
      checkWitness x r =
        let newX = (x * x) `mod` n
        in if newX == n - 1
           then True
           else if newX == 1
           then False
           else checkWitness newX (r - 1)
      witnesses = take k [2..n-1]
  in all testWitness witnesses

-- 分解2的幂次
factorize2 :: Integer -> (Integer, Integer)
factorize2 n = factorize2Helper n 0
  where
    factorize2Helper n s
      | odd n = (s, n)
      | otherwise = factorize2Helper (n `div` 2) (s + 1)

-- 生成大素数
generatePrime :: Integer -> Integer -> Integer
generatePrime minVal maxVal =
  let gen = mkStdGen 42
      candidates = [minVal + 2*i | i <- [0..(maxVal - minVal) `div` 2]]
      prime = head [c | c <- candidates, isPrime c]
  in prime

-- ElGamal密码系统
data ElGamalKeys = ElGamalKeys
  { publicKey :: (Integer, Integer, Integer)  -- (p, g, y)
  , privateKey :: Integer                     -- x
  } deriving (Show)

-- 生成ElGamal密钥
generateElGamalKeys :: Integer -> Integer -> Integer -> ElGamalKeys
generateElGamalKeys p g x =
  let y = modPow g x p
  in ElGamalKeys (p, g, y) x

-- ElGamal加密
elGamalEncrypt :: ElGamalKeys -> Integer -> (Integer, Integer)
elGamalEncrypt keys message =
  let (p, g, y) = publicKey keys
      k = randomR (2, p-2) (mkStdGen 42)  -- 简化：使用固定种子
      c1 = modPow g k p
      c2 = (message * modPow y k p) `mod` p
  in (c1, c2)

-- ElGamal解密
elGamalDecrypt :: ElGamalKeys -> (Integer, Integer) -> Integer
elGamalDecrypt keys (c1, c2) =
  let (p, _, _) = publicKey keys
      x = privateKey keys
      s = modPow c1 x p
      sInv = modInverse s p
  in (c2 * sInv) `mod` p
```

### 4. 哈希函数

#### 形式化定义

**定义 1.7 (哈希函数)** 哈希函数 $H: \{0,1\}^* \to \{0,1\}^n$ 满足：

- 抗碰撞性：难以找到 $x \neq y$ 使得 $H(x) = H(y)$
- 抗第二原像性：给定 $x$，难以找到 $y \neq x$ 使得 $H(x) = H(y)$
- 抗原像性：给定 $h$，难以找到 $x$ 使得 $H(x) = h$

#### Haskell实现

```haskell
module Cryptography.Hash where

import Data.Bits (xor, rotateL, rotateR, (.&.), (.|.))
import Data.Word (Word32, Word64)
import Data.Char (ord)

-- 简单哈希函数
simpleHash :: String -> Word32
simpleHash = foldl hashStep 0
  where
    hashStep acc char = 
      let charVal = fromIntegral (ord char)
      in rotateL acc 5 `xor` charVal

-- SHA-1哈希函数（简化版本）
data SHA1State = SHA1State
  { h0 :: Word32
  , h1 :: Word32
  , h2 :: Word32
  , h3 :: Word32
  , h4 :: Word32
  } deriving (Show)

-- 初始SHA-1状态
initialSHA1State :: SHA1State
initialSHA1State = SHA1State 0x67452301 0xEFCDAB89 0x98BADCFE 0x10325476 0xC3D2E1F0

-- SHA-1常量
sha1Constants :: [Word32]
sha1Constants = [0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xCA62C1D6]

-- SHA-1函数
sha1F :: Int -> Word32 -> Word32 -> Word32 -> Word32
sha1F t b c d
  | t < 20 = (b .&. c) .|. ((complement b) .&. d)
  | t < 40 = b `xor` c `xor` d
  | t < 60 = (b .&. c) .|. (b .&. d) .|. (c .&. d)
  | otherwise = b `xor` c `xor` d

-- SHA-1哈希
sha1 :: String -> String
sha1 message =
  let -- 预处理
      paddedMessage = padMessage message
      -- 处理消息块
      finalState = processBlocks paddedMessage initialSHA1State
      -- 生成哈希值
      hashValue = formatHash finalState
  in hashValue

-- 消息填充
padMessage :: String -> [Word32]
padMessage message =
  let messageLength = length message * 8
      messageWords = stringToWords message
      paddingLength = 512 - ((messageLength + 64) `mod` 512)
      padding = replicate (paddingLength `div` 8) 0
      lengthWords = [fromIntegral (messageLength `shiftR` 32), 
                     fromIntegral (messageLength .&. 0xFFFFFFFF)]
  in messageWords ++ padding ++ lengthWords

-- 字符串转字数组
stringToWords :: String -> [Word32]
stringToWords = chunkToWords . map (fromIntegral . ord)

-- 字节数组转字数组
chunkToWords :: [Word32] -> [Word32]
chunkToWords [] = []
chunkToWords bytes =
  let word = foldl (\acc byte -> (acc `shiftL` 8) .|. byte) 0 (take 4 bytes)
  in word : chunkToWords (drop 4 bytes)

-- 处理消息块
processBlocks :: [Word32] -> SHA1State -> SHA1State
processBlocks [] state = state
processBlocks words state =
  let block = take 16 words
      newState = processBlock block state
  in processBlocks (drop 16 words) newState

-- 处理单个块
processBlock :: [Word32] -> SHA1State -> SHA1State
processBlock block state =
  let -- 扩展消息
      extendedBlock = extendBlock block
      -- 初始化工作变量
      (a, b, c, d, e) = (state.h0, state.h1, state.h2, state.h3, state.h4)
      -- 主循环
      finalState = foldl processRound (a, b, c, d, e) (zip [0..79] extendedBlock)
      (a', b', c', d', e') = finalState
  in SHA1State (state.h0 + a') (state.h1 + b') (state.h2 + c') (state.h3 + d') (state.h4 + e')

-- 扩展消息块
extendBlock :: [Word32] -> [Word32]
extendBlock block =
  let initial = block
      extended = [w (i-16) `xor` w (i-14) `xor` w (i-8) `xor` w (i-3) | i <- [16..79]]
      w i = if i < 16 then block !! i else extended !! (i - 16)
  in initial ++ extended

-- 处理轮
processRound :: (Word32, Word32, Word32, Word32, Word32) -> (Int, Word32) -> (Word32, Word32, Word32, Word32, Word32)
processRound (a, b, c, d, e) (t, w) =
  let temp = rotateL a 5 + sha1F t b c d + e + w + sha1Constants !! (t `div` 20)
      newA = temp
      newB = a
      newC = rotateL b 30
      newD = c
      newE = d
  in (newA, newB, newC, newD, newE)

-- 格式化哈希值
formatHash :: SHA1State -> String
formatHash state =
  let values = [state.h0, state.h1, state.h2, state.h3, state.h4]
      hexString = concatMap (\w -> printf "%08x" w) values
  in hexString

-- 简化的printf函数
printf :: String -> Word32 -> String
printf format value = showHex value ""
  where
    showHex :: Word32 -> String -> String
    showHex 0 acc = if null acc then "0" else acc
    showHex n acc = 
      let digit = n .&. 0xF
          char = if digit < 10 then chr (ord '0' + fromIntegral digit)
                 else chr (ord 'a' + fromIntegral digit - 10)
      in showHex (n `shiftR` 4) (char : acc)
```

### 5. 数字签名

#### 形式化定义

**定义 1.8 (数字签名)** 数字签名方案包含：

- 密钥生成：$Gen(1^n) \to (pk, sk)$
- 签名：$Sign(sk, m) \to \sigma$
- 验证：$Verify(pk, m, \sigma) \to \{0,1\}$

**定义 1.9 (RSA签名)** RSA签名：

- 签名：$\sigma = m^d \bmod n$
- 验证：$m = \sigma^e \bmod n$

#### Haskell实现

```haskell
module Cryptography.DigitalSignature where

import Cryptography.PublicKey
import Cryptography.Hash
import Data.Char (ord)

-- 数字签名
data DigitalSignature = DigitalSignature
  { message :: String
  , signature :: Integer
  , publicKey :: (Integer, Integer)
  } deriving (Show)

-- RSA签名
rsaSign :: RSAKeyPair -> String -> Integer
rsaSign keys message =
  let hashValue = simpleHash message
      (n, d) = privateKey keys
  in modPow (fromIntegral hashValue) d n

-- RSA签名验证
rsaVerify :: RSAKeyPair -> String -> Integer -> Bool
rsaVerify keys message signature =
  let hashValue = simpleHash message
      (n, e) = publicKey keys
      decrypted = modPow signature e n
  in fromIntegral hashValue == decrypted

-- DSA签名（简化版本）
data DSASignature = DSASignature
  { r :: Integer
  , s :: Integer
  } deriving (Show)

-- DSA密钥
data DSAKeys = DSAKeys
  { publicKey :: (Integer, Integer, Integer)  -- (p, q, g, y)
  , privateKey :: Integer                     -- x
  } deriving (Show)

-- 生成DSA密钥
generateDSAKeys :: Integer -> Integer -> Integer -> Integer -> DSAKeys
generateDSAKeys p q g x =
  let y = modPow g x p
  in DSAKeys (p, q, g, y) x

-- DSA签名
dsaSign :: DSAKeys -> String -> DSASignature
dsaSign keys message =
  let (p, q, g, y) = publicKey keys
      x = privateKey keys
      hashValue = simpleHash message
      k = randomR (1, q-1) (mkStdGen 42)  -- 简化：使用固定种子
      r = modPow g k p `mod` q
      kInv = modInverse k q
      s = (kInv * (hashValue + x * r)) `mod` q
  in DSASignature r s

-- DSA验证
dsaVerify :: DSAKeys -> String -> DSASignature -> Bool
dsaVerify keys message signature =
  let (p, q, g, y) = publicKey keys
      hashValue = simpleHash message
      w = modInverse signature.s q
      u1 = (hashValue * w) `mod` q
      u2 = (signature.r * w) `mod` q
      v = ((modPow g u1 p * modPow y u2 p) `mod` p) `mod` q
  in v == signature.r

-- 椭圆曲线数字签名（简化版本）
data ECDSASignature = ECDSASignature
  { r :: Integer
  , s :: Integer
  } deriving (Show)

-- 椭圆曲线点
data ECPoint = ECPoint
  { x :: Integer
  , y :: Integer
  } deriving (Show, Eq)

-- 无穷远点
infinity :: ECPoint
infinity = ECPoint 0 0

-- 椭圆曲线参数
data ECCurve = ECCurve
  { p :: Integer  -- 有限域模数
  , a :: Integer  -- 曲线参数a
  , b :: Integer  -- 曲线参数b
  , n :: Integer  -- 基点阶数
  , g :: ECPoint  -- 基点
  } deriving (Show)

-- 点加法
ecAdd :: ECCurve -> ECPoint -> ECPoint -> ECPoint
ecAdd curve p1 p2
  | p1 == infinity = p2
  | p2 == infinity = p1
  | p1 == p2 = ecDouble curve p1
  | otherwise = ecAddDifferent curve p1 p2

-- 点倍乘
ecDouble :: ECCurve -> ECPoint -> ECPoint
ecDouble curve point
  | point == infinity = infinity
  | point.y == 0 = infinity
  | otherwise =
      let lambda = ((3 * point.x * point.x + curve.a) * modInverse (2 * point.y) curve.p) `mod` curve.p
          x3 = (lambda * lambda - 2 * point.x) `mod` curve.p
          y3 = (lambda * (point.x - x3) - point.y) `mod` curve.p
      in ECPoint x3 y3

-- 不同点加法
ecAddDifferent :: ECCurve -> ECPoint -> ECPoint -> ECPoint
ecAddDifferent curve p1 p2 =
  let lambda = ((p2.y - p1.y) * modInverse (p2.x - p1.x) curve.p) `mod` curve.p
      x3 = (lambda * lambda - p1.x - p2.x) `mod` curve.p
      y3 = (lambda * (p1.x - x3) - p1.y) `mod` curve.p
  in ECPoint x3 y3

-- 标量乘法
ecScalarMultiply :: ECCurve -> Integer -> ECPoint -> ECPoint
ecScalarMultiply curve k point =
  let multiplyHelper 0 _ = infinity
      multiplyHelper k point
        | odd k = ecAdd curve point (multiplyHelper (k `div` 2) (ecDouble curve point))
        | otherwise = multiplyHelper (k `div` 2) (ecDouble curve point)
  in multiplyHelper k point

-- ECDSA签名
ecdsaSign :: ECCurve -> Integer -> String -> ECDSASignature
ecdsaSign curve privateKey message =
  let hashValue = simpleHash message
      k = randomR (1, curve.n-1) (mkStdGen 42)  -- 简化：使用固定种子
      rPoint = ecScalarMultiply curve k curve.g
      r = rPoint.x `mod` curve.n
      kInv = modInverse k curve.n
      s = (kInv * (hashValue + privateKey * r)) `mod` curve.n
  in ECDSASignature r s

-- ECDSA验证
ecdsaVerify :: ECCurve -> ECPoint -> String -> ECDSASignature -> Bool
ecdsaVerify curve publicKey message signature =
  let hashValue = simpleHash message
      w = modInverse signature.s curve.n
      u1 = (hashValue * w) `mod` curve.n
      u2 = (signature.r * w) `mod` curve.n
      point1 = ecScalarMultiply curve u1 curve.g
      point2 = ecScalarMultiply curve u2 publicKey
      v = ecAdd curve point1 point2
  in v.x `mod` curve.n == signature.r
```

## 🔬 高级密码技术

### 1. 零知识证明

#### 形式化定义

**定义 1.10 (零知识证明)** 零知识证明系统满足：

- **完备性**：如果陈述为真，诚实验证者总是接受诚实验证者的证明
- **可靠性**：如果陈述为假，任何不诚实的验证者被诚实验证者说服的概率可忽略
- **零知识性**：验证者除了陈述为真外，不获得任何其他信息

#### Haskell实现

```haskell
module Cryptography.ZeroKnowledge where

import Cryptography.PublicKey
import System.Random (randomR, mkStdGen)

-- Schnorr身份识别协议
data SchnorrProtocol = SchnorrProtocol
  { p :: Integer  -- 大素数
  , q :: Integer  -- p-1的大素因子
  , g :: Integer  -- 生成元
  , publicKey :: Integer  -- y = g^x mod p
  , privateKey :: Integer -- x
  } deriving (Show)

-- 创建Schnorr协议
createSchnorrProtocol :: Integer -> Integer -> Integer -> SchnorrProtocol
createSchnorrProtocol p q g =
  let x = randomR (1, q-1) (mkStdGen 42)  -- 简化：使用固定种子
      y = modPow g x p
  in SchnorrProtocol p q g y x

-- 证明者步骤1：承诺
schnorrCommit :: SchnorrProtocol -> (Integer, Integer)
schnorrCommit protocol =
  let r = randomR (1, protocol.q-1) (mkStdGen 42)  -- 简化：使用固定种子
      t = modPow protocol.g r protocol.p
  in (t, r)

-- 验证者步骤：挑战
schnorrChallenge :: Integer -> Integer
schnorrChallenge q = randomR (0, q-1) (mkStdGen 42)  -- 简化：使用固定种子

-- 证明者步骤2：响应
schnorrResponse :: SchnorrProtocol -> Integer -> Integer -> Integer
schnorrResponse protocol r c =
  (r + protocol.privateKey * c) `mod` protocol.q

-- 验证者验证
schnorrVerify :: SchnorrProtocol -> Integer -> Integer -> Integer -> Bool
schnorrVerify protocol t c s =
  let left = modPow protocol.g s protocol.p
      right = (t * modPow protocol.publicKey c protocol.p) `mod` protocol.p
  in left == right

-- 完整Schnorr协议执行
executeSchnorrProtocol :: SchnorrProtocol -> Bool
executeSchnorrProtocol protocol =
  let (t, r) = schnorrCommit protocol
      c = schnorrChallenge protocol.q
      s = schnorrResponse protocol r c
  in schnorrVerify protocol t c s
```

### 2. 同态加密

#### 形式化定义

**定义 1.11 (同态加密)** 同态加密允许在密文上进行计算：
$$E(m_1) \otimes E(m_2) = E(m_1 \oplus m_2)$$

其中 $\otimes$ 是密文运算，$\oplus$ 是明文运算。

#### Haskell实现

```haskell
module Cryptography.Homomorphic where

import Cryptography.PublicKey
import System.Random (randomR, mkStdGen)

-- 简单同态加密（基于RSA）
data HomomorphicRSA = HomomorphicRSA
  { publicKey :: (Integer, Integer)  -- (n, e)
  , privateKey :: (Integer, Integer) -- (n, d)
  } deriving (Show)

-- 创建同态RSA
createHomomorphicRSA :: Integer -> Integer -> Integer -> HomomorphicRSA
createHomomorphicRSA p q e =
  let n = p * q
      phi = (p - 1) * (q - 1)
      d = modInverse e phi
  in HomomorphicRSA (n, e) (n, d)

-- 加密
homomorphicEncrypt :: HomomorphicRSA -> Integer -> Integer
homomorphicEncrypt rsa message =
  let (n, e) = publicKey rsa
  in modPow message e n

-- 解密
homomorphicDecrypt :: HomomorphicRSA -> Integer -> Integer
homomorphicDecrypt rsa ciphertext =
  let (n, d) = privateKey rsa
  in modPow ciphertext d n

-- 同态乘法
homomorphicMultiply :: HomomorphicRSA -> Integer -> Integer -> Integer
homomorphicMultiply rsa c1 c2 =
  let (n, _) = publicKey rsa
  in (c1 * c2) `mod` n

-- 同态加法（使用乘法模拟）
homomorphicAdd :: HomomorphicRSA -> Integer -> Integer -> Integer
homomorphicAdd rsa c1 c2 =
  let (n, e) = publicKey rsa
      -- 使用乘法模拟加法：E(m1 + m2) = E(m1) * E(m2) mod n
      result = (c1 * c2) `mod` n
  in result

-- 验证同态性质
verifyHomomorphicProperty :: HomomorphicRSA -> Integer -> Integer -> Bool
verifyHomomorphicRSA rsa m1 m2 =
  let c1 = homomorphicEncrypt rsa m1
      c2 = homomorphicEncrypt rsa m2
      -- 同态乘法
      cMult = homomorphicMultiply rsa c1 c2
      mMult = homomorphicDecrypt rsa cMult
      expectedMult = (m1 * m2) `mod` (fst (publicKey rsa))
      -- 同态加法
      cAdd = homomorphicAdd rsa c1 c2
      mAdd = homomorphicDecrypt rsa cAdd
      expectedAdd = (m1 + m2) `mod` (fst (publicKey rsa))
  in mMult == expectedMult && mAdd == expectedAdd
```

## 📊 密码分析

### 1. 攻击方法

```haskell
module Cryptography.Cryptanalysis where

import Cryptography.Symmetric
import Cryptography.PublicKey
import Data.List (find, group, sort)
import Data.Char (ord, chr)

-- 频率分析
frequencyAnalysis :: String -> [(Char, Int)]
frequencyAnalysis text =
  let charCounts = [(char, length (filter (== char) text)) | char <- nub text]
  in sortBy (comparing (negate . snd)) charCounts

-- 去重
nub :: (Eq a) => [a] -> [a]
nub [] = []
nub (x:xs) = x : nub (filter (/= x) xs)

-- 排序
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy _ [] = []
sortBy cmp (x:xs) = 
  let smaller = sortBy cmp [a | a <- xs, cmp a x <= EQ]
      bigger = sortBy cmp [a | a <- xs, cmp a x > EQ]
  in smaller ++ [x] ++ bigger

-- 比较函数
comparing :: (Ord a) => (b -> a) -> b -> b -> Ordering
comparing f x y = compare (f x) (f y)

-- 暴力破解凯撒密码
bruteForceCaesar :: String -> [(Int, String)]
bruteForceCaesar ciphertext =
  [(shift, caesarCipher shift ciphertext) | shift <- [0..25]]

-- 维吉尼亚密码破解
vigenereCrack :: String -> String
vigenereCrack ciphertext =
  let -- 找到密钥长度
      keyLength = findKeyLength ciphertext
      -- 按密钥长度分组
      groups = groupByKeyLength ciphertext keyLength
      -- 对每组进行频率分析
      keyChars = map findKeyChar groups
  in keyChars

-- 找到密钥长度
findKeyLength :: String -> Int
findKeyLength ciphertext =
  let maxLength = min 20 (length ciphertext `div` 2)
      coincidences = [(len, countCoincidences ciphertext len) | len <- [1..maxLength]]
  in fst $ maximumBy (comparing snd) coincidences

-- 计算重合指数
countCoincidences :: String -> Int -> Int
countCoincidences text len =
  let groups = groupByKeyLength text len
      coincidenceScores = map calculateCoincidence groups
  in sum coincidenceScores

-- 按密钥长度分组
groupByKeyLength :: String -> Int -> [String]
groupByKeyLength text len =
  [takeEvery len (drop i text) | i <- [0..len-1]]

-- 每隔n个取一个元素
takeEvery :: Int -> String -> String
takeEvery _ [] = []
takeEvery n (x:xs) = x : takeEvery n (drop (n-1) xs)

-- 计算重合指数
calculateCoincidence :: String -> Int
calculateCoincidence text =
  let charCounts = [(char, length (filter (== char) text)) | char <- nub text]
      total = length text
      coincidence = sum [count * (count - 1) | (_, count) <- charCounts]
  in coincidence

-- 找到密钥字符
findKeyChar :: String -> Char
findKeyChar group =
  let frequencies = frequencyAnalysis group
      englishFreq = "ETAOIN SHRDLU"
      bestShift = findBestShift frequencies englishFreq
  in chr (ord 'A' + bestShift)

-- 找到最佳移位
findBestShift :: [(Char, Int)] -> String -> Int
findBestShift frequencies englishFreq =
  let shifts = [0..25]
      scores = [(shift, calculateScore frequencies englishFreq shift) | shift <- shifts]
  in fst $ maximumBy (comparing snd) scores

-- 计算分数
calculateScore :: [(Char, Int)] -> String -> Int -> Int
calculateScore frequencies englishFreq shift =
  let shiftedFreq = [(chr ((ord char - ord 'A' + shift) `mod` 26 + ord 'A'), count) | 
                     (char, count) <- frequencies]
      score = sum [count | (char, count) <- shiftedFreq, char `elem` englishFreq]
  in score

-- 最大值
maximumBy :: (a -> a -> Ordering) -> [a] -> a
maximumBy _ [] = error "maximumBy: empty list"
maximumBy cmp (x:xs) = foldl (\max x -> if cmp x max > EQ then x else max) x xs

-- RSA小指数攻击
rsaSmallExponentAttack :: (Integer, Integer) -> Integer -> Maybe Integer
rsaSmallExponentAttack (n, e) ciphertext =
  let maxM = ceiling (fromIntegral n ** (1/fromIntegral e))
      candidates = [m | m <- [0..maxM], modPow m e n == ciphertext]
  in if null candidates then Nothing else Just (head candidates)

-- 中间相遇攻击
meetInTheMiddle :: (Integer -> Integer) -> (Integer -> Integer) -> Integer -> Maybe (Integer, Integer)
meetInTheMiddle f g target =
  let maxVal = 1000000  -- 限制搜索空间
      fValues = [(f x, x) | x <- [0..maxVal]]
      gValues = [(g x, x) | x <- [0..maxVal]]
      matches = [(x, y) | (fx, x) <- fValues, (gy, y) <- gValues, fx == gy]
  in if null matches then Nothing else Just (head matches)
```

## 📚 形式化证明

### 定理 1.1: RSA的安全性

**定理** RSA的安全性基于大整数分解问题的困难性。

**证明**：

1. 如果攻击者能够分解 $n = pq$，则可以计算 $\phi(n) = (p-1)(q-1)$
2. 利用扩展欧几里得算法计算 $d = e^{-1} \bmod \phi(n)$
3. 因此，RSA的安全性等价于大整数分解问题的困难性

### 定理 1.2: 完美保密性

**定理** 一次一密具有完美保密性。

**证明**：

1. 对于任意明文 $m$ 和密文 $c$，存在唯一的密钥 $k = m \oplus c$
2. 由于密钥是随机均匀分布的，$P(K = k) = \frac{1}{|K|}$
3. 因此 $P(M = m | C = c) = P(M = m) = \frac{1}{|M|}$
4. 对所有明文 $m$ 都成立，满足完美保密性

## 🔗 相关链接

- [网络安全](./02-Network-Security.md)
- [软件安全](./03-Software-Security.md)
- [隐私技术](./04-Privacy-Technology.md)
- [数学基础](../02-Formal-Science/01-Mathematical-Foundations/01-Set-Theory.md)

---

*本文档建立了密码学的完整形式化理论体系，包含严格的数学定义、Haskell实现和形式化证明。*
