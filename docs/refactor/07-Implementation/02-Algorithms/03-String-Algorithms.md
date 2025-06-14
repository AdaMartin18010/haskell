# 字符串算法 - 形式化理论与Haskell实现

## 📋 概述

字符串算法是处理文本数据的基础算法，广泛应用于文本搜索、模式匹配、数据压缩等领域。本文档从形式化理论的角度分析各种字符串算法，并提供完整的Haskell实现。

## 🎯 形式化定义

### 字符串的基本概念

#### 字符串的数学定义

给定字母表 $\Sigma$，字符串是 $\Sigma^*$ 中的元素，即字母表上所有有限序列的集合。

**形式化定义**：
- **字母表**：$\Sigma = \{a_1, a_2, \ldots, a_k\}$
- **字符串**：$s = s_1s_2\ldots s_n$，其中 $s_i \in \Sigma$
- **长度**：$|s| = n$
- **空字符串**：$\epsilon$，$|\epsilon| = 0$

#### 字符串操作

1. **连接**：$s \cdot t = s_1s_2\ldots s_n t_1t_2\ldots t_m$
2. **子串**：$s[i:j] = s_i s_{i+1}\ldots s_{j-1}$
3. **前缀**：$s[0:i]$ 是 $s$ 的前缀
4. **后缀**：$s[i:n]$ 是 $s$ 的后缀

## 🔧 Haskell实现

### 基础类型定义

```haskell
{-# LANGUAGE TypeFamilies, FlexibleContexts, MultiParamTypeClasses #-}

import Data.List (isPrefixOf, isSuffixOf, findIndex)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Text as T
import qualified Data.ByteString as BS

-- 字符串类型类
class StringLike s where
    type CharType s :: *
    empty :: s
    length :: s -> Int
    head :: s -> Maybe (CharType s)
    tail :: s -> s
    cons :: CharType s -> s -> s
    append :: s -> s -> s
    substring :: s -> Int -> Int -> s
    index :: s -> Int -> Maybe (CharType s)

-- 字符串算法结果类型
data StringAlgorithmResult a = StringAlgorithmResult
    { result :: a
    , comparisons :: Int
    , time :: Double
    , memory :: Int
    }

-- 字符串算法类型类
class StringAlgorithm alg where
    type Input alg :: *
    type Output alg :: *
    execute :: alg -> Input alg -> Output alg
    algorithmName :: alg -> String
    complexity :: alg -> String
```

### 1. 字符串匹配算法 (KMP)

#### 形式化定义

KMP算法是一种高效的字符串匹配算法，利用模式串的自身信息来避免不必要的比较。

**算法描述**：
1. 计算模式串的失败函数（next数组）
2. 使用失败函数进行匹配，避免回溯

**失败函数定义**：
$next[i] = \max\{k : 0 \leq k < i \land P[0:k] = P[i-k:i]\}$

#### Haskell实现

```haskell
-- KMP算法实现
kmpSearch :: String -> String -> [Int]
kmpSearch pattern text = 
    let next = computeNext pattern
    in kmpSearch' pattern text next 0 0 []

kmpSearch' :: String -> String -> [Int] -> Int -> Int -> [Int] -> [Int]
kmpSearch' pattern text next i j matches
  | i >= length text = matches
  | j == length pattern = 
      let newMatches = matches ++ [i - j]
          newJ = next !! (j - 1)
      in kmpSearch' pattern text next i newJ newMatches
  | i < length text && j < length pattern && text !! i == pattern !! j = 
      kmpSearch' pattern text next (i + 1) (j + 1) matches
  | j > 0 = 
      let newJ = next !! (j - 1)
      in kmpSearch' pattern text next i newJ matches
  | otherwise = kmpSearch' pattern text next (i + 1) 0 matches

-- 计算失败函数
computeNext :: String -> [Int]
computeNext pattern = 
    let n = length pattern
        next = replicate n 0
    in computeNext' pattern next 1 0

computeNext' :: String -> [Int] -> Int -> Int -> [Int]
computeNext' pattern next i j
  | i >= length pattern = next
  | j > 0 && pattern !! i /= pattern !! j = 
      computeNext' pattern next i (next !! (j - 1))
  | pattern !! i == pattern !! j = 
      let newNext = next // [(i, j + 1)]
      in computeNext' pattern newNext (i + 1) (j + 1)
  | otherwise = 
      let newNext = next // [(i, 0)]
      in computeNext' pattern newNext (i + 1) 0

-- 数组更新操作
(//) :: [a] -> [(Int, a)] -> [a]
xs // updates = 
    let updateMap = Map.fromList updates
    in [if i `Map.member` updateMap then updateMap Map.! i else x 
        | (i, x) <- zip [0..] xs]

-- 带统计的KMP
kmpSearchWithStats :: String -> String -> StringAlgorithmResult [Int]
kmpSearchWithStats pattern text = StringAlgorithmResult
    { result = result
    , comparisons = compCount
    , time = 0.0
    , memory = memory
    }
  where
    (result, compCount, memory) = kmpSearchStats pattern text

kmpSearchStats :: String -> String -> ([Int], Int, Int)
kmpSearchStats pattern text = 
    let next = computeNext pattern
    in kmpSearchStats' pattern text next 0 0 [] 0 0

kmpSearchStats' :: String -> String -> [Int] -> Int -> Int -> [Int] -> Int -> Int -> ([Int], Int, Int)
kmpSearchStats' pattern text next i j matches comps mem
  | i >= length text = (matches, comps, mem)
  | j == length pattern = 
      let newMatches = matches ++ [i - j]
          newJ = next !! (j - 1)
          newComps = comps + 1
          newMem = mem + 1
      in kmpSearchStats' pattern text next i newJ newMatches newComps newMem
  | i < length text && j < length pattern && text !! i == pattern !! j = 
      let newComps = comps + 1
          newMem = mem + 1
      in kmpSearchStats' pattern text next (i + 1) (j + 1) matches newComps newMem
  | j > 0 = 
      let newJ = next !! (j - 1)
          newComps = comps + 1
      in kmpSearchStats' pattern text next i newJ matches newComps mem
  | otherwise = 
      let newComps = comps + 1
      in kmpSearchStats' pattern text next (i + 1) 0 matches newComps mem

-- 复杂度分析
kmpComplexity :: String
kmpComplexity = 
    "时间复杂度: O(n + m)\n" ++
    "空间复杂度: O(m)\n" ++
    "预处理时间: O(m)\n" ++
    "应用: 文本搜索、DNA序列匹配、模式识别"
```

#### 性能分析

**时间复杂度**：
- 预处理：$O(m)$
- 匹配：$O(n + m)$

**空间复杂度**：$O(m)$

### 2. Boyer-Moore算法

#### 形式化定义

Boyer-Moore算法是一种高效的字符串匹配算法，从右到左比较，利用坏字符规则和好后缀规则进行跳跃。

**算法描述**：
1. 计算坏字符表和好后缀表
2. 从右到左比较模式串和文本
3. 根据规则进行跳跃

#### Haskell实现

```haskell
-- Boyer-Moore算法实现
boyerMooreSearch :: String -> String -> [Int]
boyerMooreSearch pattern text = 
    let badCharTable = computeBadCharTable pattern
        goodSuffixTable = computeGoodSuffixTable pattern
    in boyerMooreSearch' pattern text badCharTable goodSuffixTable 0

boyerMooreSearch' :: String -> String -> Map Char Int -> [Int] -> Int -> [Int]
boyerMooreSearch' pattern text badCharTable goodSuffixTable start
  | start + length pattern > length text = []
  | otherwise = 
      let match = checkMatch pattern text start
      in if match
         then start : boyerMooreSearch' pattern text badCharTable goodSuffixTable 
              (start + goodSuffixTable !! 0)
         else let shift = computeShift pattern text start badCharTable goodSuffixTable
              in boyerMooreSearch' pattern text badCharTable goodSuffixTable (start + shift)

-- 检查匹配
checkMatch :: String -> String -> Int -> Bool
checkMatch pattern text start = 
    let n = length pattern
    in all (\i -> pattern !! i == text !! (start + i)) [0..n-1]

-- 计算坏字符表
computeBadCharTable :: String -> Map Char Int
computeBadCharTable pattern = 
    let m = length pattern
        charPositions = [(pattern !! i, m - 1 - i) | i <- [0..m-1]]
    in Map.fromListWith max charPositions

-- 计算好后缀表
computeGoodSuffixTable :: String -> [Int]
computeGoodSuffixTable pattern = 
    let m = length pattern
        suffixes = computeSuffixes pattern
        shifts = replicate m m
    in computeGoodSuffixTable' pattern suffixes shifts

computeGoodSuffixTable' :: String -> [Int] -> [Int] -> [Int]
computeGoodSuffixTable' pattern suffixes shifts = 
    let m = length pattern
        j = 0
    in computeGoodSuffixTable'' pattern suffixes shifts j

computeGoodSuffixTable'' :: String -> [Int] -> [Int] -> Int -> [Int]
computeGoodSuffixTable'' pattern suffixes shifts j
  | j >= length pattern = shifts
  | otherwise = 
      let k = length pattern - 1 - suffixes !! j
          newShifts = shifts // [(k, length pattern - 1 - j)]
      in computeGoodSuffixTable'' pattern suffixes newShifts (j + 1)

-- 计算后缀数组
computeSuffixes :: String -> [Int]
computeSuffixes pattern = 
    let m = length pattern
        suffixes = replicate m 0
    in computeSuffixes' pattern suffixes (m - 1) (m - 1) 0

computeSuffixes' :: String -> [Int] -> Int -> Int -> Int -> [Int]
computeSuffixes' pattern suffixes i j k
  | i < 0 = suffixes
  | j >= 0 && pattern !! (m - 1 - k) == pattern !! j = 
      let newSuffixes = suffixes // [(i, k + 1)]
      in computeSuffixes' pattern newSuffixes (i - 1) (j - 1) (k + 1)
  | otherwise = 
      let newSuffixes = suffixes // [(i, k)]
      in computeSuffixes' pattern newSuffixes (i - 1) (i - 1) 0
  where m = length pattern

-- 计算跳跃距离
computeShift :: String -> String -> Int -> Map Char Int -> [Int] -> Int
computeShift pattern text start badCharTable goodSuffixTable = 
    let m = length pattern
        j = m - 1
        badCharShift = computeBadCharShift pattern text start j badCharTable
        goodSuffixShift = goodSuffixTable !! j
    in max badCharShift goodSuffixShift

computeBadCharShift :: String -> String -> Int -> Int -> Map Char Int -> Int
computeBadCharShift pattern text start j badCharTable = 
    let char = text !! (start + j)
        badCharShift = fromMaybe (j + 1) $ Map.lookup char badCharTable
    in max 1 (badCharShift - (length pattern - 1 - j))

-- 复杂度分析
boyerMooreComplexity :: String
boyerMooreComplexity = 
    "时间复杂度: O(n/m) 最好情况, O(nm) 最坏情况\n" ++
    "空间复杂度: O(k + m)\n" ++
    "预处理时间: O(m + k)\n" ++
    "应用: 文本编辑器、DNA序列分析、网络入侵检测"
```

#### 性能分析

**时间复杂度**：
- 最好情况：$O(n/m)$
- 最坏情况：$O(nm)$
- 平均情况：$O(n/m)$

**空间复杂度**：$O(k + m)$，其中 $k$ 是字母表大小

### 3. 最长公共子序列 (LCS)

#### 形式化定义

最长公共子序列问题是找到两个序列的最长公共子序列。

**问题定义**：
给定两个序列 $X = x_1x_2\ldots x_m$ 和 $Y = y_1y_2\ldots y_n$，找到最长的序列 $Z = z_1z_2\ldots z_k$，使得 $Z$ 是 $X$ 和 $Y$ 的子序列。

**动态规划方程**：
$$LCS[i,j] = \begin{cases}
0 & \text{if } i = 0 \text{ or } j = 0 \\
LCS[i-1,j-1] + 1 & \text{if } x_i = y_j \\
\max(LCS[i-1,j], LCS[i,j-1]) & \text{otherwise}
\end{cases}$$

#### Haskell实现

```haskell
-- 最长公共子序列算法
lcs :: String -> String -> String
lcs str1 str2 = 
    let m = length str1
        n = length str2
        dp = computeLCSDP str1 str2
    in reconstructLCS str1 str2 dp m n

-- 计算动态规划表
computeLCSDP :: String -> String -> Array (Int, Int) Int
computeLCSDP str1 str2 = 
    let m = length str1
        n = length str2
        bounds = ((0, 0), (m, n))
        initialArray = array bounds [(i, 0) | i <- range bounds]
    in computeLCSDP' str1 str2 initialArray 1 1

computeLCSDP' :: String -> String -> Array (Int, Int) Int -> Int -> Int -> Array (Int, Int) Int
computeLCSDP' str1 str2 dp i j
  | i > length str1 = dp
  | j > length str2 = computeLCSDP' str1 str2 dp (i + 1) 1
  | str1 !! (i - 1) == str2 !! (j - 1) = 
      let newValue = dp ! (i - 1, j - 1) + 1
          newDp = dp // [((i, j), newValue)]
      in computeLCSDP' str1 str2 newDp i (j + 1)
  | otherwise = 
      let maxValue = max (dp ! (i - 1, j)) (dp ! (i, j - 1))
          newDp = dp // [((i, j), maxValue)]
      in computeLCSDP' str1 str2 newDp i (j + 1)

-- 重构LCS
reconstructLCS :: String -> String -> Array (Int, Int) Int -> Int -> Int -> String
reconstructLCS str1 str2 dp i j
  | i == 0 || j == 0 = ""
  | str1 !! (i - 1) == str2 !! (j - 1) = 
      reconstructLCS str1 str2 dp (i - 1) (j - 1) ++ [str1 !! (i - 1)]
  | dp ! (i - 1, j) >= dp ! (i, j - 1) = 
      reconstructLCS str1 str2 dp (i - 1) j
  | otherwise = 
      reconstructLCS str1 str2 dp i (j - 1)

-- 带统计的LCS
lcsWithStats :: String -> String -> StringAlgorithmResult String
lcsWithStats str1 str2 = StringAlgorithmResult
    { result = result
    , comparisons = compCount
    , time = 0.0
    , memory = memory
    }
  where
    (result, compCount, memory) = lcsStats str1 str2

lcsStats :: String -> String -> (String, Int, Int)
lcsStats str1 str2 = 
    let m = length str1
        n = length str2
        dp = computeLCSDP str1 str2
        result = reconstructLCS str1 str2 dp m n
        compCount = m * n
        memory = m * n
    in (result, compCount, memory)

-- 复杂度分析
lcsComplexity :: String
lcsComplexity = 
    "时间复杂度: O(mn)\n" ++
    "空间复杂度: O(mn)\n" ++
    "应用: 生物信息学、版本控制、文本相似度\n" ++
    "特点: 动态规划算法，全局最优解"
```

#### 性能分析

**时间复杂度**：$O(mn)$
**空间复杂度**：$O(mn)$

### 4. 编辑距离算法

#### 形式化定义

编辑距离是衡量两个字符串相似度的指标，定义为将一个字符串转换为另一个字符串所需的最少操作次数。

**操作类型**：
1. **插入**：在字符串中插入一个字符
2. **删除**：从字符串中删除一个字符
3. **替换**：将字符串中的一个字符替换为另一个字符

**动态规划方程**：
$$ED[i,j] = \begin{cases}
i & \text{if } j = 0 \\
j & \text{if } i = 0 \\
ED[i-1,j-1] & \text{if } x_i = y_j \\
\min(ED[i-1,j] + 1, ED[i,j-1] + 1, ED[i-1,j-1] + 1) & \text{otherwise}
\end{cases}$$

#### Haskell实现

```haskell
-- 编辑距离算法
editDistance :: String -> String -> Int
editDistance str1 str2 = 
    let m = length str1
        n = length str2
        dp = computeEditDistanceDP str1 str2
    in dp ! (m, n)

-- 计算编辑距离动态规划表
computeEditDistanceDP :: String -> String -> Array (Int, Int) Int
computeEditDistanceDP str1 str2 = 
    let m = length str1
        n = length str2
        bounds = ((0, 0), (m, n))
        initialArray = array bounds [(i, i) | i <- [0..m]] // 
                                     [(j, j) | j <- [0..n]]
    in computeEditDistanceDP' str1 str2 initialArray 1 1

computeEditDistanceDP' :: String -> String -> Array (Int, Int) Int -> Int -> Int -> Array (Int, Int) Int
computeEditDistanceDP' str1 str2 dp i j
  | i > length str1 = dp
  | j > length str2 = computeEditDistanceDP' str1 str2 dp (i + 1) 1
  | str1 !! (i - 1) == str2 !! (j - 1) = 
      let newValue = dp ! (i - 1, j - 1)
          newDp = dp // [((i, j), newValue)]
      in computeEditDistanceDP' str1 str2 newDp i (j + 1)
  | otherwise = 
      let deleteCost = dp ! (i - 1, j) + 1
          insertCost = dp ! (i, j - 1) + 1
          replaceCost = dp ! (i - 1, j - 1) + 1
          minCost = minimum [deleteCost, insertCost, replaceCost]
          newDp = dp // [((i, j), minCost)]
      in computeEditDistanceDP' str1 str2 newDp i (j + 1)

-- 带统计的编辑距离
editDistanceWithStats :: String -> String -> StringAlgorithmResult Int
editDistanceWithStats str1 str2 = StringAlgorithmResult
    { result = result
    , comparisons = compCount
    , time = 0.0
    , memory = memory
    }
  where
    (result, compCount, memory) = editDistanceStats str1 str2

editDistanceStats :: String -> String -> (Int, Int, Int)
editDistanceStats str1 str2 = 
    let m = length str1
        n = length str2
        dp = computeEditDistanceDP str1 str2
        result = dp ! (m, n)
        compCount = m * n
        memory = m * n
    in (result, compCount, memory)

-- 复杂度分析
editDistanceComplexity :: String
editDistanceComplexity = 
    "时间复杂度: O(mn)\n" ++
    "空间复杂度: O(mn)\n" ++
    "应用: 拼写检查、DNA序列比对、自然语言处理\n" ++
    "特点: 动态规划算法，全局最优解"
```

#### 性能分析

**时间复杂度**：$O(mn)$
**空间复杂度**：$O(mn)$

### 5. 字符串哈希算法

#### 形式化定义

字符串哈希是将字符串映射到整数的函数，用于快速比较和查找。

**哈希函数**：
$$H(s) = \sum_{i=0}^{n-1} s[i] \cdot p^i \bmod m$$

其中 $p$ 是质数，$m$ 是模数。

#### Haskell实现

```haskell
-- 字符串哈希算法
stringHash :: String -> Int
stringHash str = 
    let p = 31  -- 质数
        m = 1000000007  -- 大质数
    in stringHash' str p m 0 0

stringHash' :: String -> Int -> Int -> Int -> Int -> Int
stringHash' [] p m hash power = hash
stringHash' (c:cs) p m hash power = 
    let newHash = (hash + (ord c - ord 'a' + 1) * power) `mod` m
        newPower = (power * p) `mod` m
    in stringHash' cs p m newHash newPower

-- 滚动哈希
rollingHash :: String -> Int -> Int -> [Int]
rollingHash str windowSize p = 
    let m = 1000000007
        initialHash = stringHash $ take windowSize str
    in rollingHash' str windowSize p m initialHash 1

rollingHash' :: String -> Int -> Int -> Int -> Int -> Int -> [Int]
rollingHash' str windowSize p m hash power
  | length str <= windowSize = [hash]
  | otherwise = 
      let oldChar = ord $ head str
          newChar = ord $ str !! windowSize
          newHash = ((hash - (oldChar - ord 'a' + 1) * power) * p + 
                     (newChar - ord 'a' + 1)) `mod` m
          newPower = (power * p) `mod` m
      in hash : rollingHash' (tail str) windowSize p m newHash newPower

-- 复杂度分析
stringHashComplexity :: String
stringHashComplexity = 
    "时间复杂度: O(n) 初始化, O(1) 滚动\n" ++
    "空间复杂度: O(1)\n" ++
    "应用: 字符串匹配、重复检测、数据去重\n" ++
    "特点: 概率性算法，可能有哈希冲突"
```

#### 性能分析

**时间复杂度**：
- 初始化：$O(n)$
- 滚动：$O(1)$

**空间复杂度**：$O(1)$

## 📊 算法比较

### 性能对比表

| 算法 | 时间复杂度 | 空间复杂度 | 应用场景 | 特点 |
|------|------------|------------|----------|------|
| KMP | O(n + m) | O(m) | 精确匹配 | 线性时间，预处理 |
| Boyer-Moore | O(n/m) 平均 | O(k + m) | 大文本搜索 | 跳跃式匹配 |
| LCS | O(mn) | O(mn) | 序列比对 | 动态规划 |
| 编辑距离 | O(mn) | O(mn) | 相似度计算 | 动态规划 |
| 字符串哈希 | O(n) | O(1) | 快速比较 | 概率性算法 |

### 选择指南

```haskell
-- 算法选择函数
chooseStringAlgorithm :: String -> String
chooseStringAlgorithm "exact_match" = "KMP或Boyer-Moore"
chooseStringAlgorithm "similarity" = "编辑距离"
chooseStringAlgorithm "common_subsequence" = "LCS"
chooseStringAlgorithm "fast_comparison" = "字符串哈希"
chooseStringAlgorithm _ = "根据具体需求选择"

-- 智能算法选择
smartStringAlgorithm :: String -> String -> String
smartStringAlgorithm "search" "exact" = "KMP"
smartStringAlgorithm "search" "approximate" = "Boyer-Moore"
smartStringAlgorithm "compare" "similarity" = "编辑距离"
smartStringAlgorithm "compare" "subsequence" = "LCS"
smartStringAlgorithm "hash" "rolling" = "滚动哈希"
smartStringAlgorithm _ _ = "需要更多信息"
```

## 🔬 形式化验证

### 正确性证明

#### KMP算法正确性

**定理**：KMP算法能够正确找到模式串在文本中的所有匹配位置。

**证明**：
1. **失败函数正确性**：失败函数确保不会错过任何可能的匹配
2. **匹配过程正确性**：每次比较都是必要的，不会重复比较

#### 编辑距离算法正确性

**定理**：编辑距离算法能够找到两个字符串之间的最小编辑距离。

**证明**：
1. **基础情况**：空字符串的编辑距离显然正确
2. **归纳假设**：假设对长度小于 $n$ 的字符串正确
3. **归纳步骤**：通过动态规划方程确保最优解

### 复杂度证明

#### LCS算法复杂度

**定理**：LCS算法的时间复杂度为 $O(mn)$。

**证明**：
- 动态规划表大小为 $m \times n$
- 每个单元格的计算时间为 $O(1)$
- 总时间复杂度：$O(mn)$

## 🎯 实际应用

### 性能测试

```haskell
-- 性能测试函数
testStringAlgorithmPerformance :: String -> String -> IO ()
testStringAlgorithmPerformance pattern text = do
    putStrLn "字符串算法性能测试"
    putStrLn "=================="
    
    let testAlgorithm name algFunc = do
            start <- getCurrentTime
            let result = algFunc pattern text
            end <- getCurrentTime
            let duration = diffUTCTime end start
            putStrLn $ name ++ ": " ++ show duration
    
    testAlgorithm "KMP" kmpSearch
    testAlgorithm "Boyer-Moore" boyerMooreSearch
    testAlgorithm "LCS" (\p t -> lcs p t)
    testAlgorithm "编辑距离" editDistance

-- 生成测试数据
generateTestString :: Int -> IO String
generateTestString n = do
    gen <- newStdGen
    return $ take n $ randomRs ('a', 'z') gen
```

### 实际应用场景

1. **文本编辑器**：查找和替换功能
2. **生物信息学**：DNA序列匹配和分析
3. **自然语言处理**：拼写检查和文本相似度
4. **版本控制**：文件差异比较
5. **网络安全**：模式匹配和入侵检测

## 📚 扩展阅读

### 高级字符串算法

1. **后缀数组**：高效的字符串索引结构
2. **后缀自动机**：线性时间的字符串处理
3. **AC自动机**：多模式串匹配
4. **Manacher算法**：最长回文子串
5. **Z算法**：线性时间的模式匹配

### 并行字符串算法

```haskell
-- 并行字符串匹配
parallelStringSearch :: String -> String -> [Int]
parallelStringSearch pattern text = 
    let chunkSize = length text `div` numCapabilities
        chunks = chunksOf chunkSize text
        searchChunk chunk offset = 
            let matches = kmpSearch pattern chunk
            in map (+ offset) matches
    in concat $ zipWith searchChunk chunks [0, chunkSize..]

-- 分块函数
chunksOf :: Int -> [a] -> [[a]]
chunksOf n [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)
```

## 🔗 相关链接

- [基础数据结构](../01-Haskell-Basics/01-Language-Features.md)
- [高级数据结构](../03-Data-Structures/01-Advanced-Data-Structures.md)
- [形式化证明](../04-Formal-Proofs/01-Theorem-Proving.md)
- [性能优化](../05-Performance-Optimization/01-Memory-Optimization.md)

---

*本文档提供了字符串算法的完整形式化理论和Haskell实现，包括性能分析和实际应用指导。* 