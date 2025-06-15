# 信息论

## 概述

信息论是研究信息传输、存储和处理的数学理论，包括熵、信道容量、编码理论等。本文档从形式化角度探讨信息论的核心概念和理论。

## 1. 信息熵

### 1.1 基本概念

信息熵是信息论的核心概念。

```haskell
-- 信息熵
data InformationEntropy = InformationEntropy
  { entropyValue :: Double
  , entropyBase :: Double
  , entropyDistribution :: [(String, Double)]
  }

-- 计算信息熵
computeEntropy :: [(String, Double)] -> Double -> Double
computeEntropy distribution base = 
  let probabilities = map snd distribution
      logProbabilities = map (\p -> if p > 0 then logBase base p else 0) probabilities
      weightedLogs = zipWith (*) probabilities logProbabilities
  in -sum weightedLogs

-- 香农熵
shannonEntropy :: [(String, Double)] -> Double
shannonEntropy distribution = computeEntropy distribution 2

-- 联合熵
jointEntropy :: [(String, Double)] -> [(String, Double)] -> Double
jointEntropy dist1 dist2 = 
  let jointDistribution = [(x ++ "," ++ y, p1 * p2) | 
                           (x, p1) <- dist1, (y, p2) <- dist2]
  in shannonEntropy jointDistribution

-- 条件熵
conditionalEntropy :: [(String, Double)] -> [(String, Double)] -> Double
conditionalEntropy dist1 dist2 = 
  let jointDist = [(x ++ "," ++ y, p1 * p2) | 
                   (x, p1) <- dist1, (y, p2) <- dist2]
      marginalDist2 = [(y, sum [p | (xy, p) <- jointDist, 
                                   let (x', y') = splitAt (length x) xy, 
                                   y' == y]) | 
                       (y, _) <- dist2]
  in jointEntropy dist1 dist2 - shannonEntropy marginalDist2

-- 相对熵（KL散度）
relativeEntropy :: [(String, Double)] -> [(String, Double)] -> Double
relativeEntropy p q = 
  let commonOutcomes = nub (map fst p ++ map fst q)
      klTerms = [let pVal = lookup x p ? 0
                     qVal = lookup x q ? 0
                 in if pVal > 0 && qVal > 0
                    then pVal * logBase 2 (pVal / qVal)
                    else 0 | x <- commonOutcomes]
  in sum klTerms

-- 交叉熵
crossEntropy :: [(String, Double)] -> [(String, Double)] -> Double
crossEntropy p q = 
  let commonOutcomes = nub (map fst p ++ map fst q)
      crossTerms = [let pVal = lookup x p ? 0
                        qVal = lookup x q ? 0
                    in if pVal > 0 && qVal > 0
                       then -pVal * logBase 2 qVal
                       else 0 | x <- commonOutcomes]
  in sum crossTerms

-- 从Maybe中提取值
(?) :: Maybe a -> a -> a
(Just x) ? _ = x
Nothing ? y = y
```

### 1.2 互信息

互信息衡量两个随机变量之间的依赖关系。

```haskell
-- 互信息
data MutualInformation = MutualInformation
  { mutualInformationValue :: Double
  , variable1 :: String
  , variable2 :: String
  }

-- 计算互信息
computeMutualInformation :: [(String, Double)] -> [(String, Double)] -> Double
computeMutualInformation dist1 dist2 = 
  let entropy1 = shannonEntropy dist1
      entropy2 = shannonEntropy dist2
      jointEnt = jointEntropy dist1 dist2
  in entropy1 + entropy2 - jointEnt

-- 信息增益
informationGain :: [(String, Double)] -> [(String, Double)] -> Double
informationGain target feature = 
  let targetEntropy = shannonEntropy target
      conditionalEnt = conditionalEntropy target feature
  in targetEntropy - conditionalEnt

-- 条件互信息
conditionalMutualInformation :: [(String, Double)] -> [(String, Double)] -> [(String, Double)] -> Double
conditionalMutualInformation x y z = 
  let jointXYZ = [(x' ++ "," ++ y' ++ "," ++ z', p1 * p2 * p3) | 
                   (x', p1) <- x, (y', p2) <- y, (z', p3) <- z]
      jointXZ = [(x' ++ "," ++ z', p1 * p3) | 
                 (x', p1) <- x, (z', p3) <- z]
      jointYZ = [(y' ++ "," ++ z', p2 * p3) | 
                 (y', p2) <- y, (z', p3) <- z]
      jointZ = [(z', p3) | (z', p3) <- z]
  in shannonEntropy jointXYZ + shannonEntropy jointZ - 
     shannonEntropy jointXZ - shannonEntropy jointYZ
```

### 1.3 熵的性质

熵具有重要的数学性质。

```haskell
-- 熵的性质验证
entropyProperties :: [(String, Double)] -> Bool
entropyProperties distribution = 
  let entropy = shannonEntropy distribution
      probabilities = map snd distribution
  in -- 非负性
     entropy >= 0 &&
     -- 对称性
     entropy == shannonEntropy (reverse distribution) &&
     -- 最大熵
     entropy <= logBase 2 (fromIntegral (length distribution))

-- 最大熵分布
maximumEntropyDistribution :: Int -> [(String, Double)]
maximumEntropyDistribution n = 
  let outcomes = map show [1..n]
      probability = 1.0 / fromIntegral n
  in [(outcome, probability) | outcome <- outcomes]

-- 熵的凸性
entropyConvexity :: [(String, Double)] -> [(String, Double)] -> Double -> Bool
entropyConvexity p q lambda = 
  let entropyP = shannonEntropy p
      entropyQ = shannonEntropy q
      convexCombination = [(x, lambda * pVal + (1 - lambda) * qVal) | 
                           (x, pVal) <- p, 
                           (x, qVal) <- q]
      entropyConvex = shannonEntropy convexCombination
  in entropyConvex <= lambda * entropyP + (1 - lambda) * entropyQ

-- 熵的链式法则
entropyChainRule :: [(String, Double)] -> [(String, Double)] -> Bool
entropyChainRule x y = 
  let jointEntropy = jointEntropy x y
      entropyX = shannonEntropy x
      conditionalEntropy = conditionalEntropy x y
  in abs (jointEntropy - (entropyX + conditionalEntropy)) < 0.001
```

## 2. 信道理论

### 2.1 信道模型

信道是信息传输的数学模型。

```haskell
-- 信道
data Channel = Channel
  { channelMatrix :: [[Double]]
  , inputAlphabet :: [String]
  , outputAlphabet :: [String]
  }

-- 离散无记忆信道
data DiscreteMemorylessChannel = DiscreteMemorylessChannel
  { inputSize :: Int
  , outputSize :: Int
  , transitionMatrix :: [[Double]]
  }

-- 二元对称信道
binarySymmetricChannel :: Double -> DiscreteMemorylessChannel
binarySymmetricChannel errorProbability = 
  DiscreteMemorylessChannel {
    inputSize = 2,
    outputSize = 2,
    transitionMatrix = [[1 - errorProbability, errorProbability],
                        [errorProbability, 1 - errorProbability]]
  }

-- 二元擦除信道
binaryErasureChannel :: Double -> DiscreteMemorylessChannel
binaryErasureChannel erasureProbability = 
  DiscreteMemorylessChannel {
    inputSize = 2,
    outputSize = 3,
    transitionMatrix = [[1 - erasureProbability, 0, erasureProbability],
                        [0, 1 - erasureProbability, erasureProbability]]
  }

-- 信道输出概率
channelOutputProbability :: DiscreteMemorylessChannel -> Int -> Int -> Double
channelOutputProbability channel input output = 
  transitionMatrix channel !! input !! output

-- 信道容量
data ChannelCapacity = ChannelCapacity
  { capacityValue :: Double
  , optimalDistribution :: [(String, Double)]
  }

-- 计算信道容量
computeChannelCapacity :: DiscreteMemorylessChannel -> ChannelCapacity
computeChannelCapacity channel = 
  let inputSize = inputSize channel
      outputSize = outputSize channel
      -- 简化实现，实际需要迭代算法
      uniformDistribution = [(show i, 1.0 / fromIntegral inputSize) | i <- [0..inputSize-1]]
      capacity = mutualInformationForChannel channel uniformDistribution
  in ChannelCapacity {
    capacityValue = capacity,
    optimalDistribution = uniformDistribution
  }

-- 信道互信息
mutualInformationForChannel :: DiscreteMemorylessChannel -> [(String, Double)] -> Double
mutualInformationForChannel channel inputDist = 
  let inputSize = inputSize channel
      outputSize = outputSize channel
      matrix = transitionMatrix channel
      -- 计算输出分布
      outputDist = [(show j, sum [pX * matrix !! i !! j | 
                                   (x, pX) <- zip (map show [0..inputSize-1]) (map snd inputDist), 
                                   let i = read x]) | 
                    j <- [0..outputSize-1]]
      -- 计算联合分布
      jointDist = [(x ++ "," ++ show j, pX * matrix !! i !! j) | 
                   (x, pX) <- zip (map show [0..inputSize-1]) (map snd inputDist),
                   j <- [0..outputSize-1],
                   let i = read x]
  in computeMutualInformation inputDist outputDist
```

### 2.2 信道编码

信道编码是提高传输可靠性的方法。

```haskell
-- 信道编码
data ChannelCode = ChannelCode
  { codeLength :: Int
  , codeDimension :: Int
  , generatorMatrix :: [[Int]]
  , parityCheckMatrix :: [[Int]]
  }

-- 线性码
data LinearCode = LinearCode
  { codeLength :: Int
  , codeDimension :: Int
  , generatorMatrix :: [[Int]]
  }

-- 生成线性码
generateLinearCode :: Int -> Int -> LinearCode
generateLinearCode n k = 
  let generatorMatrix = generateGeneratorMatrix n k
  in LinearCode {
    codeLength = n,
    codeDimension = k,
    generatorMatrix = generatorMatrix
  }

-- 生成生成矩阵
generateGeneratorMatrix :: Int -> Int -> [[Int]]
generateGeneratorMatrix n k = 
  let identityMatrix = [[if i == j then 1 else 0 | j <- [0..k-1]] | i <- [0..k-1]]
      randomMatrix = [[if i < k then 0 else (i + j) `mod` 2 | j <- [0..n-k-1]] | i <- [0..n-1]]
  in zipWith (++) identityMatrix randomMatrix

-- 编码
encode :: LinearCode -> [Int] -> [Int]
encode code message = 
  let generator = generatorMatrix code
  in matrixVectorMultiply generator message

-- 矩阵向量乘法
matrixVectorMultiply :: [[Int]] -> [Int] -> [Int]
matrixVectorMultiply matrix vector = 
  map (\row -> sum (zipWith (*) row vector)) matrix

-- 解码
decode :: LinearCode -> [Int] -> [Int]
decode code received = 
  let syndrome = computeSyndrome code received
      errorPattern = findErrorPattern syndrome
      corrected = zipWith xor received errorPattern
  in extractMessage code corrected

-- 计算症状
computeSyndrome :: LinearCode -> [Int] -> [Int]
computeSyndrome code received = 
  let parityCheck = computeParityCheckMatrix code
  in matrixVectorMultiply parityCheck received

-- 计算校验矩阵
computeParityCheckMatrix :: LinearCode -> [[Int]]
computeParityCheckMatrix code = 
  let n = codeLength code
      k = codeDimension code
      generator = generatorMatrix code
      -- 简化实现
      parityCheck = [[if i == j then 1 else 0 | j <- [0..n-k-1]] | i <- [0..n-k-1]]
  in parityCheck

-- 查找错误模式
findErrorPattern :: [Int] -> [Int]
findErrorPattern syndrome = 
  -- 简化实现，实际需要查找表
  replicate (length syndrome) 0

-- 异或运算
xor :: Int -> Int -> Int
xor 0 0 = 0
xor 0 1 = 1
xor 1 0 = 1
xor 1 1 = 0

-- 提取消息
extractMessage :: LinearCode -> [Int] -> [Int]
extractMessage code codeword = 
  let k = codeDimension code
  in take k codeword
```

### 2.3 香农定理

香农定理是信息论的重要定理。

```haskell
-- 香农定理
data ShannonTheorem = ShannonTheorem
  { channelCapacity :: Double
  , achievableRate :: Double
  , errorProbability :: Double
  }

-- 香农第一定理（无噪声编码定理）
shannonFirstTheorem :: [(String, Double)] -> Double -> ShannonTheorem
shannonFirstTheorem source entropy = 
  let rate = entropy
      capacity = entropy  -- 无噪声信道
      errorProb = 0.0
  in ShannonTheorem {
    channelCapacity = capacity,
    achievableRate = rate,
    errorProbability = errorProb
  }

-- 香农第二定理（信道编码定理）
shannonSecondTheorem :: DiscreteMemorylessChannel -> Double -> ShannonTheorem
shannonSecondTheorem channel rate = 
  let capacity = computeChannelCapacity channel
      achievableRate = min rate (capacityValue capacity)
      errorProb = if rate <= capacityValue capacity then 0.0 else 1.0
  in ShannonTheorem {
    channelCapacity = capacityValue capacity,
    achievableRate = achievableRate,
    errorProbability = errorProb
  }

-- 香农第三定理（率失真定理）
shannonThirdTheorem :: [(String, Double)] -> Double -> ShannonTheorem
shannonThirdTheorem source distortion = 
  let entropy = shannonEntropy source
      rate = max 0 (entropy - distortion)
      capacity = entropy
  in ShannonTheorem {
    channelCapacity = capacity,
    achievableRate = rate,
    errorProbability = distortion
  }
```

## 3. 编码理论

### 3.1 信源编码

信源编码是压缩信息的方法。

```haskell
-- 信源编码
data SourceCode = SourceCode
  { codeAlphabet :: [String]
  , codeMapping :: [(String, String)]
  , codeLength :: Int
  }

-- 霍夫曼编码
data HuffmanCode = HuffmanCode
  { codeTree :: HuffmanTree
  , codeMapping :: [(String, String)]
  }

-- 霍夫曼树
data HuffmanTree = 
  Leaf String Double
  | Node HuffmanTree HuffmanTree Double

-- 构建霍夫曼编码
buildHuffmanCode :: [(String, Double)] -> HuffmanCode
buildHuffmanCode distribution = 
  let sortedDist = sortBy (comparing snd) distribution
      tree = buildHuffmanTree sortedDist
      mapping = generateHuffmanMapping tree
  in HuffmanCode {
    codeTree = tree,
    codeMapping = mapping
  }

-- 构建霍夫曼树
buildHuffmanTree :: [(String, Double)] -> HuffmanTree
buildHuffmanTree [] = error "Empty distribution"
buildHuffmanTree [(symbol, prob)] = Leaf symbol prob
buildHuffmanTree distribution = 
  let sortedDist = sortBy (comparing snd) distribution
      (symbol1, prob1) = head sortedDist
      (symbol2, prob2) = head (tail sortedDist)
      remaining = drop 2 sortedDist
      combinedProb = prob1 + prob2
      newSymbol = symbol1 ++ symbol2
      newDist = (newSymbol, combinedProb) : remaining
      subtree = buildHuffmanTree newDist
  in case subtree of
       Leaf _ _ -> Node (Leaf symbol1 prob1) (Leaf symbol2 prob2) combinedProb
       Node left right _ -> Node (Node left right combinedProb) (Leaf symbol2 prob2) combinedProb

-- 生成霍夫曼映射
generateHuffmanMapping :: HuffmanTree -> [(String, String)]
generateHuffmanMapping tree = 
  generateHuffmanMappingHelper tree ""

-- 霍夫曼映射辅助函数
generateHuffmanMappingHelper :: HuffmanTree -> String -> [(String, String)]
generateHuffmanMappingHelper (Leaf symbol _) code = [(symbol, code)]
generateHuffmanMappingHelper (Node left right _) code = 
  generateHuffmanMappingHelper left (code ++ "0") ++
  generateHuffmanMappingHelper right (code ++ "1")

-- 霍夫曼编码
huffmanEncode :: HuffmanCode -> String -> String
huffmanEncode code message = 
  let mapping = codeMapping code
      symbols = words message
  in concat [lookup symbol mapping ? symbol | symbol <- symbols]

-- 霍夫曼解码
huffmanDecode :: HuffmanCode -> String -> String
huffmanDecode code encoded = 
  let tree = codeTree code
      decoded = huffmanDecodeHelper tree tree encoded
  in unwords decoded

-- 霍夫曼解码辅助函数
huffmanDecodeHelper :: HuffmanTree -> HuffmanTree -> String -> [String]
huffmanDecodeHelper _ _ [] = []
huffmanDecodeHelper originalTree (Leaf symbol _) bits = 
  symbol : huffmanDecodeHelper originalTree originalTree bits
huffmanDecodeHelper originalTree (Node left right _) (bit:bits) = 
  case bit of
    '0' -> huffmanDecodeHelper originalTree left bits
    '1' -> huffmanDecodeHelper originalTree right bits
    _ -> huffmanDecodeHelper originalTree originalTree bits
```

### 3.2 算术编码

算术编码是另一种信源编码方法。

```haskell
-- 算术编码
data ArithmeticCode = ArithmeticCode
  { symbolProbabilities :: [(String, Double)]
  , cumulativeProbabilities :: [(String, Double)]
  }

-- 构建算术编码
buildArithmeticCode :: [(String, Double)] -> ArithmeticCode
buildArithmeticCode distribution = 
  let sortedDist = sortBy (comparing fst) distribution
      cumulative = scanl (\(_, _) (symbol, prob) -> 
                           (symbol, snd (last cumulative) + prob)) 
                         ("", 0.0) sortedDist
  in ArithmeticCode {
    symbolProbabilities = distribution,
    cumulativeProbabilities = tail cumulative
  }

-- 算术编码
arithmeticEncode :: ArithmeticCode -> String -> Double
arithmeticEncode code message = 
  let symbols = words message
      probabilities = symbolProbabilities code
      cumulative = cumulativeProbabilities code
  in arithmeticEncodeHelper symbols probabilities cumulative 0.0 1.0

-- 算术编码辅助函数
arithmeticEncodeHelper :: [String] -> [(String, Double)] -> [(String, Double)] -> Double -> Double -> Double
arithmeticEncodeHelper [] _ _ low high = (low + high) / 2
arithmeticEncodeHelper (symbol:symbols) probs cumul low high = 
  let symbolProb = lookup symbol probs ? 0.0
      symbolCumul = lookup symbol cumul ? 0.0
      range = high - low
      newLow = low + symbolCumul * range
      newHigh = low + (symbolCumul + symbolProb) * range
  in arithmeticEncodeHelper symbols probs cumul newLow newHigh

-- 算术解码
arithmeticDecode :: ArithmeticCode -> Double -> Int -> String
arithmeticDecode code encodedValue length = 
  let probabilities = symbolProbabilities code
      cumulative = cumulativeProbabilities code
  in arithmeticDecodeHelper probabilities cumulative encodedValue length ""

-- 算术解码辅助函数
arithmeticDecodeHelper :: [(String, Double)] -> [(String, Double)] -> Double -> Int -> String -> String
arithmeticDecodeHelper _ _ _ 0 decoded = decoded
arithmeticDecodeHelper probs cumul value length decoded = 
  let symbol = findSymbol probs cumul value
      symbolProb = lookup symbol probs ? 0.0
      symbolCumul = lookup symbol cumul ? 0.0
      newValue = (value - symbolCumul) / symbolProb
  in arithmeticDecodeHelper probs cumul newValue (length - 1) (decoded ++ " " ++ symbol)

-- 查找符号
findSymbol :: [(String, Double)] -> [(String, Double)] -> Double -> String
findSymbol probs cumul value = 
  let pairs = zip (map fst probs) (map snd cumul)
      symbol = find (\(_, cumulVal) -> value >= cumulVal) pairs
  in case symbol of
       Just (sym, _) -> sym
       Nothing -> head (map fst probs)
```

## 4. 率失真理论

### 4.1 失真度量

失真度量衡量重建信号与原始信号的差异。

```haskell
-- 失真度量
data DistortionMeasure = DistortionMeasure
  { measureFunction :: String -> String -> Double
  , measureType :: DistortionType
  }

-- 失真类型
data DistortionType = 
  Hamming | Euclidean | Manhattan | Chebyshev

-- 汉明失真
hammingDistortion :: DistortionMeasure
hammingDistortion = DistortionMeasure {
  measureFunction = \x y -> 
    let length = min (length x) (length y)
        differences = sum [if x !! i /= y !! i then 1 else 0 | i <- [0..length-1]]
    in fromIntegral differences,
  measureType = Hamming
}

-- 欧几里得失真
euclideanDistortion :: DistortionMeasure
euclideanDistortion = DistortionMeasure {
  measureFunction = \x y -> 
    let xValues = map read (words x) :: [Double]
        yValues = map read (words y) :: [Double]
        length = min (length xValues) (length yValues)
        squaredDiff = sum [(xValues !! i - yValues !! i)^2 | i <- [0..length-1]]
    in sqrt squaredDiff,
  measureType = Euclidean
}

-- 率失真函数
data RateDistortionFunction = RateDistortionFunction
  { sourceDistribution :: [(String, Double)]
  , distortionMeasure :: DistortionMeasure
  , rateFunction :: Double -> Double
  }

-- 计算率失真函数
computeRateDistortionFunction :: [(String, Double)] -> DistortionMeasure -> RateDistortionFunction
computeRateDistortionFunction source distortion = 
  RateDistortionFunction {
    sourceDistribution = source,
    distortionMeasure = distortion,
    rateFunction = \d -> 
      let entropy = shannonEntropy source
      in max 0 (entropy - d)
  }

-- 率失真编码
data RateDistortionCode = RateDistortionCode
  { sourceAlphabet :: [String]
  , reproductionAlphabet :: [String]
  , encodingFunction :: String -> String
  , distortion :: Double
  }

-- 构建率失真编码
buildRateDistortionCode :: [(String, Double)] -> DistortionMeasure -> Double -> RateDistortionCode
buildRateDistortionCode source distortion targetDistortion = 
  let sourceAlphabet = map fst source
      reproductionAlphabet = generateReproductionAlphabet sourceAlphabet
      encodingFunction = \x -> findBestReproduction x reproductionAlphabet distortion
      actualDistortion = computeAverageDistortion source encodingFunction distortion
  in RateDistortionCode {
    sourceAlphabet = sourceAlphabet,
    reproductionAlphabet = reproductionAlphabet,
    encodingFunction = encodingFunction,
    distortion = actualDistortion
  }

-- 生成重建字母表
generateReproductionAlphabet :: [String] -> [String]
generateReproductionAlphabet source = 
  let uniqueSymbols = nub (concatMap words source)
  in uniqueSymbols

-- 查找最佳重建
findBestReproduction :: String -> [String] -> DistortionMeasure -> String
findBestReproduction source reproductions distortion = 
  let distortions = [(rep, measureFunction distortion source rep) | rep <- reproductions]
      bestReproduction = minimumBy (comparing snd) distortions
  in fst bestReproduction

-- 计算平均失真
computeAverageDistortion :: [(String, Double)] -> (String -> String) -> DistortionMeasure -> Double
computeAverageDistortion source encodingFunction distortion = 
  let distortions = [(symbol, prob * measureFunction distortion symbol (encodingFunction symbol)) | 
                     (symbol, prob) <- source]
  in sum (map snd distortions)
```

## 总结

信息论为理解信息传输、存储和处理提供了系统的数学框架。通过形式化方法，我们可以：

1. **精确建模**：用数学结构精确描述信息源和信道
2. **性能分析**：分析编码方案的效率和可靠性
3. **算法设计**：设计高效的信源编码和信道编码算法
4. **理论发展**：为通信系统提供理论基础

信息论的研究将继续推动我们对信息本质的理解，并为通信和数据处理技术提供指导。 