# 信息论 / Information Theory

## 📚 概述 / Overview

信息论是研究信息的度量、传输、编码与压缩的理论体系。它为通信、数据压缩、加密、机器学习等领域提供基础理论，是现代数字通信和数据处理的核心理论基础。

Information theory is a theoretical system that studies the measurement, transmission, encoding, and compression of information. It provides fundamental theories for communication, data compression, encryption, machine learning, etc., and is the core theoretical foundation of modern digital communication and data processing.

## 🎯 核心目标 / Core Objectives

1. **形式化信息概念 / Formalize Information Concepts**: 建立信息、熵、互信息等概念的严格数学定义 / Establish rigorous mathematical definitions of information, entropy, mutual information, etc.
2. **实现信息度量 / Implement Information Measures**: 构建熵、条件熵、互信息的计算模型 / Construct computational models for entropy, conditional entropy, and mutual information
3. **建立编码理论 / Establish Coding Theory**: 实现香农编码、霍夫曼编码、信道编码 / Implement Shannon coding, Huffman coding, and channel coding
4. **发展信道理论 / Develop Channel Theory**: 建立信道容量、噪声模型、编码定理 / Establish channel capacity, noise models, and coding theorems
5. **应用信息论 / Apply Information Theory**: 在数据压缩、通信系统、机器学习中的应用 / Applications in data compression, communication systems, and machine learning

## 🏗️ 理论框架 / Theoretical Framework

### 1. 信息熵 / Information Entropy

**定义 1.1 (信息熵 / Information Entropy)**
离散随机变量 $X$ 的信息熵定义为：

The information entropy of discrete random variable $X$ is defined as:

$$
H(X) = -\sum_{i=1}^{n} p(x_i) \log_2 p(x_i)
$$

其中 $p(x_i)$ 是 $X$ 取值为 $x_i$ 的概率。

Where $p(x_i)$ is the probability that $X$ takes value $x_i$.

**定义 1.2 (联合熵 / Joint Entropy)**
两个随机变量 $X$ 和 $Y$ 的联合熵定义为：

The joint entropy of two random variables $X$ and $Y$ is defined as:

$$
H(X, Y) = -\sum_{i,j} p(x_i, y_j) \log_2 p(x_i, y_j)
$$

**定义 1.3 (条件熵 / Conditional Entropy)**
给定 $Y$ 的条件下 $X$ 的条件熵定义为：

The conditional entropy of $X$ given $Y$ is defined as:

$$
H(X|Y) = -\sum_{i,j} p(x_i, y_j) \log_2 p(x_i|y_j)
$$

**定理 1.1 (熵的基本性质 / Basic Properties of Entropy)**:

1. $H(X) \geq 0$ / $H(X) \geq 0$
2. $H(X) \leq \log_2 |\mathcal{X}|$ / $H(X) \leq \log_2 |\mathcal{X}|$
3. $H(X, Y) \leq H(X) + H(Y)$ / $H(X, Y) \leq H(X) + H(Y)$

```haskell
-- 信息熵 / Information Entropy
class InformationMeasure a where
    -- 信息熵 / Information entropy
    entropy :: a -> Double
    
    -- 联合熵 / Joint entropy
    jointEntropy :: a -> a -> Double
    
    -- 条件熵 / Conditional entropy
    conditionalEntropy :: a -> a -> Double
    
    -- 互信息 / Mutual information
    mutualInformation :: a -> a -> Double

-- 离散概率分布 / Discrete Probability Distribution
data DiscreteDistribution a = DiscreteDistribution
    { outcomes :: [a]
    , probabilities :: [Double]
    }

-- 概率分布实例 / Probability Distribution Instance
instance (Eq a) => InformationMeasure (DiscreteDistribution a) where
    entropy dist = 
        let ps = probabilities dist
        in negate $ sum [p * logBase 2 p | p <- ps, p > 0]
    
    jointEntropy dist1 dist2 = 
        let jointProbs = jointProbabilities dist1 dist2
        in negate $ sum [p * logBase 2 p | p <- jointProbs, p > 0]
    
    conditionalEntropy dist1 dist2 = 
        let jointProbs = jointProbabilities dist1 dist2
            marginalProbs2 = marginalProbabilities dist2
            conditionalProbs = conditionalProbabilities jointProbs marginalProbs2
        in negate $ sum [p * logBase 2 p | p <- conditionalProbs, p > 0]
    
    mutualInformation dist1 dist2 = 
        entropy dist1 + entropy dist2 - jointEntropy dist1 dist2

-- 联合概率计算 / Joint Probability Calculation
jointProbabilities :: DiscreteDistribution a -> DiscreteDistribution b -> [Double]
jointProbabilities dist1 dist2 = 
    [p1 * p2 | p1 <- probabilities dist1, p2 <- probabilities dist2]

-- 边缘概率计算 / Marginal Probability Calculation
marginalProbabilities :: DiscreteDistribution a -> [Double]
marginalProbabilities = probabilities

-- 条件概率计算 / Conditional Probability Calculation
conditionalProbabilities :: [Double] -> [Double] -> [Double]
conditionalProbabilities jointProbs marginalProbs = 
    [if p2 > 0 then p1 / p2 else 0 | (p1, p2) <- zip jointProbs marginalProbs]

-- 熵计算示例 / Entropy Calculation Example
entropyExample :: Double
entropyExample = 
    let fairCoin = DiscreteDistribution [True, False] [0.5, 0.5]
    in entropy fairCoin  -- 应该等于 1.0

-- 互信息计算示例 / Mutual Information Calculation Example
mutualInformationExample :: Double
mutualInformationExample = 
    let dist1 = DiscreteDistribution [1, 2] [0.5, 0.5]
        dist2 = DiscreteDistribution [1, 2] [0.5, 0.5]
    in mutualInformation dist1 dist2
```

### 2. 信道理论 / Channel Theory

**定义 2.1 (离散无记忆信道 / Discrete Memoryless Channel)**
离散无记忆信道是三元组 $(\mathcal{X}, \mathcal{Y}, p(y|x))$，其中：

A discrete memoryless channel is a triple $(\mathcal{X}, \mathcal{Y}, p(y|x))$, where:

- $\mathcal{X}$ 是输入字母表 / $\mathcal{X}$ is the input alphabet
- $\mathcal{Y}$ 是输出字母表 / $\mathcal{Y}$ is the output alphabet
- $p(y|x)$ 是转移概率 / $p(y|x)$ is the transition probability

**定义 2.2 (信道容量 / Channel Capacity)**
信道容量定义为：

Channel capacity is defined as:

$$
C = \max_{p(x)} I(X; Y)
$$

其中 $I(X; Y)$ 是 $X$ 和 $Y$ 之间的互信息。

Where $I(X; Y)$ is the mutual information between $X$ and $Y$.

**定理 2.1 (香农信道编码定理 / Shannon's Channel Coding Theorem)**
对于任何传输速率 $R < C$，存在编码方案使得误码率可以任意小。

For any transmission rate $R < C$, there exists a coding scheme such that the error rate can be made arbitrarily small.

```haskell
-- 信道模型 / Channel Model
data Channel input output = Channel
    { inputAlphabet :: [input]
    , outputAlphabet :: [output]
    , transitionMatrix :: [[Double]]  -- p(y|x)
    }

-- 信道容量计算 / Channel Capacity Calculation
channelCapacity :: (Eq input, Eq output) => Channel input output -> Double
channelCapacity channel = 
    let inputDistributions = generateInputDistributions (inputAlphabet channel)
        mutualInformations = map (\p -> mutualInformationForChannel channel p) inputDistributions
    in maximum mutualInformations

-- 生成输入分布 / Generate Input Distributions
generateInputDistributions :: [a] -> [[Double]]
generateInputDistributions alphabet = 
    let n = length alphabet
        step = 0.1
        values = [0, step..1]
    in [[p1, p2, p3, p4] | p1 <- values, p2 <- values, p3 <- values, p4 <- values,
                          abs (sum [p1, p2, p3, p4] - 1.0) < 0.01]

-- 信道互信息计算 / Channel Mutual Information Calculation
mutualInformationForChannel :: (Eq input, Eq output) => 
    Channel input output -> [Double] -> Double
mutualInformationForChannel channel inputProbs = 
    let jointProbs = jointProbabilitiesForChannel channel inputProbs
        outputProbs = marginalOutputProbabilities jointProbs
        conditionalProbs = conditionalProbabilitiesForChannel jointProbs outputProbs
    in entropy (DiscreteDistribution (outputAlphabet channel) outputProbs) -
       conditionalEntropy (DiscreteDistribution (outputAlphabet channel) outputProbs)
                         (DiscreteDistribution (inputAlphabet channel) inputProbs)

-- 二元对称信道 / Binary Symmetric Channel
binarySymmetricChannel :: Double -> Channel Bool Bool
binarySymmetricChannel p = Channel
    { inputAlphabet = [True, False]
    , outputAlphabet = [True, False]
    , transitionMatrix = [[1-p, p], [p, 1-p]]
    }

-- 二元擦除信道 / Binary Erasure Channel
binaryErasureChannel :: Double -> Channel Bool (Maybe Bool)
binaryErasureChannel p = Channel
    { inputAlphabet = [True, False]
    , outputAlphabet = [Just True, Just False, Nothing]
    , transitionMatrix = [[1-p, 0, p], [0, 1-p, p]]
    }
```

### 3. 编码理论 / Coding Theory

**定义 3.1 (前缀码 / Prefix Code)**
前缀码是满足前缀条件的编码，即没有任何码字是其他码字的前缀。

A prefix code is a code satisfying the prefix condition, i.e., no codeword is a prefix of any other codeword.

**定义 3.2 (霍夫曼编码 / Huffman Coding)**
霍夫曼编码是一种最优前缀码，通过构建霍夫曼树得到。

Huffman coding is an optimal prefix code obtained by constructing a Huffman tree.

**定理 3.1 (霍夫曼编码最优性 / Huffman Coding Optimality)**
霍夫曼编码在所有前缀码中具有最小的平均码长。

Huffman coding has the minimum average codeword length among all prefix codes.

```haskell
-- 编码 / Code
data Code symbol = Code
    { symbols :: [symbol]
    , codewords :: [String]
    }

-- 前缀码检查 / Prefix Code Check
isPrefixCode :: Code a -> Bool
isPrefixCode code = 
    let words = codewords code
    in not $ any (\w1 -> any (\w2 -> w1 /= w2 && isPrefixOf w1 w2) words) words

-- 霍夫曼树 / Huffman Tree
data HuffmanTree a = Leaf a Double | Node (HuffmanTree a) (HuffmanTree a) Double

-- 霍夫曼编码构建 / Huffman Code Construction
huffmanCode :: [(a, Double)] -> Code a
huffmanCode symbolProbs = 
    let tree = buildHuffmanTree symbolProbs
        symbolToCode = buildCodeMap tree
        symbols = map fst symbolProbs
        codewords = map (symbolToCode Map.!) symbols
    in Code symbols codewords

-- 构建霍夫曼树 / Build Huffman Tree
buildHuffmanTree :: [(a, Double)] -> HuffmanTree a
buildHuffmanTree [(symbol, prob)] = Leaf symbol prob
buildHuffmanTree symbolProbs = 
    let sorted = sortBy (compare `on` snd) symbolProbs
        (symbol1, prob1) = head sorted
        (symbol2, prob2) = head (tail sorted)
        remaining = drop 2 sorted
        newNode = Node (Leaf symbol1 prob1) (Leaf symbol2 prob2) (prob1 + prob2)
    in buildHuffmanTree (remaining ++ [(newNode, prob1 + prob2)])

-- 构建编码映射 / Build Code Map
buildCodeMap :: HuffmanTree a -> Map.Map a String
buildCodeMap tree = buildCodeMapHelper tree ""
  where
    buildCodeMapHelper (Leaf symbol _) code = Map.singleton symbol code
    buildCodeMapHelper (Node left right _) code = 
        Map.union (buildCodeMapHelper left (code ++ "0"))
                 (buildCodeMapHelper right (code ++ "1"))

-- 香农编码 / Shannon Coding
shannonCode :: [(a, Double)] -> Code a
shannonCode symbolProbs = 
    let sorted = sortBy (flip compare `on` snd) symbolProbs
        cumulativeProbs = scanl1 (+) (map snd sorted)
        codewords = map (shannonCodeword . fst) (zip cumulativeProbs (map snd sorted))
        symbols = map fst sorted
    in Code symbols codewords

-- 香农码字生成 / Shannon Codeword Generation
shannonCodeword :: Double -> String
shannonCodeword prob = 
    let length = ceiling (-logBase 2 prob)
        binary = toBinary prob length
    in take length binary

-- 二进制转换 / Binary Conversion
toBinary :: Double -> Int -> String
toBinary x n = 
    let integerPart = floor (x * 2^n)
    in reverse $ take n $ map (\i -> if odd (integerPart `div` 2^i) then '1' else '0') [0..]
```

### 4. 数据压缩 / Data Compression

**定义 4.1 (无损压缩 / Lossless Compression)**
无损压缩是能够完全恢复原始数据的压缩方法。

Lossless compression is a compression method that can completely recover the original data.

**定义 4.2 (有损压缩 / Lossy Compression)**
有损压缩是允许一定信息损失的压缩方法。

Lossy compression is a compression method that allows some information loss.

**定理 4.1 (香农无失真编码定理 / Shannon's Noiseless Coding Theorem)**
对于熵为 $H$ 的信息源，平均码长 $L$ 满足：

For an information source with entropy $H$, the average codeword length $L$ satisfies:

$$
H \leq L < H + 1
```

```haskell
-- 压缩器 / Compressor
class Compressor a where
    -- 压缩 / Compress
    compress :: a -> String

    -- 解压缩 / Decompress
    decompress :: String -> a

    -- 压缩比 / Compression ratio
    compressionRatio :: a -> Double

-- 游程编码 / Run-length Encoding
data RunLengthCode = RunLengthCode
    { runs :: [(Char, Int)]
    }

instance Compressor String where
    compress str =
        let runs = runLengthEncode str
        in concatMap (\(c, n) -> c : show n) runs

    decompress str =
        let runs = runLengthDecode str
        in concatMap (\(c, n) -> replicate n c) runs

    compressionRatio str =
        let compressed = compress str
        in fromIntegral (length compressed) / fromIntegral (length str)

-- 游程编码 / Run-length Encoding
runLengthEncode :: String -> [(Char, Int)]
runLengthEncode [] = []
runLengthEncode (c:cs) =
    let (same, rest) = span (== c) cs
        count = 1 + length same
    in (c, count) : runLengthEncode rest

-- 游程解码 / Run-length Decoding
runLengthDecode :: String -> [(Char, Int)]
runLengthDecode [] = []
runLengthDecode (c:cs) =
    let (digits, rest) = span isDigit cs
        count = read digits :: Int
    in (c, count) : runLengthDecode rest

-- LZ77压缩 / LZ77 Compression
data LZ77Code = LZ77Code
    { tokens :: [(Int, Int, Char)]  -- (offset, length, next_char)
    }

-- LZ77压缩 / LZ77 Compression
lz77Compress :: String -> LZ77Code
lz77Compress str =
    let tokens = lz77CompressHelper str 0 ""
    in LZ77Code tokens

-- LZ77压缩辅助函数 / LZ77 Compression Helper
lz77CompressHelper :: String -> Int -> String -> [(Int, Int, Char)]
lz77CompressHelper [] _ _ = []
lz77CompressHelper (c:cs) pos window =
    let match = findLongestMatch (c:cs) window
        (offset, length) = case match of
            Just (off, len) -> (off, len)
            Nothing -> (0, 0)
        nextChar = if pos + length < length (c:cs)
                   then (c:cs) !! length
                   else '\0'
        newWindow = take 4096 (window ++ take length (c:cs))
    in (offset, length, nextChar) :
       lz77CompressHelper (drop (length + 1) (c:cs)) (pos + length + 1) newWindow

-- 最长匹配查找 / Longest Match Finding
findLongestMatch :: String -> String -> Maybe (Int, Int)
findLongestMatch input window =
    let matches = [(offset, length) | offset <- [1..length window],
                                     length <- [1..min (length input) (length window - offset + 1)],
                                     take length input == take length (drop (offset - 1) window)]
    in if null matches then Nothing else Just (maximumBy (compare `on` snd) matches)
```

## 形式化证明 / Formal Proofs

### 定理 1 (信息论基本定理 / Basic Information Theory Theorems)

**定理 1.1 (熵的凸性 / Convexity of Entropy)**
熵函数 $H(p)$ 是概率分布 $p$ 的凹函数。

The entropy function $H(p)$ is a concave function of probability distribution $p$.

**证明 / Proof**：
通过詹森不等式证明 / Prove through Jensen's inequality.

### 定理 2 (编码定理 / Coding Theorems)

**定理 2.1 (香农无失真编码定理 / Shannon's Noiseless Coding Theorem)**
对于熵为 $H$ 的信息源，存在编码方案使得平均码长 $L$ 满足 $H \leq L < H + 1$。

For an information source with entropy $H$, there exists a coding scheme such that the average codeword length $L$ satisfies $H \leq L < H + 1$.

**证明 / Proof**：
通过香农编码构造证明 / Prove through Shannon coding construction.

### 定理 3 (信道编码定理 / Channel Coding Theorems)

**定理 3.1 (香农信道编码定理 / Shannon's Channel Coding Theorem)**
对于任何传输速率 $R < C$，存在编码方案使得误码率可以任意小。

For any transmission rate $R < C$, there exists a coding scheme such that the error rate can be made arbitrarily small.

**证明 / Proof**：
通过随机编码和典型序列证明 / Prove through random coding and typical sequences.

## 应用领域 / Application Domains

### 1. 数据压缩 / Data Compression
- **无损压缩 / Lossless Compression**: ZIP、GZIP、PNG / ZIP, GZIP, PNG
- **有损压缩 / Lossy Compression**: JPEG、MP3、MPEG / JPEG, MP3, MPEG
- **图像压缩 / Image Compression**: 变换编码、预测编码 / Transform coding, predictive coding

### 2. 通信系统 / Communication Systems
- **数字通信 / Digital Communication**: 调制解调、信道编码 / Modulation/demodulation, channel coding
- **网络协议 / Network Protocols**: 错误检测、纠错编码 / Error detection, error correction coding
- **无线通信 / Wireless Communication**: 多径衰落、信道估计 / Multipath fading, channel estimation

### 3. 机器学习 / Machine Learning
- **特征选择 / Feature Selection**: 互信息、信息增益 / Mutual information, information gain
- **模型选择 / Model Selection**: 最小描述长度、贝叶斯信息准则 / Minimum description length, Bayesian information criterion
- **深度学习 / Deep Learning**: 信息瓶颈、互信息最大化 / Information bottleneck, mutual information maximization

### 4. 密码学 / Cryptography
- **信息论安全 / Information-theoretic Security**: 完美保密、无条件安全 / Perfect secrecy, unconditional security
- **熵源 / Entropy Sources**: 随机数生成、密钥生成 / Random number generation, key generation
- **侧信道攻击 / Side-channel Attacks**: 信息泄露分析 / Information leakage analysis

## 批判性分析 / Critical Analysis

### 1. 信息论争议 / Information Theory Controversies

**争议 1.1 (信息定义 / Definition of Information)**:
- **香农信息 vs 语义信息 / Shannon Information vs Semantic Information**: 信息论是否考虑语义内容 / Whether information theory considers semantic content
- **主观信息 vs 客观信息 / Subjective vs Objective Information**: 信息的客观性vs主观性 / Objectivity vs subjectivity of information

**争议 1.2 (熵的解释 / Interpretation of Entropy)**:
- **热力学熵 vs 信息熵 / Thermodynamic Entropy vs Information Entropy**: 两种熵的关系和区别 / Relationship and difference between the two types of entropy
- **最大熵原理 / Maximum Entropy Principle**: 最大熵原理的哲学基础 / Philosophical foundation of maximum entropy principle

### 2. 理论局限性 / Theoretical Limitations

**局限性 2.1 (假设限制 / Assumption Limitations)**:
- **无记忆性假设 / Memoryless Assumption**: 实际系统往往有记忆性 / Real systems often have memory
- **平稳性假设 / Stationarity Assumption**: 非平稳过程的处理困难 / Difficulty in handling non-stationary processes

**局限性 2.2 (计算复杂性 / Computational Complexity)**:
- **信道容量计算 / Channel Capacity Calculation**: 高维信道的容量计算困难 / Difficulty in calculating capacity of high-dimensional channels
- **最优编码构造 / Optimal Code Construction**: 最优编码的构造复杂性 / Complexity of constructing optimal codes

### 3. 前沿趋势 / Frontier Trends

**趋势 3.1 (量子信息论 / Quantum Information Theory)**:
- **量子熵 / Quantum Entropy**: 冯·诺依曼熵、量子互信息 / von Neumann entropy, quantum mutual information
- **量子信道 / Quantum Channels**: 量子信道容量、量子编码 / Quantum channel capacity, quantum coding

**趋势 3.2 (网络信息论 / Network Information Theory)**:
- **多用户信道 / Multi-user Channels**: 广播信道、多址信道 / Broadcast channels, multiple access channels
- **网络编码 / Network Coding**: 网络信息流优化 / Network information flow optimization

**趋势 3.3 (信息几何 / Information Geometry)**:
- **信息流形 / Information Manifolds**: 概率分布的几何结构 / Geometric structure of probability distributions
- **自然梯度 / Natural Gradients**: 信息几何在机器学习中的应用 / Applications of information geometry in machine learning

## 交叉引用 / Cross References

- [数学基础 / Mathematical Foundations](./101-Mathematical-Foundations.md) - 数学理论基础 / Mathematical theoretical foundation
- [概率论 / Probability Theory](./108-Probability-Statistics.md) - 概率统计基础 / Probability and statistics foundation
- [自动机理论 / Automata Theory](./006-Automata-Theory.md) - 计算模型 / Computational models
- [复杂性理论 / Complexity Theory](./112-Computational-Complexity-Theory.md) - 计算复杂性 / Computational complexity

## 参考文献 / References

1. Shannon, C.E. (1948). *A Mathematical Theory of Communication*. Bell System Technical Journal.
2. Cover, T.M., & Thomas, J.A. (2006). *Elements of Information Theory*. Wiley.
3. MacKay, D.J.C. (2003). *Information Theory, Inference, and Learning Algorithms*. Cambridge University Press.
4. Gallager, R.G. (1968). *Information Theory and Reliable Communication*. Wiley.
5. Blahut, R.E. (1987). *Principles and Practice of Information Theory*. Addison-Wesley.
6. Yeung, R.W. (2008). *Information Theory and Network Coding*. Springer.
7. Nielsen, M.A., & Chuang, I.L. (2010). *Quantum Computation and Quantum Information*. Cambridge University Press.
8. Amari, S.I. (2016). *Information Geometry and Its Applications*. Springer.

---

`#InformationTheory #Entropy #MutualInformation #ChannelCapacity #CodingTheory #DataCompression #CommunicationSystems #MachineLearning #Cryptography #QuantumInformationTheory #NetworkInformationTheory #InformationGeometry #Haskell #FormalMethods #MathematicalFoundations #ProbabilityTheory #AutomataTheory #ComplexityTheory`
