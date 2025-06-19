# 011. 图灵机理论 (Turing Machines Theory)

## 1. 概述

图灵机是计算理论的核心模型，由艾伦·图灵在1936年提出。它提供了可计算性的形式化定义，是计算机科学和形式语言理论的基础。图灵机对应乔姆斯基层次结构中的0型语言，具有最强的计算能力。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[012-Computability-Theory]] - 可计算性理论
- [[006-Operational-Semantics]] - 操作语义

## 2. 数学基础

### 2.1 标准图灵机定义

**定义 2.1.1** (标准图灵机)
标准图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表，$\Sigma \subseteq \Gamma$
- $\Gamma$ 是有限带字母表
- $\delta: Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集

**定义 2.1.2** (瞬时描述)
图灵机的瞬时描述是一个三元组 $(q, \alpha, i)$，其中：
- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是带内容
- $i \in \mathbb{N}$ 是读写头位置

**定义 2.1.3** (转移关系)
瞬时描述间的转移关系 $\vdash_M$ 定义为：

如果 $\delta(q, \alpha_i) = (q', b, D)$，则：
$$(q, \alpha, i) \vdash_M (q', \alpha', i')$$

其中：
- $\alpha'_j = \begin{cases} b & \text{if } j = i \\ \alpha_j & \text{otherwise} \end{cases}$
- $i' = \begin{cases} i-1 & \text{if } D = L \\ i+1 & \text{if } D = R \end{cases}$

**定义 2.1.4** (语言接受)
图灵机 $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid (q_0, w, 0) \vdash_M^* (q, \alpha, i), q \in F\}$$

### 2.2 非确定性图灵机

**定义 2.2.1** (非确定性图灵机)
非确定性图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表，$\Sigma \subseteq \Gamma$
- $\Gamma$ 是有限带字母表
- $\delta: Q \times \Gamma \to 2^{Q \times \Gamma \times \{L, R\}}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集

**定理 2.2.1** (非确定性与确定性等价)
对于每个非确定性图灵机，存在等价的确定性图灵机。

**证明**: 通过模拟构造，确定性图灵机可以模拟非确定性图灵机的所有可能计算路径。

### 2.3 多带图灵机

**定义 2.3.1** (k带图灵机)
k带图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限带字母表
- $\delta: Q \times \Gamma^k \to Q \times \Gamma^k \times \{L, R\}^k$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集

**定理 2.3.1** (多带与单带等价)
对于每个k带图灵机，存在等价的单带图灵机。

**证明**: 通过带交错技术，将k个带的内容交错存储在一个带上。

## 3. Haskell 实现

### 3.1 图灵机数据类型

```haskell
-- | 图灵机方向
data Direction = L | R deriving (Show, Eq, Ord)

-- | 图灵机转移
data Transition q a = Transition
  { nextState :: q
  , writeSymbol :: a
  , moveDirection :: Direction
  } deriving (Show, Eq, Ord)

-- | 标准图灵机
data TuringMachine q a = TuringMachine
  { states :: Set q                    -- 状态集 Q
  , inputAlphabet :: Set a             -- 输入字母表 Σ
  , tapeAlphabet :: Set a              -- 带字母表 Γ
  , transition :: q -> a -> Transition q a  -- 转移函数 δ
  , startState :: q                    -- 初始状态 q₀
  , blankSymbol :: a                   -- 空白符号 B
  , acceptStates :: Set q              -- 接受状态集 F
  }

-- | 非确定性图灵机
data NDTuringMachine q a = NDTuringMachine
  { ndStates :: Set q
  , ndInputAlphabet :: Set a
  , ndTapeAlphabet :: Set a
  , ndTransition :: q -> a -> Set (Transition q a)
  , ndStartState :: q
  , ndBlankSymbol :: a
  , ndAcceptStates :: Set q
  }

-- | 瞬时描述
data Configuration q a = Configuration
  { currentState :: q
  , tapeContent :: [a]
  , headPosition :: Int
  } deriving (Show, Eq, Ord)

-- | 图灵机执行结果
data ExecutionResult q a
  = Accept q [a] Int    -- 接受状态，最终带内容，最终位置
  | Reject q [a] Int    -- 拒绝状态，最终带内容，最终位置
  | Loop                -- 无限循环
  deriving (Show, Eq)
```

### 3.2 图灵机执行

```haskell
-- | 执行图灵机
executeTM :: (Ord q, Ord a) => TuringMachine q a -> [a] -> ExecutionResult q a
executeTM tm input = executeWithHistory tm input (singleton initialConfig)
  where
    initialConfig = Configuration 
      { currentState = startState tm
      , tapeContent = input
      , headPosition = 0
      }

-- | 带历史记录的执行
executeWithHistory :: (Ord q, Ord a) => 
                      TuringMachine q a -> 
                      [a] -> 
                      Set (Configuration q a) -> 
                      ExecutionResult q a
executeWithHistory tm input history
  | any (\conf -> currentState conf `member` acceptStates tm) currentConfigs = 
      let acceptingConf = head [conf | conf <- toList currentConfigs, 
                                      currentState conf `member` acceptStates tm]
      in Accept (currentState acceptingConf) 
                (tapeContent acceptingConf) 
                (headPosition acceptingConf)
  | any (\conf -> currentState conf `notMember` acceptStates tm && 
                  null (nextConfigurations tm conf)) currentConfigs = 
      let rejectingConf = head [conf | conf <- toList currentConfigs, 
                                      currentState conf `notMember` acceptStates tm,
                                      null (nextConfigurations tm conf)]
      in Reject (currentState rejectingConf) 
                (tapeContent rejectingConf) 
                (headPosition rejectingConf)
  | otherwise = 
      let newConfigs = unions [fromList (nextConfigurations tm conf) | 
                               conf <- toList currentConfigs]
          allConfigs = history `union` newConfigs
      in if newConfigs `isSubsetOf` history 
         then Loop 
         else executeWithHistory tm input allConfigs
  where
    currentConfigs = [conf | conf <- toList history, 
                            not (any (\prev -> prev == conf) (init (toList history)))]

-- | 计算下一个配置
nextConfigurations :: (Ord q, Ord a) => TuringMachine q a -> Configuration q a -> [Configuration q a]
nextConfigurations tm conf = 
  case safeRead (tapeContent conf) (headPosition conf) of
    Just symbol -> 
      let trans = transition tm (currentState conf) symbol
          newTape = safeWrite (tapeContent conf) (headPosition conf) (writeSymbol trans)
          newPos = case moveDirection trans of
                     L -> headPosition conf - 1
                     R -> headPosition conf + 1
      in [Configuration 
            { currentState = nextState trans
            , tapeContent = newTape
            , headPosition = newPos
            }]
    Nothing -> []

-- | 安全读取带内容
safeRead :: [a] -> Int -> Maybe a
safeRead tape pos
  | pos >= 0 && pos < length tape = Just (tape !! pos)
  | otherwise = Nothing

-- | 安全写入带内容
safeWrite :: [a] -> Int -> a -> [a]
safeWrite tape pos symbol
  | pos >= 0 && pos < length tape = 
      take pos tape ++ [symbol] ++ drop (pos + 1) tape
  | pos < 0 = [symbol] ++ replicate (-pos - 1) (head tape) ++ tape
  | otherwise = 
      tape ++ replicate (pos - length tape) (last tape) ++ [symbol]

-- | 检查语言接受
acceptsLanguage :: (Ord q, Ord a) => TuringMachine q a -> [a] -> Bool
acceptsLanguage tm input = 
  case executeTM tm input of
    Accept _ _ _ -> True
    _ -> False
```

### 3.3 通用图灵机

```haskell
-- | 图灵机编码
type TMCode = String

-- | 编码图灵机
encodeTM :: (Show q, Show a) => TuringMachine q a -> TMCode
encodeTM tm = 
  "TM:" ++ 
  encodeStates (states tm) ++ ":" ++
  encodeAlphabet (inputAlphabet tm) ++ ":" ++
  encodeAlphabet (tapeAlphabet tm) ++ ":" ++
  encodeTransitions (transition tm) (states tm) (tapeAlphabet tm) ++ ":" ++
  show (startState tm) ++ ":" ++
  show (blankSymbol tm) ++ ":" ++
  encodeStates (acceptStates tm)

-- | 编码状态集
encodeStates :: Show q => Set q -> String
encodeStates states = 
  "{" ++ intercalate "," (map show (toList states)) ++ "}"

-- | 编码字母表
encodeAlphabet :: Show a => Set a -> String
encodeAlphabet alphabet = 
  "{" ++ intercalate "," (map show (toList alphabet)) ++ "}"

-- | 编码转移函数
encodeTransitions :: (Show q, Show a) => 
                     (q -> a -> Transition q a) -> 
                     Set q -> 
                     Set a -> 
                     String
encodeTransitions transFunc states alphabet = 
  "{" ++ intercalate "," transitions ++ "}"
  where
    transitions = [show (q, a, trans) | 
                   q <- toList states,
                   a <- toList alphabet,
                   let trans = transFunc q a]

-- | 通用图灵机
universalTM :: TuringMachine String String
universalTM = TuringMachine
  { states = fromList ["q0", "q1", "q2", "q3", "q_accept", "q_reject"]
  , inputAlphabet = fromList ["0", "1", "#", "|"]
  , tapeAlphabet = fromList ["0", "1", "#", "|", "B"]
  , transition = \q a -> case (q, a) of
      ("q0", "#") -> Transition "q1" "#" R
      ("q1", "|") -> Transition "q2" "|" R
      ("q2", "0") -> Transition "q2" "0" R
      ("q2", "1") -> Transition "q2" "1" R
      ("q2", "#") -> Transition "q3" "#" L
      ("q3", "0") -> Transition "q3" "0" L
      ("q3", "1") -> Transition "q3" "1" L
      ("q3", "|") -> Transition "q_accept" "|" R
      _ -> Transition "q_reject" a R
  , startState = "q0"
  , blankSymbol = "B"
  , acceptStates = fromList ["q_accept"]
  }

-- | 模拟图灵机
simulateTM :: TMCode -> [String] -> ExecutionResult String String
simulateTM code input = 
  case parseTMCode code of
    Just tm -> executeTM tm input
    Nothing -> Reject "parse_error" [] 0

-- | 解析图灵机编码
parseTMCode :: TMCode -> Maybe (TuringMachine String String)
parseTMCode code = 
  case splitOn ":" code of
    ["TM", statesStr, inputAlphStr, tapeAlphStr, transStr, startStr, blankStr, acceptStr] ->
      Just TuringMachine
        { states = parseStates statesStr
        , inputAlphabet = parseAlphabet inputAlphStr
        , tapeAlphabet = parseAlphabet tapeAlphStr
        , transition = parseTransitions transStr
        , startState = startStr
        , blankSymbol = blankStr
        , acceptStates = parseStates acceptStr
        }
    _ -> Nothing
  where
    parseStates = fromList . map read . splitOn "," . init . tail
    parseAlphabet = fromList . map read . splitOn "," . init . tail
    parseTransitions = undefined -- 实现转移函数解析
```

### 3.4 多带图灵机实现

```haskell
-- | 多带配置
data MultiTapeConfiguration q a = MultiTapeConfiguration
  { mtCurrentState :: q
  , mtTapes :: [[a]]
  , mtHeadPositions :: [Int]
  } deriving (Show, Eq, Ord)

-- | 多带图灵机
data MultiTapeTM q a = MultiTapeTM
  { mtStates :: Set q
  , mtInputAlphabet :: Set a
  , mtTapeAlphabet :: Set a
  , mtTransition :: q -> [a] -> (q, [a], [Direction])
  , mtStartState :: q
  , mtBlankSymbol :: a
  , mtAcceptStates :: Set q
  , mtTapeCount :: Int
  }

-- | 执行多带图灵机
executeMultiTapeTM :: (Ord q, Ord a) => MultiTapeTM q a -> [a] -> ExecutionResult q a
executeMultiTapeTM mtm input = 
  executeMultiTapeWithHistory mtm (replicate (mtTapeCount mtm) input) 
                              (singleton initialConfig)
  where
    initialConfig = MultiTapeConfiguration
      { mtCurrentState = mtStartState mtm
      , mtTapes = replicate (mtTapeCount mtm) input
      , mtHeadPositions = replicate (mtTapeCount mtm) 0
      }

-- | 带历史记录的多带执行
executeMultiTapeWithHistory :: (Ord q, Ord a) => 
                               MultiTapeTM q a -> 
                               [[a]] -> 
                               Set (MultiTapeConfiguration q a) -> 
                               ExecutionResult q a
executeMultiTapeWithHistory mtm input history
  | any (\conf -> mtCurrentState conf `member` mtAcceptStates mtm) currentConfigs = 
      let acceptingConf = head [conf | conf <- toList currentConfigs, 
                                      mtCurrentState conf `member` mtAcceptStates mtm]
      in Accept (mtCurrentState acceptingConf) 
                (head (mtTapes acceptingConf)) 
                (head (mtHeadPositions acceptingConf))
  | otherwise = 
      let newConfigs = unions [fromList (nextMultiTapeConfigurations mtm conf) | 
                               conf <- toList currentConfigs]
          allConfigs = history `union` newConfigs
      in if newConfigs `isSubsetOf` history 
         then Loop 
         else executeMultiTapeWithHistory mtm input allConfigs
  where
    currentConfigs = [conf | conf <- toList history, 
                            not (any (\prev -> prev == conf) (init (toList history)))]

-- | 计算下一个多带配置
nextMultiTapeConfigurations :: (Ord q, Ord a) => 
                               MultiTapeTM q a -> 
                               MultiTapeConfiguration q a -> 
                               [MultiTapeConfiguration q a]
nextMultiTapeConfigurations mtm conf = 
  let symbols = [safeRead (mtTapes conf !! i) (mtHeadPositions conf !! i) | 
                 i <- [0..mtTapeCount mtm - 1]]
  in if all isJust symbols
     then let (newState, newSymbols, directions) = 
                mtTransition mtm (map fromJust symbols)
              newTapes = zipWith3 (\tape pos sym -> 
                                    safeWrite tape pos sym) 
                                  (mtTapes conf) 
                                  (mtHeadPositions conf) 
                                  newSymbols
              newPositions = zipWith (\pos dir -> 
                                       case dir of
                                         L -> pos - 1
                                         R -> pos + 1) 
                                     (mtHeadPositions conf) 
                                     directions
          in [MultiTapeConfiguration
                { mtCurrentState = newState
                , mtTapes = newTapes
                , mtHeadPositions = newPositions
                }]
     else []
```

## 4. 应用实例

### 4.1 语言识别器

```haskell
-- | 识别 a^n b^n 的图灵机
anbnTM :: TuringMachine String Char
anbnTM = TuringMachine
  { states = fromList ["q0", "q1", "q2", "q3", "q4", "q_accept", "q_reject"]
  , inputAlphabet = fromList ['a', 'b']
  , tapeAlphabet = fromList ['a', 'b', 'X', 'Y', 'B']
  , transition = \q a -> case (q, a) of
      ("q0", 'a') -> Transition "q1" 'X' R  -- 标记第一个a
      ("q0", 'B') -> Transition "q_accept" 'B' R  -- 空串
      ("q1", 'a') -> Transition "q1" 'a' R  -- 继续读取a
      ("q1", 'b') -> Transition "q2" 'Y' L  -- 找到第一个b，标记并回退
      ("q2", 'a') -> Transition "q2" 'a' L  -- 继续回退
      ("q2", 'X') -> Transition "q3" 'X' R  -- 找到标记的X，开始下一轮
      ("q3", 'a') -> Transition "q1" 'X' R  -- 标记下一个a
      ("q3", 'Y') -> Transition "q4" 'Y' R  -- 检查是否所有a都被处理
      ("q4", 'Y') -> Transition "q4" 'Y' R  -- 继续检查Y
      ("q4", 'B') -> Transition "q_accept" 'B' R  -- 接受
      _ -> Transition "q_reject" a R  -- 拒绝
  , startState = "q0"
  , blankSymbol = 'B'
  , acceptStates = fromList ["q_accept"]
  }

-- | 测试 a^n b^n 识别器
testAnBn :: [String] -> [Bool]
testAnBn inputs = map (acceptsLanguage anbnTM) inputs

-- | 测试用例
anbnTestCases :: [String]
anbnTestCases = ["", "ab", "aabb", "aaabbb", "aab", "abb", "ba"]
```

### 4.2 计算器

```haskell
-- | 二进制加法图灵机
binaryAdderTM :: MultiTapeTM String Char
binaryAdderTM = MultiTapeTM
  { mtStates = fromList ["q0", "q1", "q2", "q3", "q_accept"]
  , mtInputAlphabet = fromList ['0', '1']
  , mtTapeAlphabet = fromList ['0', '1', 'B']
  , mtTransition = \q symbols -> case (q, symbols) of
      ("q0", ['0', '0', 'B']) -> ("q1", ['0', '0', '0'], [R, R, R])
      ("q0", ['0', '1', 'B']) -> ("q1", ['0', '1', '1'], [R, R, R])
      ("q0", ['1', '0', 'B']) -> ("q1", ['1', '0', '1'], [R, R, R])
      ("q0", ['1', '1', 'B']) -> ("q1", ['1', '1', '0'], [R, R, R])
      ("q1", ['0', '0', '0']) -> ("q1", ['0', '0', '0'], [R, R, R])
      ("q1", ['0', '1', '1']) -> ("q1", ['0', '1', '1'], [R, R, R])
      ("q1", ['1', '0', '1']) -> ("q1", ['1', '0', '1'], [R, R, R])
      ("q1", ['1', '1', '0']) -> ("q1", ['1', '1', '0'], [R, R, R])
      ("q1", ['B', 'B', 'B']) -> ("q_accept", ['B', 'B', 'B'], [R, R, R])
      _ -> ("q_accept", symbols, [R, R, R])
  , mtStartState = "q0"
  , mtBlankSymbol = 'B'
  , mtAcceptStates = fromList ["q_accept"]
  , mtTapeCount = 3
  }

-- | 执行二进制加法
binaryAdd :: String -> String -> String
binaryAdd a b = 
  case executeMultiTapeTM binaryAdderTM (a ++ "B" ++ b) of
    Accept _ result _ -> result
    _ -> "error"
```

## 5. 理论性质

### 5.1 丘奇-图灵论题

**丘奇-图灵论题**: 任何可计算的函数都可以由图灵机计算。

这个论题不是数学定理，而是一个关于计算本质的哲学假设。它基于以下观察：

1. 所有已知的计算模型都与图灵机等价
2. 图灵机能够模拟任何物理计算过程
3. 没有发现超越图灵机计算能力的计算模型

### 5.2 停机问题

**定理 5.2.1** (停机问题不可判定)
停机问题 $H = \{\langle M, w \rangle \mid M \text{ 是图灵机且 } M \text{ 在输入 } w \text{ 上停机}\}$ 是不可判定的。

**证明** (对角线法):
假设存在图灵机 $H$ 判定停机问题，构造图灵机 $D$：

```haskell
-- | 停机问题判定器 (假设存在)
haltingDecider :: TuringMachine String String -> [String] -> Bool
haltingDecider tm input = 
  case executeTM tm input of
    Accept _ _ _ -> True
    Reject _ _ _ -> True
    Loop -> False

-- | 对角线图灵机
diagonalTM :: TuringMachine String String -> [String] -> ExecutionResult String String
diagonalTM tm input = 
  if haltingDecider tm input
  then Loop  -- 如果停机，则进入无限循环
  else Accept "q_accept" [] 0  -- 如果不停机，则停机
```

这导致矛盾：$D(D)$ 停机当且仅当 $D(D)$ 不停机。

### 5.3 Rice定理

**定理 5.3.1** (Rice定理)
任何非平凡的语言性质都是不可判定的。

**定义**: 语言性质 $P$ 是非平凡的，如果存在图灵机 $M_1$ 使得 $L(M_1) \in P$，且存在图灵机 $M_2$ 使得 $L(M_2) \notin P$。

**应用**: 
- 语言是否为空集
- 语言是否为有限集
- 语言是否包含特定字符串
- 两个图灵机是否等价

## 6. 复杂度分析

### 6.1 时间复杂度

- **标准图灵机**: 无固定时间复杂度，取决于具体问题
- **线性有界自动机**: $O(n)$ 空间限制
- **确定性图灵机**: 与对应的非确定性图灵机等价

### 6.2 空间复杂度

- **标准图灵机**: 无限空间
- **线性有界自动机**: $O(n)$ 空间
- **对数空间图灵机**: $O(\log n)$ 空间

## 7. 扩展与变体

### 7.1 量子图灵机

```haskell
-- | 量子图灵机
data QuantumTM q a = QuantumTM
  { qtmStates :: Set q
  , qtmAlphabet :: Set a
  , qtmTransition :: q -> a -> [(q, a, Direction, Complex Double)]
  , qtmStartState :: q
  , qtmAcceptStates :: Set q
  }

-- | 量子配置
data QuantumConfiguration q a = QuantumConfiguration
  { qcState :: q
  , qcTape :: [a]
  , qcPosition :: Int
  , qcAmplitude :: Complex Double
  }

-- | 量子图灵机执行
executeQuantumTM :: (Ord q, Ord a) => 
                    QuantumTM q a -> 
                    [a] -> 
                    Map (q, [a], Int) (Complex Double)
executeQuantumTM qtm input = 
  quantumStep qtm (singleton (initialConfig, 1.0))
  where
    initialConfig = QuantumConfiguration
      { qcState = qtmStartState qtm
      , qcTape = input
      , qcPosition = 0
      , qcAmplitude = 1.0
      }

-- | 量子步骤
quantumStep :: (Ord q, Ord a) => 
               QuantumTM q a -> 
               Map (QuantumConfiguration q a) (Complex Double) -> 
               Map (q, [a], Int) (Complex Double)
quantumStep qtm configs = 
  foldl (\acc (config, amp) -> 
           Map.insertWith (+) (qcState config, qcTape config, qcPosition config) amp acc)
        Map.empty
        (Map.toList configs)
```

### 7.2 概率图灵机

```haskell
-- | 概率图灵机
data ProbabilisticTM q a = ProbabilisticTM
  { ptmStates :: Set q
  , ptmAlphabet :: Set a
  , ptmTransition :: q -> a -> [(q, a, Direction, Double)]
  , ptmStartState :: q
  , ptmAcceptStates :: Set q
  }

-- | 概率配置
data ProbabilisticConfiguration q a = ProbabilisticConfiguration
  { pcState :: q
  , pcTape :: [a]
  , pcPosition :: Int
  , pcProbability :: Double
  }

-- | 概率图灵机执行
executeProbabilisticTM :: (Ord q, Ord a) => 
                          ProbabilisticTM q a -> 
                          [a] -> 
                          Double
executeProbabilisticTM ptm input = 
  sum [prob | (config, prob) <- Map.toList finalConfigs,
              pcState config `member` ptmAcceptStates ptm]
  where
    finalConfigs = probabilisticStep ptm (singleton (initialConfig, 1.0))
    initialConfig = ProbabilisticConfiguration
      { pcState = ptmStartState ptm
      , pcTape = input
      , pcPosition = 0
      , pcProbability = 1.0
      }
```

## 8. 总结

图灵机理论为计算理论提供了坚实的基础，具有以下特点：

1. **通用性**: 能够计算任何可计算函数
2. **简单性**: 具有简单的数学模型
3. **等价性**: 与多种计算模型等价
4. **不可判定性**: 存在不可判定的问题
5. **扩展性**: 支持多种变体和扩展

图灵机在计算理论、形式语言理论、复杂性理论等领域有广泛应用，是计算机科学的核心概念。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[012-Computability-Theory]] - 可计算性理论 