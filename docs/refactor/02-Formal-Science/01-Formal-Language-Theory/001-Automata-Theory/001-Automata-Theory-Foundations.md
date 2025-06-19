# 自动机理论基础 (Automata Theory Foundations)

## 📚 概述

自动机理论是形式语言理论的核心，研究抽象计算模型和语言识别机制。本文档从数学形式化和Haskell实现的角度，全面阐述自动机理论的基础概念、性质和算法。

## 🎯 核心目标

- 建立自动机理论的数学基础
- 形式化自动机的定义和性质
- 展示Haskell中的自动机实现
- 分析自动机的计算能力和复杂度

## 📖 目录

1. [数学基础](#1-数学基础)
2. [有限自动机](#2-有限自动机)
3. [下推自动机](#3-下推自动机)
4. [图灵机](#4-图灵机)
5. [自动机等价性](#5-自动机等价性)
6. [实际应用](#6-实际应用)

---

## 1. 数学基础

### 1.1 基本定义

**定义 1.1** (字母表)
字母表是一个有限集合 $\Sigma$，其元素称为符号。

**定义 1.2** (字符串)
字符串是字母表 $\Sigma$ 上符号的有限序列，记作 $w \in \Sigma^*$。

**定义 1.3** (语言)
语言是字母表 $\Sigma$ 上字符串的集合，即 $L \subseteq \Sigma^*$。

### 1.2 字符串操作

**定义 1.4** (字符串连接)
对于字符串 $u, v \in \Sigma^*$，连接操作定义为：
$u \cdot v = uv$，其中 $|uv| = |u| + |v|$

**定义 1.5** (字符串幂)
字符串 $w$ 的 $n$ 次幂定义为：
$w^0 = \epsilon$（空字符串）
$w^n = w \cdot w^{n-1}$（对于 $n > 0$）

### 1.3 语言操作

**定义 1.6** (语言连接)
对于语言 $L_1, L_2 \subseteq \Sigma^*$，连接定义为：
$L_1 \cdot L_2 = \{uv \mid u \in L_1, v \in L_2\}$

**定义 1.7** (语言闭包)
语言 $L$ 的Kleene闭包定义为：
$L^* = \bigcup_{n=0}^{\infty} L^n$

```haskell
-- 字符串和语言在Haskell中的表示
type Alphabet = Set Char
type String = [Char]
type Language = Set String

-- 字符串连接
concatenate :: String -> String -> String
concatenate = (++)

-- 字符串幂
stringPower :: String -> Int -> String
stringPower _ 0 = ""
stringPower s n = s ++ stringPower s (n-1)

-- 语言连接
languageConcatenate :: Language -> Language -> Language
languageConcatenate l1 l2 = 
    fromList [u ++ v | u <- toList l1, v <- toList l2]

-- 语言闭包
languageClosure :: Language -> Language
languageClosure l = 
    let powers = iterate (\lang -> languageConcatenate lang l) (singleton "")
    in unions $ take 10 powers  -- 有限近似
```

---

## 2. 有限自动机

### 2.1 确定性有限自动机 (DFA)

**定义 2.1** (DFA)
确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.2** (DFA接受语言)
DFA $M$ 接受的语言定义为：
$L(M) = \{w \in \Sigma^* \mid \hat{\delta}(q_0, w) \in F\}$
其中 $\hat{\delta}$ 是转移函数的扩展。

```haskell
-- DFA在Haskell中的表示
data DFA = DFA
    { states :: Set Int
    , alphabet :: Set Char
    , transition :: Int -> Char -> Int
    , initialState :: Int
    , acceptingStates :: Set Int
    }

-- 扩展转移函数
extendedTransition :: DFA -> Int -> String -> Int
extendedTransition dfa q [] = q
extendedTransition dfa q (c:cs) = 
    let nextState = transition dfa q c
    in extendedTransition dfa nextState cs

-- DFA接受判断
accepts :: DFA -> String -> Bool
accepts dfa w = 
    let finalState = extendedTransition dfa (initialState dfa) w
    in finalState `member` acceptingStates dfa

-- 示例：接受偶数个a的DFA
evenA :: DFA
evenA = DFA
    { states = fromList [0, 1]
    , alphabet = fromList ['a', 'b']
    , transition = \q c -> case (q, c) of
        (0, 'a') -> 1
        (1, 'a') -> 0
        (_, 'b') -> q
        (_, _) -> q
    , initialState = 0
    , acceptingStates = fromList [0]
    }
```

### 2.2 非确定性有限自动机 (NFA)

**定义 2.3** (NFA)
非确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \rightarrow 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.4** (NFA接受语言)
NFA $M$ 接受的语言定义为：
$L(M) = \{w \in \Sigma^* \mid \hat{\delta}(q_0, w) \cap F \neq \emptyset\}$

```haskell
-- NFA在Haskell中的表示
data NFA = NFA
    { states :: Set Int
    , alphabet :: Set Char
    , transition :: Int -> Char -> Set Int
    , initialState :: Int
    , acceptingStates :: Set Int
    }

-- 扩展转移函数
extendedTransitionNFA :: NFA -> Set Int -> String -> Set Int
extendedTransitionNFA nfa qs [] = qs
extendedTransitionNFA nfa qs (c:cs) = 
    let nextStates = unions [transition nfa q c | q <- toList qs]
    in extendedTransitionNFA nfa nextStates cs

-- NFA接受判断
acceptsNFA :: NFA -> String -> Bool
acceptsNFA nfa w = 
    let finalStates = extendedTransitionNFA nfa (singleton $ initialState nfa) w
    in not $ null $ intersection finalStates (acceptingStates nfa)

-- 示例：接受包含aa或bb的NFA
containsAAorBB :: NFA
containsAAorBB = NFA
    { states = fromList [0, 1, 2, 3, 4]
    , alphabet = fromList ['a', 'b']
    , transition = \q c -> case (q, c) of
        (0, 'a') -> fromList [0, 1]
        (0, 'b') -> fromList [0, 3]
        (1, 'a') -> fromList [2]
        (1, 'b') -> fromList [0]
        (2, _) -> fromList [2]
        (3, 'a') -> fromList [0]
        (3, 'b') -> fromList [4]
        (4, _) -> fromList [4]
        (_, _) -> empty
    , initialState = 0
    , acceptingStates = fromList [2, 4]
    }
```

### 2.3 DFA与NFA等价性

**定理 2.1** (DFA与NFA等价性)
对于每个NFA $M$，存在一个DFA $M'$ 使得 $L(M) = L(M')$。

**证明**:
使用子集构造法，将NFA的状态集合作为DFA的状态。

```haskell
-- 子集构造法：NFA转DFA
nfaToDFA :: NFA -> DFA
nfaToDFA nfa = DFA
    { states = powerSet (states nfa)
    , alphabet = alphabet nfa
    , transition = \qs c -> 
        unions [transition nfa q c | q <- toList qs]
    , initialState = singleton (initialState nfa)
    , acceptingStates = 
        fromList [qs | qs <- toList (powerSet (states nfa)), 
                      not $ null $ intersection qs (acceptingStates nfa)]
    }

-- 幂集计算
powerSet :: Set a -> Set (Set a)
powerSet s = 
    let elements = toList s
        subsets = subsequences elements
    in fromList $ map fromList subsets
```

---

## 3. 下推自动机

### 3.1 下推自动机定义

**定义 3.1** (PDA)
下推自动机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta: Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^*}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

**定义 3.2** (PDA配置)
PDA的配置是一个三元组 $(q, w, \gamma)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\gamma \in \Gamma^*$ 是栈内容

```haskell
-- PDA在Haskell中的表示
data PDA = PDA
    { states :: Set Int
    , inputAlphabet :: Set Char
    , stackAlphabet :: Set Char
    , transition :: Int -> Maybe Char -> Char -> [(Int, String)]
    , initialState :: Int
    , initialStackSymbol :: Char
    , acceptingStates :: Set Int
    }

-- PDA配置
data PDAConfig = PDAConfig
    { state :: Int
    , input :: String
    , stack :: String
    }

-- PDA转移
pdaTransition :: PDA -> PDAConfig -> [PDAConfig]
pdaTransition pda (PDAConfig q (c:cs) (s:ss)) = 
    let transitions = transition pda q (Just c) s
    in [PDAConfig q' cs (gamma ++ ss) | (q', gamma) <- transitions]
pdaTransition pda (PDAConfig q [] (s:ss)) = 
    let transitions = transition pda q Nothing s
    in [PDAConfig q' [] (gamma ++ ss) | (q', gamma) <- transitions]

-- PDA接受判断
acceptsPDA :: PDA -> String -> Bool
acceptsPDA pda w = 
    let initialConfig = PDAConfig (initialState pda) w [initialStackSymbol pda]
        finalConfigs = reachableConfigs pda [initialConfig]
    in any (\config -> state config `member` acceptingStates pda && 
                      null (input config)) finalConfigs

-- 可达配置计算
reachableConfigs :: PDA -> [PDAConfig] -> [PDAConfig]
reachableConfigs pda configs = 
    let newConfigs = concatMap (pdaTransition pda) configs
        allConfigs = configs ++ newConfigs
    in if null newConfigs 
       then configs 
       else reachableConfigs pda allConfigs
```

### 3.2 上下文无关文法与PDA

**定理 3.1** (CFG与PDA等价性)
语言 $L$ 是上下文无关语言当且仅当存在PDA $M$ 使得 $L = L(M)$。

**证明**:

1. CFG转PDA：使用自顶向下或自底向上解析
2. PDA转CFG：使用配置的语法分析

```haskell
-- 上下文无关文法
data CFG = CFG
    { variables :: Set Char
    , terminals :: Set Char
    , productions :: [(Char, String)]
    , startSymbol :: Char
    }

-- CFG转PDA（自顶向下）
cfgToPDA :: CFG -> PDA
cfgToPDA cfg = PDA
    { states = fromList [0, 1, 2]
    , inputAlphabet = terminals cfg
    , stackAlphabet = variables cfg `union` terminals cfg
    , transition = \q input stack -> case (q, input, stack) of
        (0, Nothing, _) -> [(1, [startSymbol cfg])]
        (1, Nothing, v) | v `member` variables cfg -> 
            [(1, reverse rhs) | (var, rhs) <- productions cfg, var == v]
        (1, Just c, t) | t == c -> [(1, "")]
        (1, Nothing, _) -> [(2, "")]
        (_, _, _) -> []
    , initialState = 0
    , initialStackSymbol = 'Z'
    , acceptingStates = fromList [2]
    }
```

---

## 4. 图灵机

### 4.1 图灵机定义

**定义 4.1** (图灵机)
图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是磁带字母表（$\Sigma \subseteq \Gamma$）
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**定义 4.2** (图灵机配置)
图灵机的配置是一个三元组 $(q, \alpha, \beta)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是读写头左侧的磁带内容
- $\beta \in \Gamma^*$ 是读写头右侧的磁带内容

```haskell
-- 图灵机在Haskell中的表示
data Direction = L | R deriving (Eq, Show)

data TuringMachine = TuringMachine
    { states :: Set Int
    , inputAlphabet :: Set Char
    , tapeAlphabet :: Set Char
    , transition :: Int -> Char -> (Int, Char, Direction)
    , initialState :: Int
    , blankSymbol :: Char
    , acceptingStates :: Set Int
    }

-- 图灵机配置
data TMConfig = TMConfig
    { state :: Int
    , leftTape :: String
    , rightTape :: String
    }

-- 图灵机转移
tmTransition :: TuringMachine -> TMConfig -> TMConfig
tmTransition tm (TMConfig q left right) = 
    let currentSymbol = if null right then blankSymbol tm else head right
        (q', newSymbol, dir) = transition tm q currentSymbol
        newRight = if null right then [newSymbol] else newSymbol : tail right
    in case dir of
        L -> TMConfig q' (init left) (last left : newRight)
        R -> TMConfig q' (left ++ [head newRight]) (tail newRight)

-- 图灵机执行
runTM :: TuringMachine -> String -> Bool
runTM tm input = 
    let initialConfig = TMConfig (initialState tm) [] input
        finalConfig = runUntilHalt tm initialConfig
    in state finalConfig `member` acceptingStates tm

-- 运行直到停机
runUntilHalt :: TuringMachine -> TMConfig -> TMConfig
runUntilHalt tm config = 
    let nextConfig = tmTransition tm config
    in if state nextConfig `member` acceptingStates tm
       then nextConfig
       else runUntilHalt tm nextConfig

-- 示例：接受回文串的图灵机
palindromeTM :: TuringMachine
palindromeTM = TuringMachine
    { states = fromList [0, 1, 2, 3, 4, 5]
    , inputAlphabet = fromList ['a', 'b']
    , tapeAlphabet = fromList ['a', 'b', 'X', 'Y', 'B']
    , transition = \q s -> case (q, s) of
        (0, 'a') -> (1, 'X', R)
        (0, 'b') -> (2, 'Y', R)
        (0, 'B') -> (5, 'B', R)
        (1, 'a') -> (1, 'a', R)
        (1, 'b') -> (1, 'b', R)
        (1, 'B') -> (3, 'B', L)
        (2, 'a') -> (2, 'a', R)
        (2, 'b') -> (2, 'b', R)
        (2, 'B') -> (4, 'B', L)
        (3, 'a') -> (5, 'X', L)
        (3, 'X') -> (5, 'X', L)
        (3, 'Y') -> (5, 'Y', L)
        (4, 'b') -> (5, 'Y', L)
        (4, 'X') -> (5, 'X', L)
        (4, 'Y') -> (5, 'Y', L)
        (_, _) -> (5, s, R)
    , initialState = 0
    , blankSymbol = 'B'
    , acceptingStates = fromList [5]
    }
```

### 4.2 图灵机的计算能力

**定理 4.1** (丘奇-图灵论题)
任何可计算的函数都可以由图灵机计算。

**定理 4.2** (图灵机的通用性)
存在通用图灵机 $U$，对于任意图灵机 $M$ 和输入 $w$，有：
$U(\langle M \rangle, w) = M(w)$

```haskell
-- 通用图灵机的简化实现
data UniversalTM = UniversalTM
    { states :: Set Int
    , transition :: Int -> Char -> (Int, Char, Direction)
    }

-- 图灵机编码
encodeTM :: TuringMachine -> String
encodeTM tm = 
    let stateList = toList (states tm)
        transitionList = [(q, s, r) | q <- stateList, 
                                     s <- toList (tapeAlphabet tm),
                                     let (q', s', d) = transition tm q s,
                                     r <- [q', s', encodeDirection d]]
    in concatMap show transitionList

encodeDirection :: Direction -> Char
encodeDirection L = 'L'
encodeDirection R = 'R'
```

---

## 5. 自动机等价性

### 5.1 自动机等价性定义

**定义 5.1** (自动机等价性)
两个自动机 $M_1$ 和 $M_2$ 等价，当且仅当 $L(M_1) = L(M_2)$。

**定义 5.2** (最小化)
DFA $M$ 是最小的，当且仅当不存在等价的状态数更少的DFA。

### 5.2 DFA最小化算法

**定理 5.1** (DFA最小化)
对于任意DFA $M$，存在唯一的最小DFA $M'$ 使得 $L(M) = L(M')$。

**算法**:

1. 移除不可达状态
2. 合并等价状态
3. 重新标记状态

```haskell
-- DFA最小化
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = 
    let reachableStates = findReachableStates dfa
        equivalentStates = findEquivalentStates dfa reachableStates
        minimizedStates = mapStates dfa equivalentStates
    in minimizedStates

-- 找到可达状态
findReachableStates :: DFA -> Set Int
findReachableStates dfa = 
    let initial = singleton (initialState dfa)
        reachable = iterate (\states -> 
            states `union` unions [singleton (transition dfa q c) 
                                  | q <- toList states, 
                                    c <- toList (alphabet dfa)]) initial
    in reachable !! 10  -- 有限迭代

-- 找到等价状态
findEquivalentStates :: DFA -> Set Int -> [[Int]]
findEquivalentStates dfa states = 
    let initialPartition = [toList states]
        finalPartition = iterate (refinePartition dfa) initialPartition !! 10
    in finalPartition

-- 细化分区
refinePartition :: DFA -> [[Int]] -> [[Int]]
refinePartition dfa partition = 
    concatMap (\group -> 
        let subgroups = groupBy (\q1 q2 -> 
            all (\c -> sameTransition dfa q1 q2 c) (toList $ alphabet dfa)) group
        in subgroups) partition

-- 检查状态转移是否相同
sameTransition :: DFA -> Int -> Int -> Char -> Bool
sameTransition dfa q1 q2 c = 
    let next1 = transition dfa q1 c
        next2 = transition dfa q2 c
    in (next1 `member` acceptingStates dfa) == (next2 `member` acceptingStates dfa)
```

---

## 6. 实际应用

### 6.1 词法分析器

```haskell
-- 词法分析器使用DFA
data Token = Token String String deriving (Show)

lexicalAnalyzer :: DFA -> String -> [Token]
lexicalAnalyzer dfa input = 
    let tokens = scanTokens dfa input
    in map (\t -> Token (fst t) (snd t)) tokens

scanTokens :: DFA -> String -> [(String, String)]
scanTokens _ [] = []
scanTokens dfa input = 
    let (token, rest) = scanToken dfa input
    in (token, "IDENTIFIER") : scanTokens dfa rest

scanToken :: DFA -> String -> (String, String)
scanToken dfa input = 
    let (token, _) = foldl (\(acc, state) c -> 
        let nextState = transition dfa state c
        in if nextState `member` acceptingStates dfa
           then (acc ++ [c], nextState)
           else (acc, state)) ("", initialState dfa) input
    in (token, "TOKEN")
```

### 6.2 正则表达式引擎

```haskell
-- 正则表达式到NFA的转换
data Regex = Empty | Epsilon | Char Char | Concat Regex Regex | 
             Union Regex Regex | Star Regex deriving (Show)

regexToNFA :: Regex -> NFA
regexToNFA Empty = emptyNFA
regexToNFA Epsilon = epsilonNFA
regexToNFA (Char c) = charNFA c
regexToNFA (Concat r1 r2) = concatNFA (regexToNFA r1) (regexToNFA r2)
regexToNFA (Union r1 r2) = unionNFA (regexToNFA r1) (regexToNFA r2)
regexToNFA (Star r) = starNFA (regexToNFA r)

-- 匹配正则表达式
matchRegex :: Regex -> String -> Bool
matchRegex regex input = 
    let nfa = regexToNFA regex
    in acceptsNFA nfa input

-- 示例正则表达式
exampleRegex :: Regex
exampleRegex = Concat (Star (Union (Char 'a') (Char 'b'))) (Char 'c')

-- 测试
testRegex :: IO ()
testRegex = do
    print $ matchRegex exampleRegex "abc"  -- True
    print $ matchRegex exampleRegex "aabbc"  -- True
    print $ matchRegex exampleRegex "ab"  -- False
```

### 6.3 语法分析器

```haskell
-- 使用PDA进行语法分析
data ParseTree = Leaf String | Node String [ParseTree] deriving (Show)

parseWithPDA :: PDA -> String -> Maybe ParseTree
parseWithPDA pda input = 
    if acceptsPDA pda input
    then Just (buildParseTree pda input)
    else Nothing

buildParseTree :: PDA -> String -> ParseTree
buildParseTree pda input = 
    -- 简化的语法树构建
    Node "ROOT" [Leaf input]
```

---

## 🔗 交叉引用

### 相关理论

- [[03-Theory/001-Linear-Type-Theory]] - 线性类型理论与自动机
- [[03-Theory/003-Temporal-Type-Theory]] - 时态类型理论与时间自动机

### 相关实现

- [[haskell/02-Type-System]] - Haskell类型系统
- [[haskell/07-Language-Processing]] - Haskell语言处理

### 相关应用

- [[05-Industry-Domains/001-Compiler-Design]] - 编译器设计中的自动机
- [[05-Industry-Domains/002-Natural-Language-Processing]] - 自然语言处理中的自动机

---

## 📚 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). "Introduction to Automata Theory, Languages, and Computation"
2. Sipser, M. (2012). "Introduction to the Theory of Computation"
3. Kozen, D. C. (2006). "Automata and Computability"

---

**最后更新**: 2024-12-19  
**状态**: ✅ 完成  
**版本**: 1.0
