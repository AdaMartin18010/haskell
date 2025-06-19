# 009. 正则语言理论 (Regular Languages Theory)

## 1. 概述

正则语言是形式语言理论中最基础的语言类，对应乔姆斯基层次结构中的3型语言。正则语言具有有限状态的计算能力，是词法分析、模式匹配和文本处理的理论基础。

**相关文档**:
- [[001-Linear-Type-Theory]] - 线性类型理论
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[011-Turing-Machines]] - 图灵机理论
- [[012-Computability-Theory]] - 可计算性理论

## 2. 数学基础

### 2.1 正则语言定义

**定义 2.1.1** (正则语言)
给定字母表 $\Sigma$，正则语言集合 $\mathcal{R}(\Sigma)$ 是满足以下条件的最小语言类：

1. **基础语言**：
   - $\emptyset \in \mathcal{R}(\Sigma)$ (空语言)
   - $\{\varepsilon\} \in \mathcal{R}(\Sigma)$ (空串语言)
   - $\{a\} \in \mathcal{R}(\Sigma)$ 对所有 $a \in \Sigma$ (单字符语言)

2. **闭包性质**：
   - 如果 $L_1, L_2 \in \mathcal{R}(\Sigma)$，则 $L_1 \cup L_2 \in \mathcal{R}(\Sigma)$ (并运算)
   - 如果 $L_1, L_2 \in \mathcal{R}(\Sigma)$，则 $L_1 \cdot L_2 \in \mathcal{R}(\Sigma)$ (连接运算)
   - 如果 $L \in \mathcal{R}(\Sigma)$，则 $L^* \in \mathcal{R}(\Sigma)$ (克林闭包)

**定理 2.1.1** (正则语言的代数性质)
正则语言在并、连接和克林闭包运算下构成一个 Kleene 代数。

**证明**:
1. **结合律**: $(L_1 \cup L_2) \cup L_3 = L_1 \cup (L_2 \cup L_3)$
2. **分配律**: $L_1 \cdot (L_2 \cup L_3) = L_1 \cdot L_2 \cup L_1 \cdot L_3$
3. **幂等律**: $L \cup L = L$
4. **单位元**: $\{\varepsilon\} \cdot L = L \cdot \{\varepsilon\} = L$

### 2.2 正则表达式

**定义 2.2.1** (正则表达式语法)
给定字母表 $\Sigma$，正则表达式 $E$ 的语法定义为：

$$
\begin{align}
E &::= \emptyset \mid \varepsilon \mid a \mid (E_1 \cup E_2) \mid (E_1 \cdot E_2) \mid E^* \\
a &::= \text{任意 } a \in \Sigma
\end{align}
$$

**定义 2.2.2** (正则表达式语义)
正则表达式 $E$ 的语言 $L(E)$ 递归定义为：

$$
\begin{align}
L(\emptyset) &= \emptyset \\
L(\varepsilon) &= \{\varepsilon\} \\
L(a) &= \{a\} \\
L(E_1 \cup E_2) &= L(E_1) \cup L(E_2) \\
L(E_1 \cdot E_2) &= L(E_1) \cdot L(E_2) \\
L(E^*) &= L(E)^*
\end{align}
$$

**定理 2.2.1** (正则表达式与正则语言等价)
语言 $L$ 是正则语言当且仅当存在正则表达式 $E$ 使得 $L = L(E)$。

**证明**:
- **必要性**: 通过正则语言的归纳定义构造正则表达式
- **充分性**: 通过有限自动机识别正则表达式语言

## 3. 有限自动机理论

### 3.1 确定性有限自动机 (DFA)

**定义 3.1.1** (DFA)
确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\delta: Q \times \Sigma \to Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**定义 3.1.2** (扩展转移函数)
DFA 的扩展转移函数 $\delta^*: Q \times \Sigma^* \to Q$ 递归定义为：

$$
\begin{align}
\delta^*(q, \varepsilon) &= q \\
\delta^*(q, wa) &= \delta(\delta^*(q, w), a)
\end{align}
$$

**定义 3.1.3** (DFA 语言接受)
DFA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \in F\}$$

**定理 3.1.1** (DFA 确定性)
DFA 在任意输入上的行为是确定性的。

**证明**: 由于转移函数 $\delta: Q \times \Sigma \to Q$ 是单值函数，对于任意状态 $q$ 和输入符号 $a$，存在唯一的下一个状态 $\delta(q, a)$。

### 3.2 非确定性有限自动机 (NFA)

**定义 3.2.1** (NFA)
非确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\delta: Q \times \Sigma \to 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**定义 3.2.2** (NFA 扩展转移函数)
NFA 的扩展转移函数 $\delta^*: Q \times \Sigma^* \to 2^Q$ 递归定义为：

$$
\begin{align}
\delta^*(q, \varepsilon) &= \{q\} \\
\delta^*(q, wa) &= \bigcup_{p \in \delta^*(q, w)} \delta(p, a)
\end{align}
$$

**定理 3.2.1** (NFA 与 DFA 等价)
对于每个 NFA，存在等价的 DFA。

**证明** (子集构造法):
1. DFA 的状态集是 NFA 状态集的幂集 $2^Q$
2. DFA 的转移函数定义为：
   $$\delta'(S, a) = \bigcup_{q \in S} \delta(q, a)$$
3. DFA 的初始状态是 $\{q_0\}$
4. DFA 的接受状态集是 $\{S \subseteq Q \mid S \cap F \neq \emptyset\}$

## 4. Haskell 实现

### 4.1 正则表达式数据类型

```haskell
-- | 正则表达式数据类型
data Regex a where
  Empty     :: Regex a                    -- 空语言 ∅
  Epsilon   :: Regex a                    -- 空串语言 {ε}
  Symbol    :: a -> Regex a               -- 单字符语言 {a}
  Union     :: Regex a -> Regex a -> Regex a  -- 并运算 L₁ ∪ L₂
  Concat    :: Regex a -> Regex a -> Regex a  -- 连接运算 L₁ · L₂
  Star      :: Regex a -> Regex a         -- 克林闭包 L*

-- | 正则表达式的语义函数
semantics :: Eq a => Regex a -> [[a]]
semantics Empty     = []
semantics Epsilon   = [[]]
semantics (Symbol a) = [[a]]
semantics (Union r1 r2) = semantics r1 `union` semantics r2
semantics (Concat r1 r2) = [x ++ y | x <- semantics r1, y <- semantics r2]
semantics (Star r) = star (semantics r)
  where
    star lang = [[]] ++ [concat xs | xs <- sequence (replicate n lang), n <- [1..]]

-- | 辅助函数：列表并集
union :: Eq a => [[a]] -> [[a]] -> [[a]]
union xs ys = xs ++ [y | y <- ys, y `notElem` xs]
```

### 4.2 有限自动机实现

```haskell
-- | 确定性有限自动机
data DFA q a = DFA
  { states     :: Set q           -- 状态集 Q
  , alphabet   :: Set a           -- 字母表 Σ
  , transition :: q -> a -> q     -- 转移函数 δ
  , startState :: q               -- 初始状态 q₀
  , acceptStates :: Set q         -- 接受状态集 F
  }

-- | 非确定性有限自动机
data NFA q a = NFA
  { nfaStates     :: Set q                    -- 状态集 Q
  , nfaAlphabet   :: Set a                    -- 字母表 Σ
  , nfaTransition :: q -> a -> Set q          -- 转移函数 δ
  , nfaStartState :: q                        -- 初始状态 q₀
  , nfaAcceptStates :: Set q                  -- 接受状态集 F
  }

-- | DFA 语言接受函数
acceptsDFA :: (Ord q, Ord a) => DFA q a -> [a] -> Bool
acceptsDFA dfa input = finalState `member` acceptStates dfa
  where
    finalState = foldl (transition dfa) (startState dfa) input

-- | NFA 语言接受函数
acceptsNFA :: (Ord q, Ord a) => NFA q a -> [a] -> Bool
acceptsNFA nfa input = not (null (finalStates `intersection` nfaAcceptStates nfa))
  where
    finalStates = foldl step (singleton (nfaStartState nfa)) input
    step states symbol = unions [nfaTransition nfa q symbol | q <- toList states]

-- | NFA 到 DFA 的转换 (子集构造法)
nfaToDFA :: (Ord q, Ord a) => NFA q a -> DFA (Set q) a
nfaToDFA nfa = DFA
  { states = reachableStates
  , alphabet = nfaAlphabet nfa
  , transition = \stateSet symbol -> 
      unions [nfaTransition nfa q symbol | q <- toList stateSet]
  , startState = singleton (nfaStartState nfa)
  , acceptStates = fromList [s | s <- toList reachableStates, 
                                 not (null (s `intersection` nfaAcceptStates nfa))]
  }
  where
    reachableStates = closure (singleton (nfaStartState nfa))
    closure states = let newStates = unions [unions [nfaTransition nfa q a | q <- toList states] 
                                                           | a <- toList (nfaAlphabet nfa)]
                     in if newStates `isSubsetOf` states 
                        then states 
                        else closure (states `union` newStates)
```

### 4.3 正则表达式到自动机的转换

```haskell
-- | 正则表达式到 NFA 的转换 (Thompson 构造法)
regexToNFA :: (Ord q, Num q) => Regex a -> NFA q a
regexToNFA Empty = NFA
  { nfaStates = fromList [0, 1]
  , nfaAlphabet = empty
  , nfaTransition = \_ _ -> empty
  , nfaStartState = 0
  , nfaAcceptStates = empty
  }

regexToNFA Epsilon = NFA
  { nfaStates = fromList [0, 1]
  , nfaAlphabet = empty
  , nfaTransition = \_ _ -> empty
  , nfaStartState = 0
  , nfaAcceptStates = singleton 1
  }

regexToNFA (Symbol a) = NFA
  { nfaStates = fromList [0, 1, 2]
  , nfaAlphabet = singleton a
  , nfaTransition = \q s -> case (q, s) of
      (0, s') | s' == a -> singleton 1
      _ -> empty
  , nfaStartState = 0
  , nfaAcceptStates = singleton 2
  }

regexToNFA (Union r1 r2) = NFA
  { nfaStates = states1 `union` states2 `union` fromList [start, end]
  , nfaAlphabet = nfaAlphabet nfa1 `union` nfaAlphabet nfa2
  , nfaTransition = \q s -> 
      if q == start 
      then nfaTransition nfa1 (nfaStartState nfa1) s `union` 
           nfaTransition nfa2 (nfaStartState nfa2) s
      else if q `member` states1
      then nfaTransition nfa1 q s
      else if q `member` states2
      then nfaTransition nfa2 q s
      else empty
  , nfaStartState = start
  , nfaAcceptStates = singleton end
  }
  where
    nfa1 = regexToNFA r1
    nfa2 = regexToNFA r2
    states1 = nfaStates nfa1
    states2 = nfaStates nfa2
    start = maximum (toList states1 `union` toList states2) + 1
    end = start + 1

-- | 正则表达式匹配函数
matches :: (Ord a, Eq a) => Regex a -> [a] -> Bool
matches regex input = acceptsNFA (regexToNFA regex) input
```

## 5. 应用实例

### 5.1 词法分析器

```haskell
-- | 词法单元类型
data Token = 
    TNumber Int
  | TPlus
  | TMinus
  | TTimes
  | TDivide
  | TLParen
  | TRParen
  | TEOF
  deriving (Show, Eq)

-- | 词法分析器状态
data LexerState = LexerState
  { input :: String
  , position :: Int
  , tokens :: [Token]
  }

-- | 数字正则表达式
numberRegex :: Regex Char
numberRegex = Concat (Symbol '0') (Star (Symbol '0'))
  `Union` Concat (Symbol '1') (Star (Symbol '1'))
  `Union` Concat (Symbol '2') (Star (Symbol '2'))
  -- ... 扩展到所有数字

-- | 词法分析函数
lexer :: String -> [Token]
lexer input = tokens (lexerStep (LexerState input 0 []))
  where
    lexerStep state
      | position state >= length (input state) = state { tokens = TEOF : tokens state }
      | otherwise = lexerStep (processToken state)

    processToken state = 
      case matchLongestPrefix state of
        Just (token, len) -> state 
          { position = position state + len
          , tokens = token : tokens state
          }
        Nothing -> error "Invalid token"

    matchLongestPrefix state = 
      let remaining = drop (position state) (input state)
      in findLongestMatch remaining

    findLongestMatch :: String -> Maybe (Token, Int)
    findLongestMatch = undefined -- 实现最长匹配算法
```

### 5.2 模式匹配引擎

```haskell
-- | 模式匹配结果
data MatchResult = MatchResult
  { matched :: String
  , groups :: [String]
  , start :: Int
  , end :: Int
  } deriving (Show)

-- | 模式匹配函数
findMatches :: Regex Char -> String -> [MatchResult]
findMatches regex text = concatMap (findMatchesAt regex text) [0..length text - 1]
  where
    findMatchesAt regex text start = 
      let suffixes = tails (drop start text)
          matches = filter (matches regex) suffixes
      in [MatchResult 
            { matched = match
            , groups = [] -- 简化版本，不处理捕获组
            , start = start
            , end = start + length match
            } | match <- matches]
```

## 6. 理论性质

### 6.1 泵引理

**定理 6.1.1** (正则语言泵引理)
如果 $L$ 是正则语言，则存在常数 $p > 0$，使得对于任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = xyz$ 满足：

1. $|xy| \leq p$
2. $|y| > 0$
3. 对于所有 $i \geq 0$，$xy^iz \in L$

**证明**: 设 $M$ 是识别 $L$ 的 DFA，状态数为 $p$。对于长度 $\geq p$ 的字符串，根据鸽巢原理，存在状态重复，可以泵入重复部分。

**应用**: 证明语言非正则性
- $L = \{a^nb^n \mid n \geq 0\}$ 不是正则语言
- $L = \{ww \mid w \in \{a,b\}^*\}$ 不是正则语言

### 6.2 最小化算法

**定义 6.2.1** (状态等价)
DFA 中两个状态 $q_1, q_2$ 等价，当且仅当对于所有输入 $w$，$\delta^*(q_1, w) \in F \iff \delta^*(q_2, w) \in F$。

**算法 6.2.1** (DFA 最小化)
1. 移除不可达状态
2. 合并等价状态
3. 更新转移函数

```haskell
-- | DFA 最小化
minimizeDFA :: (Ord q, Ord a) => DFA q a -> DFA Int a
minimizeDFA dfa = DFA
  { states = fromList [0..length equivalenceClasses - 1]
  , alphabet = alphabet dfa
  , transition = \newState symbol -> 
      let oldState = equivalenceClasses !! newState
          nextOldState = transition dfa oldState symbol
          nextNewState = findIndex (== nextOldState) equivalenceClasses
      in fromJust nextNewState
  , startState = findIndex (== startState dfa) equivalenceClasses
  , acceptStates = fromList [i | (i, q) <- zip [0..] equivalenceClasses, 
                                 q `member` acceptStates dfa]
  }
  where
    equivalenceClasses = computeEquivalenceClasses dfa
    computeEquivalenceClasses = undefined -- 实现等价类计算
```

## 7. 复杂度分析

### 7.1 时间复杂度

- **DFA 识别**: $O(n)$，其中 $n$ 是输入长度
- **NFA 识别**: $O(n \cdot |Q|^2)$，其中 $|Q|$ 是状态数
- **NFA 到 DFA 转换**: $O(2^{|Q|})$
- **正则表达式匹配**: $O(n \cdot |E|)$，其中 $|E|$ 是表达式大小

### 7.2 空间复杂度

- **DFA**: $O(|Q| \cdot |\Sigma|)$
- **NFA**: $O(|Q| \cdot |\Sigma|)$
- **子集构造**: $O(2^{|Q|})$

## 8. 扩展与变体

### 8.1 加权有限自动机

```haskell
-- | 加权有限自动机
data WFA q a w = WFA
  { wfaStates :: Set q
  , wfaAlphabet :: Set a
  , wfaTransition :: q -> a -> q -> w  -- 转移权重
  , wfaStartWeight :: q -> w           -- 初始权重
  , wfaFinalWeight :: q -> w           -- 最终权重
  }

-- | 计算字符串权重
computeWeight :: (Ord q, Ord a, Num w) => WFA q a w -> [a] -> w
computeWeight wfa input = sum [wfaStartWeight wfa q0 * 
                               pathWeight wfa q0 input * 
                               wfaFinalWeight wfa qf | 
                               q0 <- toList (wfaStates wfa),
                               qf <- toList (wfaStates wfa)]
  where
    pathWeight wfa q [] = if q == q then 1 else 0
    pathWeight wfa q (a:as) = sum [wfaTransition wfa q a q' * 
                                   pathWeight wfa q' as | 
                                   q' <- toList (wfaStates wfa)]
```

### 8.2 概率有限自动机

```haskell
-- | 概率有限自动机
data PFA q a = PFA
  { pfaStates :: Set q
  , pfaAlphabet :: Set a
  , pfaTransition :: q -> a -> q -> Double  -- 转移概率
  , pfaStartProb :: q -> Double             -- 初始概率
  , pfaFinalProb :: q -> Double             -- 最终概率
  }

-- | 计算字符串概率
computeProbability :: (Ord q, Ord a) => PFA q a -> [a] -> Double
computeProbability pfa input = sum [pfaStartProb pfa q0 * 
                                    pathProbability pfa q0 input * 
                                    pfaFinalProb pfa qf | 
                                    q0 <- toList (pfaStates pfa),
                                    qf <- toList (pfaStates pfa)]
  where
    pathProbability pfa q [] = if q == q then 1.0 else 0.0
    pathProbability pfa q (a:as) = sum [pfaTransition pfa q a q' * 
                                        pathProbability pfa q' as | 
                                        q' <- toList (pfaStates pfa)]
```

## 9. 总结

正则语言理论为形式语言提供了最基础的计算模型，具有以下特点：

1. **有限状态性**: 计算能力受限于有限状态
2. **线性时间识别**: DFA 可以在线性时间内识别语言
3. **代数性质**: 在并、连接、克林闭包运算下封闭
4. **泵引理**: 提供了证明语言非正则性的有力工具
5. **最小化**: 可以构造最小等价 DFA

正则语言在词法分析、模式匹配、文本处理等领域有广泛应用，是形式语言理论的重要基础。

**相关文档**:
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[011-Turing-Machines]] - 图灵机理论
- [[012-Computability-Theory]] - 可计算性理论 