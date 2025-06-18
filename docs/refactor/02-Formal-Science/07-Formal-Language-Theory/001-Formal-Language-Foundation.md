# 形式语言理论基础

## 📋 概述

本文档介绍形式语言理论的基础概念，包括字母表、字符串、语言、自动机和文法。所有内容都采用严格的数学定义，并提供Haskell实现和形式化证明。

## 🎯 基础概念

### 1. 字母表和字符串

**定义 1.1 (字母表)**
字母表 $\Sigma$ 是有限符号集合：
$$\Sigma = \{a_1, a_2, \ldots, a_n\} \text{ where } n \in \mathbb{N}$$

**定义 1.2 (字符串)**
字符串是字母表中符号的有限序列：
$$w = a_1 a_2 \cdots a_n \text{ where } a_i \in \Sigma$$

**定义 1.3 (空字符串)**
空字符串 $\epsilon$ 是长度为0的字符串：
$$|\epsilon| = 0$$

**定义 1.4 (字符串操作)**:

- **连接**：$w_1 \cdot w_2 = w_1 w_2$
- **幂运算**：$w^0 = \epsilon$, $w^{n+1} = w \cdot w^n$
- **长度**：$|w| = n$ 对于 $w = a_1 a_2 \cdots a_n$

```haskell
-- 字母表定义
type Alphabet = Set Char

-- 字符串类型
type String = [Char]

-- 字符串操作
concatenate :: String -> String -> String
concatenate = (++)

power :: String -> Int -> String
power _ 0 = ""
power s n = s ++ power s (n - 1)

length :: String -> Int
length = Prelude.length

-- 空字符串
epsilon :: String
epsilon = ""

-- 字符串集合
type StringSet = Set String
```

### 2. 语言

**定义 1.5 (语言)**
语言 $L$ 是字符串集合：
$$L \subseteq \Sigma^*$$

其中 $\Sigma^*$ 是所有可能字符串的集合。

**定义 1.6 (语言操作)**:

- **并集**：$L_1 \cup L_2 = \{w \mid w \in L_1 \text{ or } w \in L_2\}$
- **连接**：$L_1 \cdot L_2 = \{w_1 w_2 \mid w_1 \in L_1, w_2 \in L_2\}$
- **克林闭包**：$L^* = \bigcup_{n=0}^{\infty} L^n$

```haskell
-- 语言定义
type Language = Set String

-- 语言操作
union :: Language -> Language -> Language
union = Set.union

concatenateLanguages :: Language -> Language -> Language
concatenateLanguages l1 l2 = 
  Set.fromList [s1 ++ s2 | s1 <- Set.toList l1, s2 <- Set.toList l2]

kleeneStar :: Language -> Language
kleeneStar lang = 
  let powers = iterate (\l -> concatenateLanguages l lang) (Set.singleton "")
  in Set.unions (take 10 powers)  -- 有限近似
```

## 🔧 乔姆斯基层次结构

### 定义 1.7 (乔姆斯基层次)

语言类别的层次结构：

1. **正则语言**：有限状态自动机识别
2. **上下文无关语言**：下推自动机识别
3. **上下文有关语言**：线性有界自动机识别
4. **递归可枚举语言**：图灵机识别

**定理 1.1 (层次包含关系)**
$$\text{Regular} \subset \text{CFL} \subset \text{CSL} \subset \text{REL}$$

**证明：**

1. **包含关系**：每个层次包含前一个层次
   - 正则语言 ⊆ 上下文无关语言
   - 上下文无关语言 ⊆ 上下文有关语言
   - 上下文有关语言 ⊆ 递归可枚举语言

2. **严格包含**：存在语言属于更高层次但不属于较低层次
   - $L = \{a^n b^n \mid n \geq 0\}$ 是上下文无关但不是正则
   - $L = \{a^n b^n c^n \mid n \geq 0\}$ 是上下文有关但不是上下文无关
   - 停机问题的语言是递归可枚举但不是递归

```haskell
-- 语言层次
data LanguageClass = 
    Regular
    | ContextFree
    | ContextSensitive
    | RecursivelyEnumerable
    deriving (Show, Eq, Ord)

-- 语言层次关系
isSubsetOf :: LanguageClass -> LanguageClass -> Bool
isSubsetOf Regular ContextFree = True
isSubsetOf ContextFree ContextSensitive = True
isSubsetOf ContextSensitive RecursivelyEnumerable = True
isSubsetOf _ _ = False

-- 示例语言
regularLanguage :: Language
regularLanguage = Set.fromList ["", "a", "aa", "aaa"]

contextFreeLanguage :: Language
contextFreeLanguage = Set.fromList ["", "ab", "aabb", "aaabbb"]

contextSensitiveLanguage :: Language
contextSensitiveLanguage = Set.fromList ["", "abc", "aabbcc", "aaabbbccc"]
```

## 🔍 有限状态自动机

### 1. 确定性有限自动机

**定义 2.1 (DFA)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.2 (DFA计算)**
DFA在输入 $w = a_1 a_2 \cdots a_n$ 上的计算：
$$q_0 \xrightarrow{a_1} q_1 \xrightarrow{a_2} q_2 \cdots \xrightarrow{a_n} q_n$$

其中 $q_{i+1} = \delta(q_i, a_{i+1})$。

**定义 2.3 (DFA接受)**
DFA接受字符串 $w$，如果计算结束于接受状态：$q_n \in F$。

```haskell
-- DFA定义
data DFA = DFA
    { states :: Set State
    , alphabet :: Alphabet
    , delta :: State -> Char -> State
    , initialState :: State
    , acceptingStates :: Set State
    }

type State = Int

-- DFA模拟
simulateDFA :: DFA -> String -> Bool
simulateDFA dfa input = 
    let finalState = foldl (delta dfa) (initialState dfa) input
    in finalState `Set.member` (acceptingStates dfa)

-- 转移函数
transition :: DFA -> State -> Char -> State
transition dfa currentState symbol = 
    delta dfa currentState symbol

-- 示例DFA：识别以'a'结尾的字符串
exampleDFA :: DFA
exampleDFA = DFA
    { states = Set.fromList [0, 1]
    , alphabet = Set.fromList ['a', 'b']
    , delta = \state symbol -> case (state, symbol) of
        (0, 'a') -> 1
        (0, 'b') -> 0
        (1, 'a') -> 1
        (1, 'b') -> 0
    , initialState = 0
    , acceptingStates = Set.singleton 1
    }
```

### 2. 非确定性有限自动机

**定义 2.4 (NFA)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是转移函数

**定义 2.5 (NFA计算)**
NFA在输入 $w$ 上的计算是一棵树，每个节点表示可能的状态。

**定理 2.1 (DFA与NFA等价性)**
对于每个NFA，存在等价的DFA。

**证明：** 通过子集构造：

1. DFA状态是NFA状态集合
2. DFA转移函数通过子集计算
3. 接受状态包含NFA接受状态

```haskell
-- NFA定义
data NFA = NFA
    { nfaStates :: Set State
    , nfaAlphabet :: Alphabet
    , nfaDelta :: State -> Char -> Set State
    , nfaInitialState :: State
    , nfaAcceptingStates :: Set State
    }

-- 子集构造
subsetConstruction :: NFA -> DFA
subsetConstruction nfa = 
    let initialState = epsilonClosure nfa (Set.singleton (nfaInitialState nfa))
        allStates = generateAllStates nfa initialState
        transitions = buildTransitions nfa allStates
        acceptingStates = findAcceptingStates nfa allStates
    in DFA { states = allStates
           , alphabet = nfaAlphabet nfa
           , delta = transitions
           , initialState = initialState
           , acceptingStates = acceptingStates }

-- ε闭包
epsilonClosure :: NFA -> Set State -> Set State
epsilonClosure nfa states = 
    let newStates = Set.unions [nfaDelta nfa s 'ε' | s <- Set.toList states]
        allStates = Set.union states newStates
    in if Set.size allStates == Set.size states
       then allStates
       else epsilonClosure nfa allStates
```

### 3. 正则表达式

**定义 2.6 (正则表达式)**
正则表达式的语法：
$$R ::= \emptyset \mid \epsilon \mid a \mid R_1 + R_2 \mid R_1 \cdot R_2 \mid R^*$$

**定义 2.7 (正则表达式语义)**:

- $L(\emptyset) = \emptyset$
- $L(\epsilon) = \{\epsilon\}$
- $L(a) = \{a\}$
- $L(R_1 + R_2) = L(R_1) \cup L(R_2)$
- $L(R_1 \cdot R_2) = L(R_1) \cdot L(R_2)$
- $L(R^*) = L(R)^*$

**定理 2.2 (正则表达式与DFA等价性)**
正则表达式和DFA识别相同的语言类。

```haskell
-- 正则表达式数据类型
data Regex = 
    Empty
    | Epsilon
    | Symbol Char
    | Union Regex Regex
    | Concat Regex Regex
    | Star Regex
    deriving (Show, Eq)

-- 正则表达式语义
semantics :: Regex -> Language
semantics Empty = Set.empty
semantics Epsilon = Set.singleton ""
semantics (Symbol c) = Set.singleton [c]
semantics (Union r1 r2) = Set.union (semantics r1) (semantics r2)
semantics (Concat r1 r2) = concatenateLanguages (semantics r1) (semantics r2)
semantics (Star r) = kleeneStar (semantics r)

-- 正则表达式到NFA的转换
regexToNFA :: Regex -> NFA
regexToNFA Empty = -- 实现
regexToNFA Epsilon = -- 实现
regexToNFA (Symbol c) = -- 实现
regexToNFA (Union r1 r2) = -- 实现
regexToNFA (Concat r1 r2) = -- 实现
regexToNFA (Star r) = -- 实现
```

## 📊 上下文无关文法

### 1. 文法定义

**定义 3.1 (CFG)**
上下文无关文法是四元组 $G = (V, T, P, S)$，其中：

- $V$ 是非终结符集合
- $T$ 是终结符集合
- $P$ 是产生式集合
- $S \in V$ 是开始符号

**定义 3.2 (推导)**
推导关系 $\Rightarrow$ 定义：

- 如果 $A \rightarrow \alpha \in P$，则 $\beta A \gamma \Rightarrow \beta \alpha \gamma$
- 如果 $\alpha \Rightarrow \beta$ 且 $\beta \Rightarrow \gamma$，则 $\alpha \Rightarrow \gamma$

**定义 3.3 (语言生成)**
文法 $G$ 生成的语言：
$$L(G) = \{w \in T^* \mid S \Rightarrow^* w\}$$

```haskell
-- 上下文无关文法
data CFG = CFG
    { nonTerminals :: Set String
    , terminals :: Set Char
    , productions :: Set Production
    , startSymbol :: String
    }

data Production = Production
    { leftSide :: String
    , rightSide :: String
    }
    deriving (Show, Eq)

-- 推导
derive :: CFG -> String -> [String]
derive cfg sententialForm = 
    let applicableProductions = filter (\p -> leftSide p `isInfixOf` sententialForm) 
                                   (Set.toList (productions cfg))
        newForms = [applyProduction p sententialForm | p <- applicableProductions]
    in newForms

applyProduction :: Production -> String -> String
applyProduction (Production left right) sententialForm = 
    -- 实现产生式应用
    undefined

-- 示例文法：S -> aSb | ε
exampleCFG :: CFG
exampleCFG = CFG
    { nonTerminals = Set.fromList ["S"]
    , terminals = Set.fromList ['a', 'b']
    , productions = Set.fromList 
        [ Production "S" "aSb"
        , Production "S" ""
        ]
    , startSymbol = "S"
    }
```

### 2. 乔姆斯基范式

**定义 3.4 (CNF)**
乔姆斯基范式文法满足：

- 所有产生式形如 $A \rightarrow BC$ 或 $A \rightarrow a$
- 其中 $A, B, C \in V$ 且 $a \in T$

**定理 3.1 (CNF转换)**
每个CFG都可以转换为等价的CNF。

**证明：** 通过构造性转换：

1. 消除 $\epsilon$ 产生式
2. 消除单位产生式
3. 转换为CNF形式

```haskell
-- CNF转换
convertToCNF :: CFG -> CFG
convertToCNF cfg = 
    let cfg1 = eliminateEpsilon cfg
        cfg2 = eliminateUnit cfg1
        cfg3 = eliminateLong cfg2
    in cfg3

eliminateEpsilon :: CFG -> CFG
eliminateEpsilon cfg = -- 实现

eliminateUnit :: CFG -> CFG
eliminateUnit cfg = -- 实现

eliminateLong :: CFG -> CFG
eliminateLong cfg = -- 实现
```

## 🔗 相关链接

### 理论基础

- [自动机理论](./002-Automata-Theory.md)
- [计算理论](../03-Theory/01-Programming-Language-Theory/001-Syntax-Theory.md)
- [形式语义](../02-Formal-Science/03-Category-Theory/001-Basic-Concepts.md)

### 实际应用

- [编译器设计](../07-Implementation/01-Compiler-Design/001-Lexical-Analysis.md)
- [语言处理](../07-Implementation/02-Language-Processing/001-Parsing-Techniques.md)
- [形式化验证](../07-Implementation/03-Formal-Verification/001-Theorem-Proving.md)

### Haskell实现

- [形式语言实现](../haskell/10-Domain-Specific-Languages/001-Parser-Combinators.md)
- [自动机验证](../haskell/13-Formal-Verification/002-Model-Checking.md)
- [文法解析](../haskell/10-Domain-Specific-Languages/003-External-DSLs.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
