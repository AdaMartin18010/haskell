# 自动机理论基础

## 📋 概述

自动机理论是形式语言理论的基础，研究抽象计算模型和语言识别能力。本文档系统性地介绍从有限自动机到图灵机的完整理论体系，包含严格的数学定义、Haskell实现和形式化证明。

## 🎯 基础概念

### 定义 1.1 (自动机)

自动机是一个抽象的计算模型，由状态、输入、转移函数和输出组成。形式化地，自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

```haskell
-- 自动机基础类型
type State = Int
type Alphabet = Set Char
type Input = String

-- 自动机基类
class Automaton a where
    states :: a -> Set State
    alphabet :: a -> Alphabet
    initialState :: a -> State
    acceptingStates :: a -> Set State
    isAccepting :: a -> State -> Bool
    isAccepting a s = s `Set.member` acceptingStates a
```

## 🔍 有限自动机

### 1. 确定性有限自动机 (DFA)

**定义 1.2 (DFA)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow Q$ 是确定性转移函数

**定义 1.3 (DFA扩展转移函数)**
扩展转移函数 $\delta^* : Q \times \Sigma^* \rightarrow Q$ 定义为：

$$\delta^*(q, \epsilon) = q$$
$$\delta^*(q, wa) = \delta(\delta^*(q, w), a)$$

**定义 1.4 (DFA语言接受)**
DFA $M$ 接受的语言：
$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \in F\}$$

**定理 1.1 (DFA确定性)**
DFA在任意输入上的行为是确定性的。

**证明：** 由于转移函数 $\delta : Q \times \Sigma \rightarrow Q$ 是单值函数，对于任意状态 $q$ 和输入符号 $a$，存在唯一的下一个状态 $\delta(q, a)$。

```haskell
-- DFA实现
data DFA = DFA
    { dfaStates :: Set State
    , dfaAlphabet :: Alphabet
    , dfaDelta :: State -> Char -> State
    , dfaInitialState :: State
    , dfaAcceptingStates :: Set State
    }

instance Automaton DFA where
    states = dfaStates
    alphabet = dfaAlphabet
    initialState = dfaInitialState
    acceptingStates = dfaAcceptingStates

-- DFA扩展转移函数
extendedDelta :: DFA -> State -> Input -> State
extendedDelta dfa q [] = q
extendedDelta dfa q (c:cs) = 
    let nextState = dfaDelta dfa q c
    in extendedDelta dfa nextState cs

-- DFA语言接受
accepts :: DFA -> Input -> Bool
accepts dfa input = 
    let finalState = extendedDelta dfa (dfaInitialState dfa) input
    in finalState `Set.member` dfaAcceptingStates dfa

-- 示例DFA：识别包含偶数个'a'的字符串
evenA_DFA :: DFA
evenA_DFA = DFA
    { dfaStates = Set.fromList [0, 1]
    , dfaAlphabet = Set.fromList ['a', 'b']
    , dfaDelta = \state symbol -> case (state, symbol) of
        (0, 'a') -> 1
        (0, 'b') -> 0
        (1, 'a') -> 0
        (1, 'b') -> 1
    , dfaInitialState = 0
    , dfaAcceptingStates = Set.singleton 0
    }
```

### 2. 非确定性有限自动机 (NFA)

**定义 1.5 (NFA)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是非确定性转移函数

**定义 1.6 (NFA扩展转移函数)**
扩展转移函数 $\delta^* : Q \times \Sigma^* \rightarrow 2^Q$ 定义为：

$$\delta^*(q, \epsilon) = \{q\}$$
$$\delta^*(q, wa) = \bigcup_{p \in \delta^*(q, w)} \delta(p, a)$$

**定义 1.7 (NFA语言接受)**
NFA $M$ 接受的语言：
$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \cap F \neq \emptyset\}$$

**定理 1.2 (NFA与DFA等价性)**
对于每个NFA，存在等价的DFA。

**证明：** 通过子集构造法：

1. DFA状态是NFA状态集合
2. DFA转移函数通过子集计算
3. 接受状态包含NFA接受状态

```haskell
-- NFA实现
data NFA = NFA
    { nfaStates :: Set State
    , nfaAlphabet :: Alphabet
    , nfaDelta :: State -> Char -> Set State
    , nfaInitialState :: State
    , nfaAcceptingStates :: Set State
    }

instance Automaton NFA where
    states = nfaStates
    alphabet = nfaAlphabet
    initialState = nfaInitialState
    acceptingStates = nfaAcceptingStates

-- NFA扩展转移函数
nfaExtendedDelta :: NFA -> State -> Input -> Set State
nfaExtendedDelta nfa q [] = Set.singleton q
nfaExtendedDelta nfa q (c:cs) = 
    let currentStates = nfaExtendedDelta nfa q cs
        nextStates = Set.unions [nfaDelta nfa s c | s <- Set.toList currentStates]
    in nextStates

-- NFA语言接受
nfaAccepts :: NFA -> Input -> Bool
nfaAccepts nfa input = 
    let finalStates = nfaExtendedDelta nfa (nfaInitialState nfa) input
    in not (Set.null (Set.intersection finalStates (nfaAcceptingStates nfa)))

-- 子集构造法
subsetConstruction :: NFA -> DFA
subsetConstruction nfa = 
    let initialState = Set.singleton (nfaInitialState nfa)
        allStates = generateAllStates nfa initialState
        transitions = buildTransitions nfa allStates
        acceptingStates = findAcceptingStates nfa allStates
    in DFA { dfaStates = allStates
           , dfaAlphabet = nfaAlphabet nfa
           , dfaDelta = transitions
           , dfaInitialState = initialState
           , dfaAcceptingStates = acceptingStates }

-- 生成所有状态
generateAllStates :: NFA -> Set (Set State) -> Set (Set State)
generateAllStates nfa startState = 
    let newStates = Set.unions [getReachableStates nfa s | s <- Set.toList startState]
        allStates = Set.union startState newStates
    in if Set.size allStates == Set.size startState
       then allStates
       else generateAllStates nfa allStates

-- 获取可达状态
getReachableStates :: NFA -> Set State -> Set (Set State)
getReachableStates nfa states = 
    Set.fromList [Set.unions [nfaDelta nfa s c | s <- Set.toList states] 
                | c <- Set.toList (nfaAlphabet nfa)]
```

### 3. ε-非确定性有限自动机 (ε-NFA)

**定义 1.8 (ε-NFA)**
ε-NFA是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \rightarrow 2^Q$ 是转移函数

**定义 1.9 (ε-闭包)**
状态 $q$ 的ε-闭包：
$$ECLOSE(q) = \{q\} \cup \bigcup_{p \in \delta(q, \epsilon)} ECLOSE(p)$$

**定理 1.3 (ε-NFA与NFA等价性)**
对于每个ε-NFA，存在等价的NFA。

**证明：** 通过ε-闭包消除：

1. 计算每个状态的ε-闭包
2. 将ε-转移转换为普通转移
3. 调整初始状态和接受状态

```haskell
-- ε-NFA实现
data EpsilonNFA = EpsilonNFA
    { enfaStates :: Set State
    , enfaAlphabet :: Alphabet
    , enfaDelta :: State -> Maybe Char -> Set State
    , enfaInitialState :: State
    , enfaAcceptingStates :: Set State
    }

-- ε-闭包计算
epsilonClosure :: EpsilonNFA -> Set State -> Set State
epsilonClosure enfa states = 
    let epsilonTransitions = Set.unions [enfaDelta enfa s Nothing | s <- Set.toList states]
        newStates = Set.union states epsilonTransitions
    in if Set.size newStates == Set.size states
       then newStates
       else epsilonClosure enfa newStates

-- ε-NFA到NFA的转换
epsilonNFAtoNFA :: EpsilonNFA -> NFA
epsilonNFAtoNFA enfa = 
    let initialClosure = epsilonClosure enfa (Set.singleton (enfaInitialState enfa))
        transitions = buildEpsilonTransitions enfa
        acceptingStates = findEpsilonAcceptingStates enfa
    in NFA { nfaStates = enfaStates enfa
           , nfaAlphabet = enfaAlphabet enfa
           , nfaDelta = transitions
           , nfaInitialState = enfaInitialState enfa
           , nfaAcceptingStates = acceptingStates }
```

## 📊 下推自动机

### 1. 确定性下推自动机 (DPDA)

**定义 2.1 (DPDA)**
确定性下推自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow Q \times \Gamma^*$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

**定义 2.2 (DPDA瞬时描述)**
瞬时描述 $(q, w, \gamma) \vdash (q', w', \gamma')$ 表示从配置 $(q, w, \gamma)$ 一步转移到 $(q', w', \gamma')$。

**定理 2.1 (DPDA语言类)**
DPDA识别的语言类是确定性上下文无关语言(DCFL)。

```haskell
-- DPDA实现
data DPDA = DPDA
    { dpdaStates :: Set State
    , dpdaInputAlphabet :: Alphabet
    , dpdaStackAlphabet :: Set Char
    , dpdaDelta :: State -> Maybe Char -> Char -> (State, String)
    , dpdaInitialState :: State
    , dpdaInitialStack :: Char
    , dpdaAcceptingStates :: Set State
    }

-- DPDA配置
data PDAConfig = PDAConfig
    { pdaState :: State
    , pdaInput :: String
    , pdaStack :: String
    }

-- DPDA转移
pdaTransition :: DPDA -> PDAConfig -> [PDAConfig]
pdaTransition dpda (PDAConfig state (c:input) (s:stack)) = 
    let (newState, newStackTop) = dpdaDelta dpda state (Just c) s
        newStack = newStackTop ++ stack
    in [PDAConfig newState input newStack]

pdaTransition dpda (PDAConfig state input (s:stack)) = 
    let (newState, newStackTop) = dpdaDelta dpda state Nothing s
        newStack = newStackTop ++ stack
    in [PDAConfig newState input newStack]

-- DPDA接受
dpdaAccepts :: DPDA -> String -> Bool
dpdaAccepts dpda input = 
    let initialConfig = PDAConfig (dpdaInitialState dpda) input [dpdaInitialStack dpda]
        finalConfigs = reachableConfigs dpda initialConfig
    in any (\config -> pdaState config `Set.member` dpdaAcceptingStates dpda && null (pdaInput config)) finalConfigs
```

### 2. 非确定性下推自动机 (NPDA)

**定义 2.3 (NPDA)**
非确定性下推自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^*}$ 是转移函数

**定理 2.2 (NPDA语言类)**
NPDA识别的语言类等于上下文无关语言(CFL)。

**定理 2.3 (NPDA与DPDA不等价)**
存在语言被NPDA识别但不被任何DPDA识别。

**证明：** 通过反例：语言 $L = \{ww^R \mid w \in \{a,b\}^*\}$ 被NPDA识别，但不被任何DPDA识别。

```haskell
-- NPDA实现
data NPDA = NPDA
    { npdaStates :: Set State
    , npdaInputAlphabet :: Alphabet
    , npdaStackAlphabet :: Set Char
    , npdaDelta :: State -> Maybe Char -> Char -> Set (State, String)
    , npdaInitialState :: State
    , npdaInitialStack :: Char
    , npdaAcceptingStates :: Set State
    }

-- NPDA转移
npdaTransition :: NPDA -> PDAConfig -> [PDAConfig]
npdaTransition npda (PDAConfig state (c:input) (s:stack)) = 
    let transitions = npdaDelta npda state (Just c) s
    in [(PDAConfig newState input (newStackTop ++ stack)) | (newState, newStackTop) <- Set.toList transitions]

-- NPDA接受
npdaAccepts :: NPDA -> String -> Bool
npdaAccepts npda input = 
    let initialConfig = PDAConfig (npdaInitialState npda) input [npdaInitialStack npda]
        finalConfigs = reachableConfigs npda initialConfig
    in any (\config -> pdaState config `Set.member` npdaAcceptingStates npda && null (pdaInput config)) finalConfigs
```

## 🔧 图灵机

### 1. 标准图灵机

**定义 3.1 (图灵机)**
图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**定义 3.2 (图灵机瞬时描述)**
瞬时描述 $(q, \alpha, i) \vdash (q', \alpha', i')$ 表示从配置 $(q, \alpha, i)$ 一步转移到 $(q', \alpha', i')$。

**定理 3.1 (图灵机计算能力)**
图灵机可以计算任何可计算函数。

**证明：** 通过丘奇-图灵论题：

1. 图灵机模型等价于λ-演算
2. 图灵机模型等价于递归函数
3. 所有已知的计算模型都与图灵机等价

```haskell
-- 图灵机实现
data Direction = L | R deriving (Show, Eq)

data TuringMachine = TuringMachine
    { tmStates :: Set State
    , tmInputAlphabet :: Alphabet
    , tmTapeAlphabet :: Set Char
    , tmDelta :: State -> Char -> (State, Char, Direction)
    , tmInitialState :: State
    , tmBlank :: Char
    , tmAcceptingStates :: Set State
    }

-- 图灵机配置
data TMConfig = TMConfig
    { tmState :: State
    , tmLeftTape :: String  -- 读写头左侧的带内容
    , tmRightTape :: String -- 读写头右侧的带内容
    }

-- 图灵机转移
tmTransition :: TuringMachine -> TMConfig -> TMConfig
tmTransition tm (TMConfig state leftTape (c:rightTape)) = 
    let (newState, newSymbol, direction) = tmDelta tm state c
    in case direction of
        L -> TMConfig newState (init leftTape) (last leftTape : newSymbol : rightTape)
        R -> TMConfig newState (leftTape ++ [newSymbol]) rightTape

-- 图灵机接受
tmAccepts :: TuringMachine -> String -> Bool
tmAccepts tm input = 
    let initialConfig = TMConfig (tmInitialState tm) "" input
        finalConfig = runTM tm initialConfig
    in tmState finalConfig `Set.member` tmAcceptingStates tm

-- 运行图灵机
runTM :: TuringMachine -> TMConfig -> TMConfig
runTM tm config
    | tmState config `Set.member` tmAcceptingStates tm = config
    | otherwise = runTM tm (tmTransition tm config)
```

### 2. 非确定性图灵机

**定义 3.2 (非确定性图灵机)**
非确定性图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $\delta : Q \times \Gamma \rightarrow 2^{Q \times \Gamma \times \{L, R\}}$ 是转移函数

**定理 3.2 (非确定性图灵机与确定性图灵机等价)**
对于每个非确定性图灵机，存在等价的确定性图灵机。

**证明：** 通过模拟构造：

1. 确定性图灵机模拟非确定性图灵机的所有可能计算路径
2. 使用三带图灵机进行模拟
3. 构造保持语言等价性

```haskell
-- 非确定性图灵机
data NDTM = NDTM
    { ndtmStates :: Set State
    , ndtmInputAlphabet :: Alphabet
    , ndtmTapeAlphabet :: Set Char
    , ndtmDelta :: State -> Char -> Set (State, Char, Direction)
    , ndtmInitialState :: State
    , ndtmBlank :: Char
    , ndtmAcceptingStates :: Set State
    }

-- 非确定性图灵机转移
ndtmTransition :: NDTM -> TMConfig -> [TMConfig]
ndtmTransition ndtm (TMConfig state leftTape (c:rightTape)) = 
    let transitions = ndtmDelta ndtm state c
    in [case direction of
           L -> TMConfig newState (init leftTape) (last leftTape : newSymbol : rightTape)
           R -> TMConfig newState (leftTape ++ [newSymbol]) rightTape
        | (newState, newSymbol, direction) <- Set.toList transitions]

-- 非确定性图灵机接受
ndtmAccepts :: NDTM -> String -> Bool
ndtmAccepts ndtm input = 
    let initialConfig = TMConfig (ndtmInitialState ndtm) "" input
        allPaths = explorePaths ndtm initialConfig
    in any (\config -> tmState config `Set.member` ndtmAcceptingStates ndtm) allPaths
```

## 🔗 相关链接

### 理论基础

- [形式语言理论](./001-Formal-Language-Foundation.md)
- [计算理论](../03-Theory/01-Programming-Language-Theory/001-Syntax-Theory.md)
- [复杂性理论](../02-Formal-Science/09-Computational-Complexity/001-Time-Complexity.md)

### 实际应用

- [编译器设计](../07-Implementation/01-Compiler-Design/001-Lexical-Analysis.md)
- [语言处理](../07-Implementation/02-Language-Processing/001-Parsing-Techniques.md)
- [形式化验证](../07-Implementation/03-Formal-Verification/001-Theorem-Proving.md)

### Haskell实现

- [自动机实现](../haskell/10-Domain-Specific-Languages/001-Parser-Combinators.md)
- [图灵机模拟](../haskell/13-Formal-Verification/002-Model-Checking.md)
- [语言识别](../haskell/10-Domain-Specific-Languages/003-External-DSLs.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
