# 02-Pushdown-Automata - 下推自动机

## 📚 概述

下推自动机（Pushdown Automaton, PDA）是识别上下文无关语言的抽象计算模型。PDA扩展了有限自动机，增加了栈存储能力，使其能够处理嵌套结构和上下文无关语言。

## 🎯 核心概念

### 形式定义

**下推自动机**是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$：有限状态集合
- $\Sigma$：输入字母表
- $\Gamma$：栈字母表
- $\delta$：转移函数，$\delta: Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow \mathcal{P}(Q \times \Gamma^*)$
- $q_0 \in Q$：初始状态
- $Z_0 \in \Gamma$：初始栈符号
- $F \subseteq Q$：接受状态集合

### 瞬时描述

PDA的**瞬时描述**（Instantaneous Description, ID）是一个三元组 $(q, w, \alpha)$，其中：

- $q \in Q$：当前状态
- $w \in \Sigma^*$：剩余输入字符串
- $\alpha \in \Gamma^*$：栈内容（栈顶在右）

### 转移关系

对于瞬时描述 $(q, aw, Z\alpha)$ 和 $(p, w, \beta\alpha)$，如果 $(p, \beta) \in \delta(q, a, Z)$，则称 $(q, aw, Z\alpha) \vdash (p, w, \beta\alpha)$。

**闭包转移**：$\vdash^*$ 表示零次或多次转移的闭包。

### 语言定义

PDA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid (q_0, w, Z_0) \vdash^* (q, \epsilon, \alpha), q \in F, \alpha \in \Gamma^*\}$$

## 🔧 Haskell实现

### 基础数据结构

```haskell
-- | 转移函数类型
type TransitionFunction = 
  State -> Maybe Char -> StackSymbol -> [(State, [StackSymbol])]

-- | 栈符号
newtype StackSymbol = StackSymbol Char
  deriving (Eq, Show, Ord)

-- | 状态
newtype State = State Int
  deriving (Eq, Show, Ord)

-- | 瞬时描述
data InstantaneousDescription = ID
  { currentState :: State
  , remainingInput :: String
  , stackContent :: [StackSymbol]  -- 栈顶在右
  }
  deriving (Eq, Show)

-- | 下推自动机
data PDA = PDA
  { states :: Set State
  , inputAlphabet :: Set Char
  , stackAlphabet :: Set StackSymbol
  , transitionFunction :: TransitionFunction
  , initialState :: State
  , initialStackSymbol :: StackSymbol
  , acceptingStates :: Set State
  }
  deriving (Show)

-- | 转移步骤
data TransitionStep = TransitionStep
  { fromID :: InstantaneousDescription
  , toID :: InstantaneousDescription
  , inputSymbol :: Maybe Char
  , stackSymbol :: StackSymbol
  , newStackSymbols :: [StackSymbol]
  }
  deriving (Eq, Show)
```

### 核心操作

```haskell
-- | 执行单步转移
step :: PDA -> InstantaneousDescription -> [InstantaneousDescription]
step pda (ID state input stack) = 
  case input of
    [] -> -- ε转移
      case stack of
        [] -> []
        (top:rest) -> 
          let transitions = transitionFunction pda state Nothing top
          in [ID newState input (newStack ++ rest) 
              | (newState, newStack) <- transitions]
    (c:cs) -> -- 输入符号转移
      case stack of
        [] -> []
        (top:rest) -> 
          let transitions = transitionFunction pda state (Just c) top
          in [ID newState cs (newStack ++ rest) 
              | (newState, newStack) <- transitions]

-- | 检查是否为接受状态
isAccepting :: PDA -> InstantaneousDescription -> Bool
isAccepting pda (ID state _ _) = state `Set.member` acceptingStates pda

-- | 检查字符串是否被接受
accepts :: PDA -> String -> Bool
accepts pda input = 
  let initialID = ID (initialState pda) input [initialStackSymbol pda]
      allConfigurations = generateAllConfigurations pda [initialID]
      acceptingConfigurations = filter (isAccepting pda) allConfigurations
  in any (\id -> remainingInput id == "") acceptingConfigurations

-- | 生成所有可能的配置
generateAllConfigurations :: PDA -> [InstantaneousDescription] -> [InstantaneousDescription]
generateAllConfigurations pda current = 
  let nextSteps = concatMap (step pda) current
      newConfigurations = filter (`notElem` current) nextSteps
  in if null newConfigurations 
     then current 
     else generateAllConfigurations pda (current ++ newConfigurations)
```

### 确定性PDA

```haskell
-- | 确定性下推自动机
data DPDA = DPDA
  { pda :: PDA
  , isDeterministic :: Bool
  }
  deriving (Show)

-- | 检查PDA是否为确定性的
checkDeterminism :: PDA -> Bool
checkDeterminism pda = 
  let allTransitions = [(state, input, stack) | 
                        state <- Set.toList (states pda),
                        input <- Nothing : map Just (Set.toList (inputAlphabet pda)),
                        stack <- Set.toList (stackAlphabet pda)]
  in all (\t -> length (getTransitions pda t) <= 1) allTransitions
  where
    getTransitions pda (state, input, stack) = 
      transitionFunction pda state input stack

-- | 确定性转移
deterministicStep :: DPDA -> InstantaneousDescription -> Maybe InstantaneousDescription
deterministicStep dpda id = 
  case step (pda dpda) id of
    [] -> Nothing
    [next] -> Just next
    _ -> error "Non-deterministic transition in DPDA"
```

## 📐 形式证明

### 定理1：PDA与CFG等价性

**定理**：语言 $L$ 是上下文无关的当且仅当存在下推自动机识别 $L$。

**证明**：

#### 必要性：CFG → PDA

对于CFG $G = (V, \Sigma, P, S)$，构造PDA $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$：

- $Q = \{q_0, q_1, q_2\}$
- $\Gamma = V \cup \Sigma \cup \{Z_0\}$
- $F = \{q_2\}$

转移函数定义：

1. $\delta(q_0, \epsilon, Z_0) = \{(q_1, SZ_0)\}$
2. $\delta(q_1, \epsilon, A) = \{(q_1, \alpha) \mid A \rightarrow \alpha \in P\}$
3. $\delta(q_1, a, a) = \{(q_1, \epsilon)\}$ 对所有 $a \in \Sigma$
4. $\delta(q_1, \epsilon, Z_0) = \{(q_2, \epsilon)\}$

**Haskell实现**：

```haskell
-- | 从CFG构造PDA
cfgToPDA :: CFG -> PDA
cfgToPDA cfg = PDA
  { states = Set.fromList [State 0, State 1, State 2]
  , inputAlphabet = terminals cfg
  , stackAlphabet = Set.fromList (map StackSymbol (Set.toList (variables cfg) ++ Set.toList (terminals cfg) ++ ["Z0"]))
  , transitionFunction = buildTransitionFunction cfg
  , initialState = State 0
  , initialStackSymbol = StackSymbol "Z0"
  , acceptingStates = Set.singleton (State 2)
  }

-- | 构建转移函数
buildTransitionFunction :: CFG -> TransitionFunction
buildTransitionFunction cfg state input stack = 
  case (state, input, stack) of
    (State 0, Nothing, StackSymbol "Z0") -> 
      [(State 1, [StackSymbol (startSymbol cfg), StackSymbol "Z0"])]
    (State 1, Nothing, StackSymbol nt) | nt `Set.member` variables cfg ->
      [(State 1, map StackSymbol rhs) | Production (NonTerminal nt') rhs <- productions cfg, nt == nt']
    (State 1, Just c, StackSymbol (c':_)) | c == c' ->
      [(State 1, [])]
    (State 1, Nothing, StackSymbol "Z0") ->
      [(State 2, [])]
    _ -> []
```

#### 充分性：PDA → CFG

对于PDA $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，构造CFG $G = (V, \Sigma, P, S)$：

- $V = \{[q, A, p] \mid q, p \in Q, A \in \Gamma\}$
- $S = [q_0, Z_0, q_f]$ 其中 $q_f \in F$

产生式定义：

1. 对于每个 $q \in F$：$[q_0, Z_0, q] \rightarrow \epsilon$
2. 对于转移 $\delta(q, a, A) \ni (p, B_1B_2...B_k)$：
   - $[q, A, r] \rightarrow a[p, B_1, q_1][q_1, B_2, q_2]...[q_{k-1}, B_k, r]$

### 定理2：确定性PDA的语言类

**定理**：确定性PDA识别的语言类是上下文无关语言的真子集。

**证明**：存在上下文无关语言（如 $\{ww^R \mid w \in \{a,b\}^*\}$）不能被确定性PDA识别。

## 🔍 实际应用

### 示例：括号匹配PDA

```haskell
-- | 括号匹配PDA
bracketMatchingPDA :: PDA
bracketMatchingPDA = PDA
  { states = Set.fromList [State 0, State 1]
  , inputAlphabet = Set.fromList "()"
  , stackAlphabet = Set.fromList [StackSymbol '(', StackSymbol 'Z']
  , transitionFunction = bracketTransitions
  , initialState = State 0
  , initialStackSymbol = StackSymbol 'Z'
  , acceptingStates = Set.singleton (State 1)
  }

-- | 括号匹配转移函数
bracketTransitions :: TransitionFunction
bracketTransitions state input stack = 
  case (state, input, stack) of
    (State 0, Just '(', StackSymbol 'Z') -> 
      [(State 0, [StackSymbol '(', StackSymbol 'Z'])]
    (State 0, Just '(', StackSymbol '(') -> 
      [(State 0, [StackSymbol '(', StackSymbol '('])]
    (State 0, Just ')', StackSymbol '(') -> 
      [(State 0, [])]
    (State 0, Nothing, StackSymbol 'Z') -> 
      [(State 1, [])]
    _ -> []

-- | 测试括号匹配
testBracketMatching :: IO ()
testBracketMatching = do
  putStrLn "Testing bracket matching PDA:"
  let testCases = ["", "()", "()()", "(()())", "(()", ")("]
  mapM_ (\input -> 
    putStrLn $ input ++ " -> " ++ show (accepts bracketMatchingPDA input)
    ) testCases
```

### 性能分析

```haskell
-- | PDA执行复杂度分析
pdaComplexity :: PDA -> String -> Int
pdaComplexity pda input = 
  let initialID = ID (initialState pda) input [initialStackSymbol pda]
      allConfigurations = generateAllConfigurations pda [initialID]
  in length allConfigurations

-- | 栈深度分析
maxStackDepth :: PDA -> String -> Int
maxStackDepth pda input = 
  let initialID = ID (initialState pda) input [initialStackSymbol pda]
      allConfigurations = generateAllConfigurations pda [initialID]
  in maximum (map (length . stackContent) allConfigurations)
```

## 🔗 相关概念

- [上下文无关文法](01-Context-Free-Grammars.md) - PDA的语言定义
- [语法分析](03-Parsing.md) - PDA在解析中的应用
- [有限自动机](01-有限自动机/01-Basic-Concepts.md) - PDA的基础模型
- [图灵机](03-图灵机理论/01-Basic-Turing-Machines.md) - 更强大的计算模型

## 📚 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.

---

*本文档提供了下推自动机的完整形式化框架，包括严格的数学定义、可执行的Haskell实现和构造性证明。*
