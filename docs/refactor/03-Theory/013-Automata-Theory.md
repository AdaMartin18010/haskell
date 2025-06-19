# 自动机理论 (Automata Theory)

## 📚 概述

自动机理论是形式语言理论的核心组成部分，研究抽象计算模型和形式语言识别机制。本文档建立自动机理论的完整数学基础，并提供 Haskell 实现。

## 🎯 核心概念

### 1. 自动机基础定义

#### 1.1 有限自动机 (Finite Automaton)

**定义 1.1.1** 有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**Haskell 实现**：

```haskell
-- 有限自动机类型定义
data FiniteAutomaton q a = FA
  { states :: Set q
  , alphabet :: Set a
  , transition :: q -> a -> q
  , initialState :: q
  , acceptingStates :: Set q
  }

-- 自动机执行函数
runFA :: (Ord q, Ord a) => FiniteAutomaton q a -> [a] -> Bool
runFA fa input = finalState `member` acceptingStates fa
  where
    finalState = foldl (transition fa) (initialState fa) input

-- 示例：识别偶数个0的自动机
evenZerosFA :: FiniteAutomaton Int Char
evenZerosFA = FA
  { states = fromList [0, 1]
  , alphabet = fromList ['0', '1']
  , transition = \state symbol -> case (state, symbol) of
      (0, '0') -> 1
      (1, '0') -> 0
      (_, '1') -> state
      _ -> state
  , initialState = 0
  , acceptingStates = fromList [0]
  }
```

#### 1.2 确定性有限自动机 (DFA)

**定义 1.2.1** 确定性有限自动机是转移函数为全函数的有限自动机：

$$\delta: Q \times \Sigma \rightarrow Q$$

**定理 1.2.1** DFA 的语言识别能力等价于正则语言。

**证明**：

1. 正则表达式可以构造等价 DFA
2. DFA 可以构造等价正则表达式
3. 通过 Kleene 定理建立等价性

```haskell
-- DFA 类型定义
type DFA q a = FiniteAutomaton q a

-- DFA 最小化算法
minimizeDFA :: (Ord q, Ord a) => DFA q a -> DFA Int a
minimizeDFA dfa = undefined -- 实现 Hopcroft 算法

-- 示例：识别二进制数中1的个数为3的倍数的DFA
mod3DFA :: DFA Int Char
mod3DFA = FA
  { states = fromList [0, 1, 2]
  , alphabet = fromList ['0', '1']
  , transition = \state symbol -> case (state, symbol) of
      (s, '0') -> s
      (s, '1') -> (s + 1) `mod` 3
      _ -> state
  , initialState = 0
  , acceptingStates = fromList [0]
  }
```

#### 1.3 非确定性有限自动机 (NFA)

**定义 1.3.1** 非确定性有限自动机允许转移函数返回状态集：

$$\delta: Q \times \Sigma \rightarrow \mathcal{P}(Q)$$

**定理 1.3.1** NFA 与 DFA 等价。

**证明**：通过子集构造法将 NFA 转换为等价 DFA。

```haskell
-- NFA 类型定义
data NFA q a = NFA
  { nfaStates :: Set q
  , nfaAlphabet :: Set a
  , nfaTransition :: q -> a -> Set q
  , nfaInitialState :: q
  , nfaAcceptingStates :: Set q
  }

-- NFA 到 DFA 的转换
nfaToDFA :: (Ord q, Ord a) => NFA q a -> DFA (Set q) a
nfaToDFA nfa = FA
  { states = reachableStates
  , alphabet = nfaAlphabet nfa
  , transition = \stateSet symbol -> 
      unions [nfaTransition nfa q symbol | q <- toList stateSet]
  , initialState = singleton (nfaInitialState nfa)
  , acceptingStates = S.filter (not . null . intersection (nfaAcceptingStates nfa)) reachableStates
  }
  where
    reachableStates = computeReachableStates nfa

-- 计算可达状态集
computeReachableStates :: (Ord q, Ord a) => NFA q a -> Set (Set q)
computeReachableStates nfa = undefined -- 实现可达性分析
```

### 2. 下推自动机 (Pushdown Automaton)

#### 2.1 下推自动机定义

**定义 2.1.1** 下推自动机是一个七元组 $P = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta: Q \times \Sigma \times \Gamma \rightarrow \mathcal{P}(Q \times \Gamma^*)$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集

```haskell
-- 下推自动机类型定义
data PushdownAutomaton q a g = PDA
  { pdaStates :: Set q
  , pdaInputAlphabet :: Set a
  , pdaStackAlphabet :: Set g
  , pdaTransition :: q -> Maybe a -> g -> Set (q, [g])
  , pdaInitialState :: q
  , pdaInitialStackSymbol :: g
  , pdaAcceptingStates :: Set q
  }

-- PDA 配置
data PDAConfiguration q a g = PDAConfig
  { pdaCurrentState :: q
  , pdaRemainingInput :: [a]
  , pdaStack :: [g]
  }

-- PDA 执行
runPDA :: (Ord q, Ord a, Ord g) => PushdownAutomaton q a g -> [a] -> Bool
runPDA pda input = any isAccepting finalConfigs
  where
    initialConfig = PDAConfig
      { pdaCurrentState = pdaInitialState pda
      , pdaRemainingInput = input
      , pdaStack = [pdaInitialStackSymbol pda]
      }
    finalConfigs = computeAllConfigurations pda initialConfig
    isAccepting config = pdaCurrentState config `member` pdaAcceptingStates pda
                        && null (pdaRemainingInput config)

-- 示例：识别回文串的PDA
palindromePDA :: PushdownAutomaton Int Char Char
palindromePDA = PDA
  { pdaStates = fromList [0, 1, 2]
  , pdaInputAlphabet = fromList ['a', 'b']
  , pdaStackAlphabet = fromList ['A', 'B', 'Z']
  , pdaTransition = \state inputSymbol stackTop -> case (state, inputSymbol, stackTop) of
      -- 读取阶段：将输入压栈
      (0, Just symbol, 'Z') -> fromList [(0, [symbol, 'Z'])]
      (0, Just symbol, _) -> fromList [(0, [symbol, stackTop])]
      -- 中间阶段：切换到匹配模式
      (0, Nothing, _) -> fromList [(1, [stackTop])]
      -- 匹配阶段：比较输入和栈顶
      (1, Just symbol, symbol') | symbol == symbol' -> fromList [(1, [])]
      (1, Nothing, 'Z') -> fromList [(2, ['Z'])]
      _ -> empty
  , pdaInitialState = 0
  , pdaInitialStackSymbol = 'Z'
  , pdaAcceptingStates = fromList [2]
  }
```

### 3. 图灵机 (Turing Machine)

#### 3.1 图灵机定义

**定义 3.1.1** 图灵机是一个七元组 $T = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是输入字母表
- $\Gamma$ 是磁带字母表
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R, N\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集

```haskell
-- 图灵机类型定义
data Direction = L | R | N deriving (Eq, Show)

data TuringMachine q a = TM
  { tmStates :: Set q
  , tmInputAlphabet :: Set a
  , tmTapeAlphabet :: Set a
  , tmTransition :: q -> a -> (q, a, Direction)
  , tmInitialState :: q
  , tmBlankSymbol :: a
  , tmAcceptingStates :: Set q
  }

-- 图灵机配置
data TMConfiguration q a = TMConfig
  { tmCurrentState :: q
  , tmLeftTape :: [a]
  , tmCurrentSymbol :: a
  , tmRightTape :: [a]
  }

-- 图灵机执行
runTM :: (Ord q, Ord a) => TuringMachine q a -> [a] -> Bool
runTM tm input = isAccepting finalConfig
  where
    initialConfig = TMConfig
      { tmCurrentState = tmInitialState tm
      , tmLeftTape = []
      , tmCurrentSymbol = head (input ++ [tmBlankSymbol tm])
      , tmRightTape = tail (input ++ [tmBlankSymbol tm])
      }
    finalConfig = runTMSteps tm initialConfig
    isAccepting config = tmCurrentState config `member` tmAcceptingStates tm

-- 执行图灵机步骤
runTMSteps :: (Ord q, Ord a) => TuringMachine q a -> TMConfiguration q a -> TMConfiguration q a
runTMSteps tm config
  | tmCurrentState config `member` tmAcceptingStates tm = config
  | otherwise = runTMSteps tm (stepTM tm config)

-- 单步执行
stepTM :: (Ord q, Ord a) => TuringMachine q a -> TMConfiguration q a -> TMConfiguration q a
stepTM tm config = TMConfig
  { tmCurrentState = newState
  , tmLeftTape = newLeftTape
  , tmCurrentSymbol = newSymbol
  , tmRightTape = newRightTape
  }
  where
    (newState, newSymbol, direction) = tmTransition tm (tmCurrentState config) (tmCurrentSymbol config)
    (newLeftTape, newRightTape) = case direction of
      L -> (init (tmLeftTape config), newSymbol : tmCurrentSymbol config : tmRightTape config)
      R -> (newSymbol : tmLeftTape config, tail (tmRightTape config ++ [tmBlankSymbol tm]))
      N -> (tmLeftTape config, tmRightTape config)

-- 示例：识别 a^n b^n c^n 的图灵机
anbncnTM :: TuringMachine Int Char
anbncnTM = TM
  { tmStates = fromList [0..6]
  , tmInputAlphabet = fromList ['a', 'b', 'c']
  , tmTapeAlphabet = fromList ['a', 'b', 'c', 'X', 'Y', 'Z', 'B']
  , tmTransition = \state symbol -> case (state, symbol) of
      -- 标记第一个a
      (0, 'a') -> (1, 'X', R)
      -- 跳过b和c，找到最后一个a
      (1, 'a') -> (1, 'a', R)
      (1, 'b') -> (1, 'b', R)
      (1, 'c') -> (1, 'c', R)
      (1, 'B') -> (2, 'B', L)
      -- 标记最后一个a
      (2, 'a') -> (3, 'X', L)
      -- 回到开始
      (3, 'a') -> (3, 'a', L)
      (3, 'b') -> (3, 'b', L)
      (3, 'c') -> (3, 'c', L)
      (3, 'X') -> (0, 'X', R)
      -- 检查是否完成
      (0, 'X') -> (4, 'X', R)
      -- 检查b
      (4, 'b') -> (5, 'Y', R)
      (5, 'b') -> (5, 'b', R)
      (5, 'c') -> (6, 'Z', L)
      (6, 'b') -> (6, 'b', L)
      (6, 'Y') -> (4, 'Y', R)
      -- 检查c
      (4, 'Y') -> (7, 'Y', R)
      (7, 'c') -> (8, 'Z', L)
      (8, 'c') -> (8, 'c', L)
      (8, 'Z') -> (7, 'Z', R)
      -- 接受
      (7, 'B') -> (9, 'B', N)
      _ -> (99, symbol, N) -- 拒绝状态
  , tmInitialState = 0
  , tmBlankSymbol = 'B'
  , tmAcceptingStates = fromList [9]
  }
```

### 4. 自动机等价性

#### 4.1 语言等价性

**定义 4.1.1** 两个自动机 $M_1$ 和 $M_2$ 语言等价，当且仅当 $L(M_1) = L(M_2)$。

**定理 4.1.1** DFA 和 NFA 语言等价。

**定理 4.1.2** PDA 识别上下文无关语言。

**定理 4.1.3** 图灵机识别递归可枚举语言。

```haskell
-- 语言等价性检查
languageEquivalence :: (Ord q1, Ord q2, Ord a) => 
  FiniteAutomaton q1 a -> FiniteAutomaton q2 a -> Bool
languageEquivalence fa1 fa2 = 
  all (\w -> runFA fa1 w == runFA fa2 w) testStrings
  where
    testStrings = generateTestStrings (alphabet fa1) maxLength
    maxLength = 10 -- 有限测试长度

-- 生成测试字符串
generateTestStrings :: Set a -> Int -> [[a]]
generateTestStrings alphabet maxLen = 
  concat [stringsOfLength n | n <- [0..maxLen]]
  where
    stringsOfLength 0 = [[]]
    stringsOfLength n = [c:str | c <- toList alphabet, str <- stringsOfLength (n-1)]
```

### 5. 自动机最小化

#### 5.1 DFA 最小化算法

**算法 5.1.1** Hopcroft 最小化算法：

1. 初始化等价类：接受状态和非接受状态
2. 迭代细化等价类
3. 合并等价状态

```haskell
-- Hopcroft 最小化算法
hopcroftMinimization :: (Ord q, Ord a) => DFA q a -> DFA Int a
hopcroftMinimization dfa = undefined -- 完整实现

-- 等价类计算
computeEquivalenceClasses :: (Ord q, Ord a) => DFA q a -> Set (Set q)
computeEquivalenceClasses dfa = undefined -- 实现等价类计算
```

### 6. 自动机应用

#### 6.1 词法分析器

```haskell
-- 词法分析器类型
data Token = Token { tokenType :: String, tokenValue :: String }

-- 词法分析器自动机
lexerAutomaton :: DFA Int Char
lexerAutomaton = undefined -- 实现词法分析器

-- 词法分析
lexicalAnalysis :: String -> [Token]
lexicalAnalysis input = undefined -- 实现词法分析
```

#### 6.2 模式匹配

```haskell
-- 字符串模式匹配自动机
patternMatchingAutomaton :: String -> DFA Int Char
patternMatchingAutomaton pattern = undefined -- 实现KMP算法

-- 模式匹配
patternMatch :: String -> String -> [Int]
patternMatch pattern text = undefined -- 实现模式匹配
```

## 🔗 交叉引用

### 与类型理论的联系

- **线性类型系统** → 资源管理自动机
- **仿射类型系统** → 所有权自动机
- **时态类型系统** → 时间自动机

### 与形式语义的联系

- **操作语义** → 自动机执行模型
- **指称语义** → 自动机语言语义
- **公理语义** → 自动机验证

### 与形式语言的联系

- **正则语言** → 有限自动机
- **上下文无关语言** → 下推自动机
- **递归可枚举语言** → 图灵机

## 📊 复杂度分析

### 时间复杂度

- **DFA 执行**: $O(n)$
- **NFA 执行**: $O(n \cdot 2^m)$
- **PDA 执行**: $O(n^3)$
- **图灵机执行**: 不可判定

### 空间复杂度

- **DFA**: $O(1)$
- **NFA**: $O(n)$
- **PDA**: $O(n)$
- **图灵机**: 无限制

## 🎯 应用领域

### 1. 编译器设计

- 词法分析器
- 语法分析器
- 代码优化

### 2. 形式验证

- 模型检测
- 程序验证
- 协议验证

### 3. 人工智能

- 自然语言处理
- 模式识别
- 机器学习

## 📚 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Kozen, D. C. (2006). Automata and Computability.

---

**最后更新**: 2024年12月19日  
**相关文档**: [[001-Linear-Type-Theory]], [[002-Affine-Type-Theory]], [[005-Denotational-Semantics]], [[009-Regular-Languages]]
