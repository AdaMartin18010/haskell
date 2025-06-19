# 自动机理论深化 (Automata Theory Deepening)

## 📚 目录

- [自动机理论深化 (Automata Theory Deepening)](#自动机理论深化-automata-theory-deepening)
  - [📚 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔬 理论基础](#-理论基础)
    - [1.1 有限自动机](#11-有限自动机)
    - [1.2 下推自动机](#12-下推自动机)
    - [1.3 图灵机](#13-图灵机)
    - [1.4 线性有界自动机](#14-线性有界自动机)
  - [⚙️ Haskell实现](#️-haskell实现)
    - [2.1 有限自动机实现](#21-有限自动机实现)
    - [2.2 下推自动机实现](#22-下推自动机实现)
    - [2.3 图灵机实现](#23-图灵机实现)
  - [🔍 理论证明](#-理论证明)
    - [3.1 自动机等价性](#31-自动机等价性)
    - [3.2 语言识别能力](#32-语言识别能力)
    - [3.3 计算复杂性](#33-计算复杂性)
  - [🌐 应用领域](#-应用领域)
    - [4.1 词法分析](#41-词法分析)
    - [4.2 语法分析](#42-语法分析)
    - [4.3 模式匹配](#43-模式匹配)
  - [🔗 相关理论](#-相关理论)
  - [📖 参考文献](#-参考文献)

## 🎯 概述

自动机理论是形式语言理论的核心，为语言识别和计算模型提供严格的数学基础。本文档深入探讨各种自动机模型，包括有限自动机、下推自动机、图灵机等，并提供完整的Haskell实现。

## 🔬 理论基础

### 1.1 有限自动机

**定义 1.1.1 (确定性有限自动机)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\delta : Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 1.1.2 (非确定性有限自动机)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 1.1.3 (ε-非确定性有限自动机)**
ε-非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\delta : Q \times (\Sigma \cup \{\varepsilon\}) \rightarrow 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定理 1.1.1 (DFA与NFA等价性)**
对于任意NFA $M$，存在等价的DFA $M'$ 使得 $L(M) = L(M')$。

**证明：** 通过子集构造法：

1. **状态构造**：DFA的状态是NFA状态的子集
2. **转移构造**：DFA的转移通过NFA转移计算
3. **接受状态**：包含NFA接受状态的子集是DFA接受状态

### 1.2 下推自动机

**定义 1.2.1 (下推自动机)**
下推自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限栈字母表
- $\delta : Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^*}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

**定义 1.2.2 (PDA配置)**
PDA的配置是三元组 $(q, w, \gamma)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\gamma \in \Gamma^*$ 是栈内容

**定义 1.2.3 (PDA转移关系)**
配置间的转移关系 $\vdash$ 定义为：
$$(q, aw, Z\gamma) \vdash (p, w, \alpha\gamma)$$
当且仅当 $(p, \alpha) \in \delta(q, a, Z)$

### 1.3 图灵机

**定义 1.3.1 (图灵机)**
图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限带字母表，$\Sigma \subseteq \Gamma$
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma - \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**定义 1.3.2 (图灵机配置)**
图灵机的配置是三元组 $(q, \alpha, \beta)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是读写头左侧的带内容
- $\beta \in \Gamma^*$ 是读写头右侧的带内容

**定义 1.3.3 (图灵机转移关系)**
配置间的转移关系 $\vdash$ 定义为：
$$(q, \alpha, a\beta) \vdash (p, \alpha b, \beta)$$
当且仅当 $\delta(q, a) = (p, b, R)$

### 1.4 线性有界自动机

**定义 1.4.1 (线性有界自动机)**
线性有界自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限带字母表，$\Sigma \subseteq \Gamma$
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma - \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**限制条件**：读写头不能移出输入字符串的边界。

## ⚙️ Haskell实现

### 2.1 有限自动机实现

```haskell
-- 状态类型
type State = Int

-- 字母表类型
type Alphabet = Set Char

-- 转移函数类型
type Transition = Map (State, Char) State
type NFATransition = Map (State, Char) (Set State)

-- 确定性有限自动机
data DFA = DFA
  { states :: Set State
  , alphabet :: Alphabet
  , transition :: Transition
  , initialState :: State
  , acceptingStates :: Set State
  }

-- 非确定性有限自动机
data NFA = NFA
  { nfaStates :: Set State
  , nfaAlphabet :: Alphabet
  , nfaTransition :: NFATransition
  , nfaInitialState :: State
  , nfaAcceptingStates :: Set State
  }

-- DFA执行
runDFA :: DFA -> String -> Bool
runDFA dfa input = 
  let finalState = foldl step (initialState dfa) input
  in Set.member finalState (acceptingStates dfa)
  where
    step :: State -> Char -> State
    step state symbol = 
      case Map.lookup (state, symbol) (transition dfa) of
        Just nextState -> nextState
        Nothing -> error "Invalid transition"

-- NFA执行
runNFA :: NFA -> String -> Bool
runNFA nfa input = 
  let finalStates = foldl step (Set.singleton (nfaInitialState nfa)) input
  in not (Set.null (Set.intersection finalStates (nfaAcceptingStates nfa)))
  where
    step :: Set State -> Char -> Set State
    step currentStates symbol = 
      Set.unions [getNextStates state symbol | state <- Set.toList currentStates]
    
    getNextStates :: State -> Char -> Set State
    getNextStates state symbol = 
      case Map.lookup (state, symbol) (nfaTransition nfa) of
        Just nextStates -> nextStates
        Nothing -> Set.empty

-- 子集构造法：NFA转DFA
nfaToDFA :: NFA -> DFA
nfaToDFA nfa = 
  let initialState = Set.singleton (nfaInitialState nfa)
      states = generateStates nfa initialState
      transitions = generateTransitions nfa states
      acceptingStates = filter (\state -> 
        not (Set.null (Set.intersection state (nfaAcceptingStates nfa)))) states
  in DFA (Set.fromList states) (nfaAlphabet nfa) transitions initialState (Set.fromList acceptingStates)

-- 生成DFA状态
generateStates :: NFA -> Set State -> [Set State]
generateStates nfa initial = 
  let allStates = Set.fromList (generateStates' [initial])
  in Set.toList allStates
  where
    generateStates' :: [Set State] -> [Set State]
    generateStates' [] = []
    generateStates' (state:rest) = 
      let newStates = [nextState | symbol <- Set.toList (nfaAlphabet nfa),
                                  let nextState = step state symbol,
                                  not (Set.member nextState (Set.fromList (state:rest)))]
      in state : generateStates' (rest ++ newStates)
    
    step :: Set State -> Char -> Set State
    step states symbol = 
      Set.unions [getNextStates state symbol | state <- Set.toList states]
    
    getNextStates :: State -> Char -> Set State
    getNextStates state symbol = 
      case Map.lookup (state, symbol) (nfaTransition nfa) of
        Just nextStates -> nextStates
        Nothing -> Set.empty

-- 生成DFA转移
generateTransitions :: NFA -> [Set State] -> Transition
generateTransitions nfa states = 
  Map.fromList [(encodeState state, symbol, encodeState nextState) | 
                state <- states,
                symbol <- Set.toList (nfaAlphabet nfa),
                let nextState = step state symbol]
  where
    step :: Set State -> Char -> Set State
    step states symbol = 
      Set.unions [getNextStates state symbol | state <- Set.toList states]
    
    getNextStates :: State -> Char -> Set State
    getNextStates state symbol = 
      case Map.lookup (state, symbol) (nfaTransition nfa) of
        Just nextStates -> nextStates
        Nothing -> Set.empty
    
    encodeState :: Set State -> State
    encodeState = hash . show  -- 简化编码

-- 状态编码
hash :: String -> State
hash = foldl (\acc c -> acc * 31 + fromEnum c) 0
```

### 2.2 下推自动机实现

```haskell
-- 栈操作
data Stack a = Stack [a]
  deriving (Eq, Show)

-- 栈操作函数
push :: a -> Stack a -> Stack a
push x (Stack xs) = Stack (x:xs)

pop :: Stack a -> Maybe (a, Stack a)
pop (Stack []) = Nothing
pop (Stack (x:xs)) = Just (x, Stack xs)

top :: Stack a -> Maybe a
top (Stack []) = Nothing
top (Stack (x:_)) = Just x

isEmpty :: Stack a -> Bool
isEmpty (Stack []) = True
isEmpty _ = False

-- 下推自动机
data PDA = PDA
  { pdaStates :: Set State
  , pdaInputAlphabet :: Alphabet
  , pdaStackAlphabet :: Set Char
  , pdaTransition :: Map (State, Char, Char) [(State, String)]
  , pdaInitialState :: State
  , pdaInitialStackSymbol :: Char
  , pdaAcceptingStates :: Set State
  }

-- PDA配置
data PDAConfig = PDAConfig
  { pdaCurrentState :: State
  , pdaRemainingInput :: String
  , pdaStack :: Stack Char
  }

-- PDA执行
runPDA :: PDA -> String -> Bool
runPDA pda input = 
  let initialConfig = PDAConfig (pdaInitialState pda) input (Stack [pdaInitialStackSymbol pda])
      finalConfigs = executePDA pda [initialConfig]
  in any isAccepting finalConfigs
  where
    isAccepting :: PDAConfig -> Bool
    isAccepting config = 
      pdaRemainingInput config == "" && 
      Set.member (pdaCurrentState config) (pdaAcceptingStates pda)

-- PDA执行步骤
executePDA :: PDA -> [PDAConfig] -> [PDAConfig]
executePDA pda configs = 
  let nextConfigs = concatMap (stepPDA pda) configs
      acceptingConfigs = filter isAccepting nextConfigs
  in if null acceptingConfigs && not (null nextConfigs)
     then executePDA pda nextConfigs
     else nextConfigs
  where
    isAccepting :: PDAConfig -> Bool
    isAccepting config = 
      pdaRemainingInput config == "" && 
      Set.member (pdaCurrentState config) (pdaAcceptingStates pda)

-- PDA单步执行
stepPDA :: PDA -> PDAConfig -> [PDAConfig]
stepPDA pda config = 
  let currentState = pdaCurrentState config
      input = case pdaRemainingInput config of
                (c:cs) -> Just c
                [] -> Nothing
      stackTop = top (pdaStack config)
      transitions = getTransitions pda currentState input stackTop
  in [applyTransition config transition | transition <- transitions]

-- 获取转移
getTransitions :: PDA -> State -> Maybe Char -> Maybe Char -> [(State, String)]
getTransitions pda state input stackTop = 
  case (input, stackTop) of
    (Just c, Just s) -> 
      case Map.lookup (state, c, s) (pdaTransition pda) of
        Just transitions -> transitions
        Nothing -> []
    (Nothing, Just s) -> 
      case Map.lookup (state, 'ε', s) (pdaTransition pda) of
        Just transitions -> transitions
        Nothing -> []
    _ -> []

-- 应用转移
applyTransition :: PDAConfig -> (State, String) -> PDAConfig
applyTransition config (newState, stackPush) = 
  let newStack = foldr push (pdaStack config) stackPush
      newInput = case pdaRemainingInput config of
                   (_:cs) -> cs
                   [] -> []
  in PDAConfig newState newInput newStack
```

### 2.3 图灵机实现

```haskell
-- 图灵机带
data Tape a = Tape [a] a [a]
  deriving (Eq, Show)

-- 带操作
readTape :: Tape a -> a
readTape (Tape _ current _) = current

writeTape :: a -> Tape a -> Tape a
writeTape new (Tape left _ right) = Tape left new right

moveLeft :: Tape a -> Tape a
moveLeft (Tape [] current right) = Tape [] (error "Left boundary") (current:right)
moveLeft (Tape (l:left) current right) = Tape left l (current:right)

moveRight :: Tape a -> Tape a
moveRight (Tape left current []) = Tape (current:left) (error "Right boundary") []
moveRight (Tape left current (r:right)) = Tape (current:left) r right

-- 图灵机
data TuringMachine = TuringMachine
  { tmStates :: Set State
  , tmInputAlphabet :: Alphabet
  , tmTapeAlphabet :: Set Char
  , tmTransition :: Map (State, Char) (State, Char, Direction)
  , tmInitialState :: State
  , tmBlankSymbol :: Char
  , tmAcceptingStates :: Set State
  }

data Direction = L | R
  deriving (Eq, Show)

-- 图灵机配置
data TMConfig = TMConfig
  { tmCurrentState :: State
  , tmTape :: Tape Char
  }

-- 图灵机执行
runTuringMachine :: TuringMachine -> String -> Bool
runTuringMachine tm input = 
  let initialTape = createTape input (tmBlankSymbol tm)
      initialConfig = TMConfig (tmInitialState tm) initialTape
      finalConfig = executeTM tm initialConfig
  in Set.member (tmCurrentState finalConfig) (tmAcceptingStates tm)

-- 创建带
createTape :: String -> Char -> Tape Char
createTape [] blank = Tape [] blank []
createTape (c:cs) blank = Tape [] c (cs ++ [blank])

-- 图灵机执行
executeTM :: TuringMachine -> TMConfig -> TMConfig
executeTM tm config = 
  let currentState = tmCurrentState config
      currentSymbol = readTape (tmTape config)
      transition = getTransition tm currentState currentSymbol
  in case transition of
       Just (newState, newSymbol, direction) -> 
         let newTape = writeTape newSymbol (tmTape config)
             movedTape = case direction of
                           L -> moveLeft newTape
                           R -> moveRight newTape
             newConfig = TMConfig newState movedTape
         in if Set.member newState (tmAcceptingStates tm)
            then newConfig
            else executeTM tm newConfig
       Nothing -> config

-- 获取转移
getTransition :: TuringMachine -> State -> Char -> Maybe (State, Char, Direction)
getTransition tm state symbol = 
  Map.lookup (state, symbol) (tmTransition tm)
```

## 🔍 理论证明

### 3.1 自动机等价性

**定理 3.1.1 (DFA与NFA等价性)**
对于任意NFA $M$，存在等价的DFA $M'$ 使得 $L(M) = L(M')$。

**证明：** 通过子集构造法：

1. **状态构造**：DFA的状态是NFA状态的子集
2. **转移构造**：DFA的转移通过NFA转移计算
3. **接受状态**：包含NFA接受状态的子集是DFA接受状态

**定理 3.1.2 (PDA与CFG等价性)**
对于任意上下文无关文法 $G$，存在等价的下推自动机 $M$ 使得 $L(G) = L(M)$。

**证明：** 通过构造：

1. **自顶向下分析**：从开始符号推导
2. **自底向上分析**：从输入字符串归约
3. **LR分析**：结合自顶向下和自底向上

### 3.2 语言识别能力

**定理 3.2.1 (自动机层次)**
自动机的语言识别能力形成严格层次：
$$\text{DFA} = \text{NFA} \subset \text{PDA} \subset \text{LBA} \subset \text{TM}$$

**证明：** 通过分离语言：

1. **正则语言分离**：$\{a^n b^n \mid n \geq 0\}$ 不能被DFA识别
2. **上下文无关语言分离**：$\{a^n b^n c^n \mid n \geq 0\}$ 不能被PDA识别
3. **上下文相关语言分离**：停机问题不能被LBA识别

### 3.3 计算复杂性

**定理 3.3.1 (自动机复杂度)**
各种自动机的计算复杂度：

- **DFA**：$O(n)$ 时间，$O(1)$ 空间
- **NFA**：$O(n \cdot |Q|)$ 时间，$O(|Q|)$ 空间
- **PDA**：$O(n^3)$ 时间，$O(n^2)$ 空间
- **TM**：不可判定

## 🌐 应用领域

### 4.1 词法分析

自动机在词法分析中的应用：

```haskell
-- 词法分析器
data Token = Identifier String | Number Int | Operator String | Keyword String
  deriving (Eq, Show)

-- 词法分析器状态
data LexerState = Start | InIdentifier | InNumber | InOperator
  deriving (Eq, Show)

-- 词法分析器
lexer :: String -> [Token]
lexer = tokenize Start []
  where
    tokenize :: LexerState -> String -> String -> [Token]
    tokenize Start [] [] = []
    tokenize Start [] (c:cs) = 
      if isAlpha c
      then tokenize InIdentifier [c] cs
      else if isDigit c
      then tokenize InNumber [c] cs
      else if isOperatorChar c
      then tokenize InOperator [c] cs
      else tokenize Start [] cs
    
    tokenize InIdentifier buffer [] = [createToken buffer] ++ tokenize Start [] []
    tokenize InIdentifier buffer (c:cs) = 
      if isAlphaNum c
      then tokenize InIdentifier (buffer ++ [c]) cs
      else createToken buffer : tokenize Start [] (c:cs)
    
    tokenize InNumber buffer [] = [createToken buffer] ++ tokenize Start [] []
    tokenize InNumber buffer (c:cs) = 
      if isDigit c
      then tokenize InNumber (buffer ++ [c]) cs
      else createToken buffer : tokenize Start [] (c:cs)
    
    tokenize InOperator buffer [] = [createToken buffer] ++ tokenize Start [] []
    tokenize InOperator buffer (c:cs) = 
      if isOperatorChar c
      then tokenize InOperator (buffer ++ [c]) cs
      else createToken buffer : tokenize Start [] (c:cs)
    
    createToken :: String -> Token
    createToken s
      | isKeyword s = Keyword s
      | isOperator s = Operator s
      | isNumber s = Number (read s)
      | otherwise = Identifier s

-- 辅助函数
isAlpha :: Char -> Bool
isAlpha c = c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'

isDigit :: Char -> Bool
isDigit c = c >= '0' && c <= '9'

isAlphaNum :: Char -> Bool
isAlphaNum c = isAlpha c || isDigit c

isOperatorChar :: Char -> Bool
isOperatorChar c = elem c "+-*/=<>!&|"

isKeyword :: String -> Bool
isKeyword s = elem s ["if", "then", "else", "while", "do", "let", "in"]

isOperator :: String -> Bool
isOperator s = elem s ["+", "-", "*", "/", "=", "<", ">", "==", "!="]

isNumber :: String -> Bool
isNumber s = all isDigit s
```

### 4.2 语法分析

自动机在语法分析中的应用：

```haskell
-- 语法分析器
data ParseTree = Leaf String | Node String [ParseTree]
  deriving (Eq, Show)

-- LR分析器
data LRParser = LRParser
  { lrAction :: Map (State, String) (Either Int String)
  , lrGoto :: Map (State, String) State
  , lrProductions :: [(String, [String])]
  }

-- LR分析
lrParse :: LRParser -> [String] -> ParseTree
lrParse parser tokens = 
  let initialState = 0
      initialStack = [(initialState, [])]
      finalTree = lrParseStep parser initialStack tokens
  in finalTree

-- LR分析步骤
lrParseStep :: LRParser -> [(State, [ParseTree])] -> [String] -> ParseTree
lrParseStep parser stack [] = 
  case stack of
    [(_, [tree])] -> tree
    _ -> error "Parse error"
lrParseStep parser stack (token:tokens) = 
  let (currentState, trees) = head stack
      action = getAction parser currentState token
  in case action of
       Left nextState -> 
         lrParseStep parser ((nextState, [Leaf token]):stack) tokens
       Right production -> 
         let (lhs, rhs) = getProduction parser production
             newTree = Node lhs (reverse (take (length rhs) trees))
             newStack = drop (length rhs) stack
             (oldState, _) = head newStack
             gotoState = getGoto parser oldState lhs
         in lrParseStep parser ((gotoState, newTree:(snd (head newStack))):tail newStack) (token:tokens)

-- 获取动作
getAction :: LRParser -> State -> String -> Either Int String
getAction parser state token = 
  case Map.lookup (state, token) (lrAction parser) of
    Just action -> action
    Nothing -> error "Invalid action"

-- 获取转移
getGoto :: LRParser -> State -> String -> State
getGoto parser state symbol = 
  case Map.lookup (state, symbol) (lrGoto parser) of
    Just gotoState -> gotoState
    Nothing -> error "Invalid goto"

-- 获取产生式
getProduction :: LRParser -> String -> (String, [String])
getProduction parser index = 
  let i = read index
  in lrProductions parser !! i
```

### 4.3 模式匹配

自动机在模式匹配中的应用：

```haskell
-- 正则表达式
data Regex = Empty | Epsilon | Char Char | Concat Regex Regex | Union Regex Regex | Star Regex
  deriving (Eq, Show)

-- 正则表达式到NFA
regexToNFA :: Regex -> NFA
regexToNFA Empty = createEmptyNFA
regexToNFA Epsilon = createEpsilonNFA
regexToNFA (Char c) = createCharNFA c
regexToNFA (Concat r1 r2) = concatNFA (regexToNFA r1) (regexToNFA r2)
regexToNFA (Union r1 r2) = unionNFA (regexToNFA r1) (regexToNFA r2)
regexToNFA (Star r) = starNFA (regexToNFA r)

-- 创建空NFA
createEmptyNFA :: NFA
createEmptyNFA = NFA (Set.fromList [0, 1]) (Set.fromList []) Map.empty 0 (Set.fromList [1])

-- 创建ε-NFA
createEpsilonNFA :: NFA
createEpsilonNFA = NFA (Set.fromList [0, 1]) (Set.fromList []) Map.empty 0 (Set.fromList [1])

-- 创建字符NFA
createCharNFA :: Char -> NFA
createCharNFA c = 
  let transition = Map.singleton (0, c) (Set.singleton 1)
  in NFA (Set.fromList [0, 1]) (Set.singleton c) transition 0 (Set.fromList [1])

-- 连接NFA
concatNFA :: NFA -> NFA -> NFA
concatNFA nfa1 nfa2 = 
  let states1 = Set.toList (nfaStates nfa1)
      states2 = Set.toList (nfaStates nfa2)
      offset = maximum states1 + 1
      newStates = Set.fromList (states1 ++ map (+offset) states2)
      newAlphabet = Set.union (nfaAlphabet nfa1) (nfaAlphabet nfa2)
      newTransition = Map.union (nfaTransition nfa1) 
                                (Map.fromList [(offset + s, c, Set.map (+offset) nextStates) | 
                                              (s, c, nextStates) <- Map.toList (nfaTransition nfa2)])
      newInitialState = nfaInitialState nfa1
      newAcceptingStates = Set.map (+offset) (nfaAcceptingStates nfa2)
  in NFA newStates newAlphabet newTransition newInitialState newAcceptingStates

-- 并集NFA
unionNFA :: NFA -> NFA -> NFA
unionNFA nfa1 nfa2 = 
  let states1 = Set.toList (nfaStates nfa1)
      states2 = Set.toList (nfaStates nfa2)
      offset = maximum states1 + 1
      newStates = Set.fromList (0:states1 ++ map (+offset) states2)
      newAlphabet = Set.union (nfaAlphabet nfa1) (nfaAlphabet nfa2)
      newTransition = Map.union (nfaTransition nfa1) 
                                (Map.fromList [(offset + s, c, Set.map (+offset) nextStates) | 
                                              (s, c, nextStates) <- Map.toList (nfaTransition nfa2)])
      newInitialState = 0
      newAcceptingStates = Set.union (nfaAcceptingStates nfa1) 
                                     (Set.map (+offset) (nfaAcceptingStates nfa2))
  in NFA newStates newAlphabet newTransition newInitialState newAcceptingStates

-- 星号NFA
starNFA :: NFA -> NFA
starNFA nfa = 
  let states = Set.toList (nfaStates nfa)
      newStates = Set.fromList (0:states)
      newAlphabet = nfaAlphabet nfa
      newTransition = nfaTransition nfa
      newInitialState = 0
      newAcceptingStates = Set.insert 0 (nfaAcceptingStates nfa)
  in NFA newStates newAlphabet newTransition newInitialState newAcceptingStates

-- 正则表达式匹配
matchRegex :: Regex -> String -> Bool
matchRegex regex input = 
  let nfa = regexToNFA regex
  in runNFA nfa input
```

## 🔗 相关理论

- [[02-Formal-Language/001-Formal-Language-Foundations]] - 形式语言基础理论
- [[02-Formal-Language/003-Syntax-Analysis-Theory]] - 语法分析理论
- [[03-Theory/009-Regular-Languages]] - 正则语言理论
- [[03-Theory/010-Context-Free-Grammars]] - 上下文无关文法
- [[03-Theory/011-Turing-Machines]] - 图灵机理论

## 📖 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to automata theory, languages, and computation. Pearson Education.
2. Sipser, M. (2012). Introduction to the theory of computation. Cengage Learning.
3. Kozen, D. C. (2006). Automata and computability. Springer Science & Business Media.
4. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: principles, techniques, and tools. Pearson Education.
5. Lewis, H. R., & Papadimitriou, C. H. (1998). Elements of the theory of computation. Prentice Hall.

---

**最后更新**: 2024年12月19日  
**相关文档**: [[02-Formal-Language/003-Syntax-Analysis-Theory]] - 语法分析理论
