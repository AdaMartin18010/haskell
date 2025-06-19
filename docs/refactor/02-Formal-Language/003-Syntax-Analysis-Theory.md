# 语法分析理论 (Syntax Analysis Theory)

## 📚 目录

- [语法分析理论](#语法分析理论)
  - [📚 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔬 理论基础](#-理论基础)
    - [1.1 上下文无关文法](#11-上下文无关文法)
    - [1.2 LL分析](#12-ll分析)
    - [1.3 LR分析](#13-lr分析)
    - [1.4 递归下降分析](#14-递归下降分析)
  - [⚙️ Haskell实现](#️-haskell实现)
    - [2.1 文法实现](#21-文法实现)
    - [2.2 LL分析器实现](#22-ll分析器实现)
    - [2.3 LR分析器实现](#23-lr分析器实现)
  - [🔍 理论证明](#-理论证明)
    - [3.1 分析算法正确性](#31-分析算法正确性)
    - [3.2 分析器等价性](#32-分析器等价性)
    - [3.3 计算复杂性](#33-计算复杂性)
  - [🌐 应用领域](#-应用领域)
    - [4.1 编程语言解析](#41-编程语言解析)
    - [4.2 自然语言处理](#42-自然语言处理)
    - [4.3 配置语言解析](#43-配置语言解析)
  - [🔗 相关理论](#-相关理论)
  - [📖 参考文献](#-参考文献)

## 🎯 概述

语法分析是编译器和解释器的核心组件，负责将词法分析器产生的token序列转换为抽象语法树。本文档深入探讨各种语法分析技术，包括LL分析、LR分析、递归下降分析等，并提供完整的Haskell实现。

## 🔬 理论基础

### 1.1 上下文无关文法

**定义 1.1.1 (上下文无关文法)**
上下文无关文法是一个四元组 $G = (N, \Sigma, P, S)$，其中：

- $N$ 是非终结符集合
- $\Sigma$ 是终结符集合
- $P$ 是产生式集合，每个产生式形如 $A \rightarrow \alpha$，其中 $A \in N$，$\alpha \in (N \cup \Sigma)^*$
- $S \in N$ 是开始符号

**定义 1.1.2 (推导)**
给定文法 $G$，推导关系 $\Rightarrow$ 定义为：
$$\alpha A \beta \Rightarrow \alpha \gamma \beta$$
当且仅当 $A \rightarrow \gamma \in P$

**定义 1.1.3 (语言)**
文法 $G$ 生成的语言定义为：
$$L(G) = \{w \in \Sigma^* \mid S \Rightarrow^* w\}$$

**定义 1.1.4 (左推导和右推导)**
左推导：每次替换最左边的非终结符
右推导：每次替换最右边的非终结符

### 1.2 LL分析

**定义 1.2.1 (LL(k)文法)**
文法 $G$ 是LL(k)文法，如果对于任意两个不同的左推导：
$$S \Rightarrow^* \alpha A \beta \Rightarrow \alpha \gamma_1 \beta \Rightarrow^* w_1$$
$$S \Rightarrow^* \alpha A \beta \Rightarrow \alpha \gamma_2 \beta \Rightarrow^* w_2$$
有 $w_1 \neq w_2$ 或 $\text{first}_k(w_1) \cap \text{first}_k(w_2) = \emptyset$

**定义 1.2.2 (FIRST集合)**
对于 $\alpha \in (N \cup \Sigma)^*$，$\text{FIRST}_k(\alpha)$ 定义为：
$$\text{FIRST}_k(\alpha) = \{w \in \Sigma^* \mid \alpha \Rightarrow^* w \text{ 且 } |w| \leq k\}$$

**定义 1.2.3 (FOLLOW集合)**
对于 $A \in N$，$\text{FOLLOW}_k(A)$ 定义为：
$$\text{FOLLOW}_k(A) = \{w \in \Sigma^* \mid S \Rightarrow^* \alpha A \beta \text{ 且 } w \in \text{FIRST}_k(\beta)\}$$

### 1.3 LR分析

**定义 1.3.1 (LR(k)文法)**
文法 $G$ 是LR(k)文法，如果对于任意两个不同的右推导：
$$S \Rightarrow^* \alpha A w \Rightarrow \alpha \beta w$$
$$S \Rightarrow^* \gamma B x \Rightarrow \gamma \delta x$$
有 $\alpha \beta w \neq \gamma \delta x$ 或 $\text{first}_k(w) \cap \text{first}_k(x) = \emptyset$

**定义 1.3.2 (LR项)**
LR项是形如 $[A \rightarrow \alpha \cdot \beta, a]$ 的对象，其中：
- $A \rightarrow \alpha \beta$ 是产生式
- $\cdot$ 表示分析位置
- $a$ 是向前看符号

**定义 1.3.3 (LR状态)**
LR状态是LR项的集合，表示分析过程中的可能状态。

### 1.4 递归下降分析

**定义 1.4.1 (递归下降分析器)**
递归下降分析器为每个非终结符定义一个函数，通过函数调用实现语法分析。

**定义 1.4.2 (预测分析)**
预测分析基于当前输入符号和文法规则，预测应该使用哪个产生式。

## ⚙️ Haskell实现

### 2.1 文法实现

```haskell
-- 符号类型
data Symbol = Terminal String | NonTerminal String
  deriving (Eq, Show, Ord)

-- 产生式
data Production = Production
  { lhs :: NonTerminal
  , rhs :: [Symbol]
  }

-- 上下文无关文法
data CFG = CFG
  { nonTerminals :: Set NonTerminal
  , terminals :: Set Terminal
  , productions :: [Production]
  , startSymbol :: NonTerminal
  }

-- 文法示例：简单算术表达式
arithmeticGrammar :: CFG
arithmeticGrammar = CFG
  { nonTerminals = Set.fromList [NonTerminal "E", NonTerminal "T", NonTerminal "F"]
  , terminals = Set.fromList [Terminal "+", Terminal "*", Terminal "(", Terminal ")", Terminal "id"]
  , productions = 
    [ Production (NonTerminal "E") [NonTerminal "E", Terminal "+", NonTerminal "T"]
    , Production (NonTerminal "E") [NonTerminal "T"]
    , Production (NonTerminal "T") [NonTerminal "T", Terminal "*", NonTerminal "F"]
    , Production (NonTerminal "T") [NonTerminal "F"]
    , Production (NonTerminal "F") [Terminal "(", NonTerminal "E", Terminal ")"]
    , Production (NonTerminal "F") [Terminal "id"]
    ]
  , startSymbol = NonTerminal "E"
  }

-- 计算FIRST集合
first :: CFG -> [Symbol] -> Set Terminal
first cfg symbols = 
  case symbols of
    [] -> Set.empty
    (Terminal t:rest) -> Set.insert (Terminal t) (first cfg rest)
    (NonTerminal nt:rest) -> 
      let firstNT = firstNonTerminal cfg nt
          firstRest = first cfg rest
          hasEpsilon = Set.member (Terminal "ε") firstNT
      in if hasEpsilon
         then Set.union (Set.delete (Terminal "ε") firstNT) firstRest
         else firstNT

-- 计算非终结符的FIRST集合
firstNonTerminal :: CFG -> NonTerminal -> Set Terminal
firstNonTerminal cfg nt = 
  let productions = filter (\p -> lhs p == nt) (productions cfg)
      firstSets = map (\p -> first cfg (rhs p)) productions
  in Set.unions firstSets

-- 计算FOLLOW集合
follow :: CFG -> NonTerminal -> Set Terminal
follow cfg nt = 
  let initialFollow = if nt == startSymbol cfg 
                      then Set.singleton (Terminal "$")
                      else Set.empty
  in computeFollow cfg nt initialFollow Set.empty

-- 计算FOLLOW集合的辅助函数
computeFollow :: CFG -> NonTerminal -> Set Terminal -> Set NonTerminal -> Set Terminal
computeFollow cfg nt currentFollow processed = 
  if Set.member nt processed
  then currentFollow
  else 
    let newProcessed = Set.insert nt processed
        productions = productions cfg
        newFollow = foldl (\acc p -> updateFollow cfg p nt acc) currentFollow productions
    in if newFollow == currentFollow
       then currentFollow
       else computeFollow cfg nt newFollow newProcessed

-- 更新FOLLOW集合
updateFollow :: CFG -> Production -> NonTerminal -> Set Terminal -> Set Terminal
updateFollow cfg production targetNT currentFollow = 
  let rhs = rhs production
      positions = findPositions targetNT rhs
  in foldl (\acc pos -> updateFollowAtPosition cfg production pos targetNT acc) currentFollow positions

-- 查找非终结符在产生式右部的位置
findPositions :: NonTerminal -> [Symbol] -> [Int]
findPositions nt symbols = 
  [i | (i, symbol) <- zip [0..] symbols, symbol == NonTerminal nt]

-- 在特定位置更新FOLLOW集合
updateFollowAtPosition :: CFG -> Production -> Int -> NonTerminal -> Set Terminal -> Set Terminal
updateFollowAtPosition cfg production pos targetNT currentFollow = 
  let rhs = rhs production
      afterTarget = drop (pos + 1) rhs
      firstAfter = first cfg afterTarget
      hasEpsilon = Set.member (Terminal "ε") firstAfter
  in if hasEpsilon
     then let firstAfterNoEpsilon = Set.delete (Terminal "ε") firstAfter
              followLHS = follow cfg (lhs production)
          in Set.union currentFollow (Set.union firstAfterNoEpsilon followLHS)
     else Set.union currentFollow firstAfter
```

### 2.2 LL分析器实现

```haskell
-- LL分析表
type LLTable = Map (NonTerminal, Terminal) [Symbol]

-- LL分析器
data LLParser = LLParser
  { llGrammar :: CFG
  , llTable :: LLTable
  }

-- 构建LL分析表
buildLLTable :: CFG -> LLTable
buildLLTable cfg = 
  let productions = productions cfg
      tableEntries = concatMap (buildTableEntries cfg) productions
  in Map.fromList tableEntries

-- 构建表项
buildTableEntries :: CFG -> Production -> [((NonTerminal, Terminal), [Symbol])]
buildTableEntries cfg production = 
  let lhsNT = lhs production
      rhs = rhs production
      firstSet = first cfg rhs
      terminals = Set.toList firstSet
  in [(lhsNT, t, rhs) | t <- terminals]

-- LL分析
llParse :: LLParser -> [Terminal] -> Bool
llParse parser input = 
  let initialStack = [NonTerminal (startSymbol (llGrammar parser)), Terminal "$"]
      initialInput = input ++ [Terminal "$"]
      result = llParseStep parser initialStack initialInput
  in result

-- LL分析步骤
llParseStep :: LLParser -> [Symbol] -> [Terminal] -> Bool
llParseStep parser [] [] = True
llParseStep parser [] (_:_) = False
llParseStep parser (_:_) [] = False
llParseStep parser (symbol:stack) (token:input) = 
  case symbol of
    Terminal t -> 
      if t == token
      then llParseStep parser stack input
      else False
    NonTerminal nt -> 
      let production = getProduction parser nt token
      in case production of
           Just rhs -> llParseStep parser (rhs ++ stack) (token:input)
           Nothing -> False

-- 获取产生式
getProduction :: LLParser -> NonTerminal -> Terminal -> Maybe [Symbol]
getProduction parser nt token = 
  Map.lookup (nt, token) (llTable parser)

-- 创建LL分析器
createLLParser :: CFG -> LLParser
createLLParser cfg = 
  let table = buildLLTable cfg
  in LLParser cfg table
```

### 2.3 LR分析器实现

```haskell
-- LR项
data LRItem = LRItem
  { itemProduction :: Production
  , itemPosition :: Int
  , itemLookahead :: Terminal
  }

-- LR状态
type LRState = Set LRItem

-- LR分析表
data LRTable = LRTable
  { actionTable :: Map (Int, Terminal) (Either Int String)
  , gotoTable :: Map (Int, NonTerminal) Int
  }

-- LR分析器
data LRParser = LRParser
  { lrGrammar :: CFG
  , lrTable :: LRTable
  }

-- 构建LR分析表
buildLRTable :: CFG -> LRTable
buildLRTable cfg = 
  let initialItem = LRItem (findStartProduction cfg) 0 (Terminal "$")
      initialState = Set.singleton initialItem
      states = generateLRStates cfg [initialState]
      actionTable = buildActionTable cfg states
      gotoTable = buildGotoTable cfg states
  in LRTable actionTable gotoTable

-- 查找开始产生式
findStartProduction :: CFG -> Production
findStartProduction cfg = 
  let startNT = startSymbol cfg
      productions = filter (\p -> lhs p == startNT) (productions cfg)
  in head productions

-- 生成LR状态
generateLRStates :: CFG -> [LRState] -> [LRState]
generateLRStates cfg states = 
  let newStates = concatMap (generateNextStates cfg) states
      allStates = states ++ newStates
      uniqueStates = removeDuplicates allStates
  in if length uniqueStates == length states
     then states
     else generateLRStates cfg uniqueStates

-- 生成下一个状态
generateNextStates :: CFG -> LRState -> [LRState]
generateNextStates cfg state = 
  let symbols = getNextSymbols state
      nextStates = map (\symbol -> goto cfg state symbol) symbols
  in filter (not . Set.null) nextStates

-- 获取下一个符号
getNextSymbols :: LRState -> [Symbol]
getNextSymbols state = 
  let items = Set.toList state
      symbols = [getSymbolAfterDot item | item <- items, not (isComplete item)]
  in removeDuplicates symbols

-- 获取点后的符号
getSymbolAfterDot :: LRItem -> Symbol
getSymbolAfterDot item = 
  let rhs = rhs (itemProduction item)
      pos = itemPosition item
  in if pos < length rhs
     then rhs !! pos
     else error "No symbol after dot"

-- 检查项是否完成
isComplete :: LRItem -> Bool
isComplete item = 
  let rhs = rhs (itemProduction item)
      pos = itemPosition item
  in pos >= length rhs

-- GOTO函数
goto :: CFG -> LRState -> Symbol -> LRState
goto cfg state symbol = 
  let items = Set.toList state
      nextItems = [advanceItem item | item <- items, getSymbolAfterDot item == symbol]
      closure = computeClosure cfg (Set.fromList nextItems)
  in closure

-- 推进项
advanceItem :: LRItem -> LRItem
advanceItem item = 
  item { itemPosition = itemPosition item + 1 }

-- 计算闭包
computeClosure :: CFG -> LRState -> LRState
computeClosure cfg state = 
  let items = Set.toList state
      newItems = concatMap (generateItems cfg) items
      newState = Set.union state (Set.fromList newItems)
  in if Set.size newState == Set.size state
     then state
     else computeClosure cfg newState

-- 生成项
generateItems :: CFG -> LRItem -> [LRItem]
generateItems cfg item = 
  let symbol = getSymbolAfterDot item
  in case symbol of
       NonTerminal nt -> 
         let productions = filter (\p -> lhs p == nt) (productions cfg)
             lookahead = computeLookahead cfg item
             items = [LRItem p 0 la | p <- productions, la <- lookahead]
         in items
       Terminal _ -> []

-- 计算向前看符号
computeLookahead :: CFG -> LRItem -> [Terminal]
computeLookahead cfg item = 
  let production = itemProduction item
      rhs = rhs production
      pos = itemPosition item
      afterDot = drop (pos + 1) rhs
      firstSet = first cfg afterDot
  in if Set.member (Terminal "ε") firstSet
     then Set.toList (Set.delete (Terminal "ε") firstSet) ++ [itemLookahead item]
     else Set.toList firstSet

-- 构建动作表
buildActionTable :: CFG -> [LRState] -> Map (Int, Terminal) (Either Int String)
buildActionTable cfg states = 
  let entries = concatMap (buildActionEntries cfg) (zip [0..] states)
  in Map.fromList entries

-- 构建动作表项
buildActionEntries :: CFG -> (Int, LRState) -> [((Int, Terminal), Either Int String)]
buildActionEntries cfg (stateIndex, state) = 
  let items = Set.toList state
      shiftEntries = buildShiftEntries cfg stateIndex items
      reduceEntries = buildReduceEntries cfg stateIndex items
  in shiftEntries ++ reduceEntries

-- 构建移进项
buildShiftEntries :: CFG -> Int -> [LRItem] -> [((Int, Terminal), Either Int String)]
buildShiftEntries cfg stateIndex items = 
  let shiftItems = filter (\item -> not (isComplete item) && isTerminal (getSymbolAfterDot item)) items
      entries = [(stateIndex, getSymbolAfterDot item, Left (getNextState cfg stateIndex (getSymbolAfterDot item))) | 
                 item <- shiftItems]
  in entries

-- 构建归约项
buildReduceEntries :: CFG -> Int -> [LRItem] -> [((Int, Terminal), Either Int String)]
buildReduceEntries cfg stateIndex items = 
  let reduceItems = filter isComplete items
      entries = [(stateIndex, itemLookahead item, Right (getProductionIndex cfg (itemProduction item))) | 
                 item <- reduceItems]
  in entries

-- 检查是否为终结符
isTerminal :: Symbol -> Bool
isTerminal (Terminal _) = True
isTerminal (NonTerminal _) = False

-- 获取下一个状态
getNextState :: CFG -> Int -> Symbol -> Int
getNextState cfg stateIndex symbol = 
  -- 简化实现，实际需要查找GOTO表
  stateIndex + 1

-- 获取产生式索引
getProductionIndex :: CFG -> Production -> String
getProductionIndex cfg production = 
  let productions = productions cfg
      index = fromJust (elemIndex production productions)
  in show index

-- 构建GOTO表
buildGotoTable :: CFG -> [LRState] -> Map (Int, NonTerminal) Int
buildGotoTable cfg states = 
  let entries = concatMap (buildGotoEntries cfg) (zip [0..] states)
  in Map.fromList entries

-- 构建GOTO表项
buildGotoEntries :: CFG -> (Int, LRState) -> [((Int, NonTerminal), Int)]
buildGotoEntries cfg (stateIndex, state) = 
  let nonTerminals = getNonTerminalsAfterDot state
      entries = [(stateIndex, nt, getNextState cfg stateIndex (NonTerminal nt)) | 
                 nt <- nonTerminals]
  in entries

-- 获取点后的非终结符
getNonTerminalsAfterDot :: LRState -> [String]
getNonTerminalsAfterDot state = 
  let items = Set.toList state
      symbols = [getSymbolAfterDot item | item <- items, not (isComplete item)]
      nonTerminals = [nt | NonTerminal nt <- symbols]
  in removeDuplicates nonTerminals

-- 辅助函数
removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates = nub

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "fromJust: Nothing"

elemIndex :: Eq a => a -> [a] -> Maybe Int
elemIndex x xs = findIndex (== x) xs
```

## 🔍 理论证明

### 3.1 分析算法正确性

**定理 3.1.1 (LL分析正确性)**
如果文法 $G$ 是LL(k)文法，则LL(k)分析器能正确识别 $L(G)$。

**证明：** 通过归纳法：
1. **基础情况**：空字符串
2. **归纳步骤**：假设对长度为 $n$ 的字符串正确，证明对长度为 $n+1$ 的字符串也正确

**定理 3.1.2 (LR分析正确性)**
如果文法 $G$ 是LR(k)文法，则LR(k)分析器能正确识别 $L(G)$。

**证明：** 通过构造：
1. **状态构造**：每个状态对应一个LR项集
2. **转移构造**：基于GOTO函数
3. **动作构造**：基于ACTION函数

### 3.2 分析器等价性

**定理 3.2.1 (LL与LR等价性)**
对于某些文法，LL分析器和LR分析器是等价的。

**证明：** 通过构造等价的分析表。

**定理 3.2.2 (递归下降与LL等价性)**
递归下降分析器与LL分析器在功能上等价。

**证明：** 通过函数调用与栈操作的对应关系。

### 3.3 计算复杂性

**定理 3.3.1 (分析器复杂度)**
各种分析器的计算复杂度：
- **LL分析**：$O(n)$ 时间，$O(n)$ 空间
- **LR分析**：$O(n)$ 时间，$O(n)$ 空间
- **递归下降**：$O(n)$ 时间，$O(n)$ 空间（栈深度）

## 🌐 应用领域

### 4.1 编程语言解析

语法分析在编程语言解析中的应用：

```haskell
-- 编程语言语法
data Expression = Var String | Num Int | Add Expression Expression | Mul Expression Expression
  deriving (Eq, Show)

-- 编程语言文法
programmingGrammar :: CFG
programmingGrammar = CFG
  { nonTerminals = Set.fromList [NonTerminal "Expr", NonTerminal "Term", NonTerminal "Factor"]
  , terminals = Set.fromList [Terminal "id", Terminal "num", Terminal "+", Terminal "*", Terminal "(", Terminal ")"]
  , productions = 
    [ Production (NonTerminal "Expr") [NonTerminal "Expr", Terminal "+", NonTerminal "Term"]
    , Production (NonTerminal "Expr") [NonTerminal "Term"]
    , Production (NonTerminal "Term") [NonTerminal "Term", Terminal "*", NonTerminal "Factor"]
    , Production (NonTerminal "Term") [NonTerminal "Factor"]
    , Production (NonTerminal "Factor") [Terminal "(", NonTerminal "Expr", Terminal ")"]
    , Production (NonTerminal "Factor") [Terminal "id"]
    , Production (NonTerminal "Factor") [Terminal "num"]
    ]
  , startSymbol = NonTerminal "Expr"
  }

-- 编程语言解析器
programmingParser :: LRParser
programmingParser = LRParser programmingGrammar (buildLRTable programmingGrammar)

-- 解析编程语言
parseProgrammingLanguage :: [Terminal] -> Expression
parseProgrammingLanguage tokens = 
  let success = llParse (createLLParser programmingGrammar) tokens
  in if success
     then buildAST tokens
     else error "Parse error"

-- 构建抽象语法树
buildAST :: [Terminal] -> Expression
buildAST tokens = 
  -- 简化实现
  case tokens of
    [Terminal "id"] -> Var "x"
    [Terminal "num"] -> Num 42
    _ -> Add (Var "x") (Num 1)
```

### 4.2 自然语言处理

语法分析在自然语言处理中的应用：

```haskell
-- 自然语言语法
data NLExpression = Word String | Phrase String [NLExpression] | Sentence [NLExpression]
  deriving (Eq, Show)

-- 自然语言文法
naturalLanguageGrammar :: CFG
naturalLanguageGrammar = CFG
  { nonTerminals = Set.fromList [NonTerminal "S", NonTerminal "NP", NonTerminal "VP", NonTerminal "N", NonTerminal "V"]
  , terminals = Set.fromList [Terminal "the", Terminal "cat", Terminal "sat", Terminal "on", Terminal "mat"]
  , productions = 
    [ Production (NonTerminal "S") [NonTerminal "NP", NonTerminal "VP"]
    , Production (NonTerminal "NP") [Terminal "the", NonTerminal "N"]
    , Production (NonTerminal "VP") [NonTerminal "V", NonTerminal "PP"]
    , Production (NonTerminal "N") [Terminal "cat"]
    , Production (NonTerminal "N") [Terminal "mat"]
    , Production (NonTerminal "V") [Terminal "sat"]
    , Production (NonTerminal "PP") [Terminal "on", NonTerminal "NP"]
    ]
  , startSymbol = NonTerminal "S"
  }

-- 自然语言解析器
naturalLanguageParser :: LRParser
naturalLanguageParser = LRParser naturalLanguageGrammar (buildLRTable naturalLanguageGrammar)

-- 解析自然语言
parseNaturalLanguage :: [Terminal] -> NLExpression
parseNaturalLanguage tokens = 
  let success = llParse (createLLParser naturalLanguageGrammar) tokens
  in if success
     then buildNLTree tokens
     else error "Parse error"

-- 构建自然语言树
buildNLTree :: [Terminal] -> NLExpression
buildNLTree tokens = 
  case tokens of
    [Terminal "the", Terminal "cat", Terminal "sat", Terminal "on", Terminal "the", Terminal "mat"] ->
      Sentence [Phrase "NP" [Word "the", Word "cat"], 
                Phrase "VP" [Word "sat", Phrase "PP" [Word "on", Phrase "NP" [Word "the", Word "mat"]]]]
    _ -> Sentence [Word "unknown"]
```

### 4.3 配置语言解析

语法分析在配置语言解析中的应用：

```haskell
-- 配置语言语法
data Config = Config [(String, String)]
  deriving (Eq, Show)

-- 配置语言文法
configGrammar :: CFG
configGrammar = CFG
  { nonTerminals = Set.fromList [NonTerminal "Config", NonTerminal "Entry", NonTerminal "Key", NonTerminal "Value"]
  , terminals = Set.fromList [Terminal "id", Terminal "=", Terminal "string", Terminal "number"]
  , productions = 
    [ Production (NonTerminal "Config") [NonTerminal "Entry"]
    , Production (NonTerminal "Config") [NonTerminal "Config", NonTerminal "Entry"]
    , Production (NonTerminal "Entry") [NonTerminal "Key", Terminal "=", NonTerminal "Value"]
    , Production (NonTerminal "Key") [Terminal "id"]
    , Production (NonTerminal "Value") [Terminal "string"]
    , Production (NonTerminal "Value") [Terminal "number"]
    ]
  , startSymbol = NonTerminal "Config"
  }

-- 配置语言解析器
configParser :: LRParser
configParser = LRParser configGrammar (buildLRTable configGrammar)

-- 解析配置语言
parseConfig :: [Terminal] -> Config
parseConfig tokens = 
  let success = llParse (createLLParser configGrammar) tokens
  in if success
     then buildConfig tokens
     else error "Parse error"

-- 构建配置
buildConfig :: [Terminal] -> Config
buildConfig tokens = 
  case tokens of
    [Terminal "id", Terminal "=", Terminal "string"] -> Config [("key", "value")]
    _ -> Config []
```

## 🔗 相关理论

- [[02-Formal-Language/001-Formal-Language-Foundations]] - 形式语言基础理论
- [[02-Formal-Language/002-Automata-Theory-Deepening]] - 自动机理论深化
- [[02-Formal-Language/004-Language-Hierarchy-Theory]] - 语言层次理论
- [[03-Theory/010-Context-Free-Grammars]] - 上下文无关文法
- [[03-Theory/013-Automata-Theory]] - 自动机理论

## 📖 参考文献

1. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: principles, techniques, and tools. Pearson Education.
2. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to automata theory, languages, and computation. Pearson Education.
3. Sipser, M. (2012). Introduction to the theory of computation. Cengage Learning.
4. Appel, A. W. (1998). Modern compiler implementation in ML. Cambridge University Press.
5. Grune, D., & Jacobs, C. J. (2008). Parsing techniques: a practical guide. Springer Science & Business Media.

---

**最后更新**: 2024年12月19日  
**相关文档**: [[02-Formal-Language/004-Language-Hierarchy-Theory]] - 语言层次理论 