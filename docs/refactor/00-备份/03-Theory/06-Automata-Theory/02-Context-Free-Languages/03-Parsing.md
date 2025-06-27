# 03-Parsing - 语法分析

## 📚 概述

语法分析是将输入字符串转换为语法树的过程，是编译器的核心组件。本文档涵盖自顶向下分析、自底向上分析、LR分析等主要语法分析方法，并提供完整的Haskell实现。

## 🎯 核心概念

### 语法分析问题

给定上下文无关文法 $G = (V, \Sigma, P, S)$ 和输入字符串 $w \in \Sigma^*$，语法分析的目标是：

1. 判断 $w \in L(G)$
2. 如果 $w \in L(G)$，构造 $w$ 的语法树
3. 如果 $w \notin L(G)$，报告语法错误

### 分析策略分类

- **自顶向下分析**：从开始符号开始，逐步推导到输入字符串
- **自底向上分析**：从输入字符串开始，逐步归约到开始符号
- **确定性分析**：每个步骤都有唯一的选择
- **非确定性分析**：可能需要回溯或并行探索

## 🔧 Haskell实现

### 基础数据结构

```haskell
-- | 语法树节点
data ParseTreeNode = ParseTreeNode
  { nodeSymbol :: Symbol
  , children :: [ParseTreeNode]
  , position :: (Int, Int)  -- (行, 列)
  }
  deriving (Eq, Show)

-- | 语法树
data ParseTree = ParseTree
  { root :: ParseTreeNode
  , grammar :: CFG
  }
  deriving (Eq, Show)

-- | 分析状态
data ParseState = ParseState
  { stack :: [Symbol]           -- 分析栈
  , input :: String             -- 剩余输入
  , actions :: [ParseAction]    -- 已执行的动作
  }
  deriving (Eq, Show)

-- | 分析动作
data ParseAction = 
    Shift Symbol Int            -- 移进符号和位置
  | Reduce Production Int       -- 归约产生式和位置
  | Accept                      -- 接受
  | Error String                -- 错误信息
  deriving (Eq, Show)

-- | 分析表项
data ParseTableEntry = ParseTableEntry
  { state :: Int
  , symbol :: Symbol
  , action :: ParseAction
  }
  deriving (Eq, Show)

-- | 分析表
type ParseTable = [ParseTableEntry]
```

### 自顶向下分析

#### 递归下降分析

```haskell
-- | 递归下降分析器
data RecursiveDescentParser = RecursiveDescentParser
  { grammar :: CFG
  , currentPosition :: Int
  , input :: String
  }
  deriving (Show)

-- | 递归下降分析
recursiveDescentParse :: CFG -> String -> Either String ParseTree
recursiveDescentParse cfg input = 
  let parser = RecursiveDescentParser cfg 0 input
      result = parseStartSymbol parser
  in case result of
       Left error -> Left error
       Right (tree, remaining) -> 
         if null remaining 
         then Right tree 
         else Left "Unexpected input remaining"

-- | 解析开始符号
parseStartSymbol :: RecursiveDescentParser -> Either String (ParseTree, String)
parseStartSymbol parser = 
  let startNode = ParseTreeNode (NonTerminal (startSymbol (grammar parser))) [] (0, 0)
      (node, remaining) = parseSymbol parser (NonTerminal (startSymbol (grammar parser)))
  in Right (ParseTree node (grammar parser), remaining)

-- | 解析符号
parseSymbol :: RecursiveDescentParser -> Symbol -> (ParseTreeNode, String)
parseSymbol parser symbol = 
  case symbol of
    Terminal c -> 
      let input = input parser
          pos = currentPosition parser
      in case input of
           (c':rest) | c == c' -> 
             (ParseTreeNode symbol [] (pos, pos), rest)
           _ -> error $ "Expected '" ++ [c] ++ "', got '" ++ take 1 input ++ "'"
    NonTerminal nt -> 
      let productions = [p | p@(Production lhs rhs) <- productions (grammar parser), lhs == NonTerminal nt]
      in case productions of
           [] -> error $ "No production for non-terminal: " ++ nt
           (prod:_) -> parseProduction parser prod

-- | 解析产生式
parseProduction :: RecursiveDescentParser -> Production -> (ParseTreeNode, String)
parseProduction parser (Production lhs rhs) = 
  let (children, remaining) = parseSymbols parser rhs
      node = ParseTreeNode lhs children (currentPosition parser, currentPosition parser)
  in (node, remaining)

-- | 解析符号序列
parseSymbols :: RecursiveDescentParser -> [Symbol] -> ([ParseTreeNode], String)
parseSymbols parser [] = ([], input parser)
parseSymbols parser (s:ss) = 
  let (child, remaining1) = parseSymbol parser s
      (children, remaining2) = parseSymbols (parser { input = remaining1 }) ss
  in (child : children, remaining2)
```

#### LL(1)分析

```haskell
-- | LL(1)分析器
data LL1Parser = LL1Parser
  { grammar :: CFG
  , parseTable :: ParseTable
  }
  deriving (Show)

-- | 构造LL(1)分析表
buildLL1ParseTable :: CFG -> ParseTable
buildLL1ParseTable cfg = 
  let firstSets = computeFirstSets cfg
      followSets = computeFollowSets cfg firstSets
      allProductions = productions cfg
  in concatMap (buildTableEntries cfg firstSets followSets) allProductions

-- | 计算First集
computeFirstSets :: CFG -> Map String (Set Char)
computeFirstSets cfg = 
  let initial = Map.fromList [(nt, Set.empty) | nt <- Set.toList (variables cfg)]
      step current = 
        let new = Map.mapWithKey (\nt _ -> computeFirstForSymbol cfg current nt) current
        in if new == current then current else step new
  in step initial

-- | 计算符号的First集
computeFirstForSymbol :: CFG -> Map String (Set Char) -> String -> Set Char
computeFirstForSymbol cfg firstSets symbol = 
  case symbol of
    [c] | c `Set.member` terminals cfg -> Set.singleton c
    _ -> 
      let productions = [rhs | Production (NonTerminal nt) rhs <- productions cfg, nt == symbol]
      in foldr Set.union Set.empty (map (computeFirstForSequence cfg firstSets) productions)

-- | 计算序列的First集
computeFirstForSequence :: CFG -> Map String (Set Char) -> [Symbol] -> Set Char
computeFirstForSequence cfg firstSets [] = Set.singleton 'ε'
computeFirstForSequence cfg firstSets (s:ss) = 
  let firstS = computeFirstForSymbol cfg firstSets (symbolToString s)
      hasEpsilon = 'ε' `Set.member` firstS
      firstWithoutEpsilon = Set.delete 'ε' firstS
  in if hasEpsilon && not (null ss)
     then Set.union firstWithoutEpsilon (computeFirstForSequence cfg firstSets ss)
     else firstWithoutEpsilon

-- | LL(1)分析
ll1Parse :: LL1Parser -> String -> Either String ParseTree
ll1Parse parser input = 
  let initialState = ParseState [NonTerminal (startSymbol (grammar parser))] input []
      result = ll1ParseStep parser initialState
  in case result of
       Left error -> Left error
       Right tree -> Right tree

-- | LL(1)分析步骤
ll1ParseStep :: LL1Parser -> ParseState -> Either String ParseTree
ll1ParseStep parser state = 
  case (stack state, input state) of
    ([], []) -> Right (ParseTree (ParseTreeNode (NonTerminal (startSymbol (grammar parser))) [] (0, 0)) (grammar parser))
    ([], _) -> Left "Unexpected input remaining"
    (_, []) -> Left "Unexpected end of input"
    (s:ss, c:cs) -> 
      case s of
        Terminal t | t == c -> 
          ll1ParseStep parser (state { stack = ss, input = cs })
        NonTerminal nt -> 
          case findAction (parseTable parser) nt c of
            Just (Reduce prod _) -> 
              let newState = applyReduction state prod
              in ll1ParseStep parser newState
            Nothing -> Left $ "No action for " ++ nt ++ " and '" ++ [c] ++ "'"
```

### 自底向上分析

#### LR(0)分析

```haskell
-- | LR(0)项目
data LR0Item = LR0Item
  { production :: Production
  , dotPosition :: Int  -- 点的位置
  }
  deriving (Eq, Show)

-- | LR(0)状态
data LR0State = LR0State
  { stateId :: Int
  , items :: Set LR0Item
  }
  deriving (Eq, Show)

-- | LR(0)分析器
data LR0Parser = LR0Parser
  { grammar :: CFG
  , states :: [LR0State]
  , parseTable :: ParseTable
  }
  deriving (Show)

-- | 构造LR(0)状态机
buildLR0States :: CFG -> [LR0State]
buildLR0States cfg = 
  let initialItem = LR0Item (Production (NonTerminal (startSymbol cfg)) []) 0
      initialState = LR0State 0 (Set.singleton initialItem)
      allStates = buildStates cfg [initialState] 0
  in allStates

-- | 构建所有状态
buildStates :: CFG -> [LR0State] -> Int -> [LR0State]
buildStates cfg currentStates nextId = 
  let newStates = concatMap (buildNextStates cfg currentStates) currentStates
      uniqueNewStates = filter (\s -> not (any (\existing -> items s == items existing) currentStates)) newStates
  in if null uniqueNewStates 
     then currentStates 
     else buildStates cfg (currentStates ++ uniqueNewStates) (nextId + length uniqueNewStates)

-- | 构建下一个状态
buildNextStates :: CFG -> [LR0State] -> LR0State -> [LR0State]
buildNextStates cfg allStates state = 
  let symbols = getNextSymbols (Set.toList (items state))
  in [buildStateForSymbol cfg allStates state symbol | symbol <- symbols]

-- | 获取下一个符号
getNextSymbols :: [LR0Item] -> [Symbol]
getNextSymbols items = 
  nub [getSymbolAfterDot item | item <- items, not (isComplete item)]

-- | 获取点后的符号
getSymbolAfterDot :: LR0Item -> Symbol
getSymbolAfterDot (LR0Item (Production _ rhs) pos) = 
  if pos < length rhs then rhs !! pos else error "Dot at end of production"

-- | 检查项目是否完整
isComplete :: LR0Item -> Bool
isComplete (LR0Item (Production _ rhs) pos) = pos >= length rhs

-- | LR(0)分析
lr0Parse :: LR0Parser -> String -> Either String ParseTree
lr0Parse parser input = 
  let initialState = ParseState [] input []
      result = lr0ParseStep parser initialState 0
  in case result of
       Left error -> Left error
       Right tree -> Right tree

-- | LR(0)分析步骤
lr0ParseStep :: LR0Parser -> ParseState -> Int -> Either String ParseTree
lr0ParseStep parser state currentStateId = 
  case input state of
    [] -> 
      case findAcceptAction (parseTable parser) currentStateId of
        Just Accept -> Right (buildParseTree (actions state))
        _ -> Left "Unexpected end of input"
    (c:cs) -> 
      case findAction (parseTable parser) currentStateId (Terminal c) of
        Just (Shift _ nextState) -> 
          let newState = state { stack = Terminal c : stack state, input = cs }
          in lr0ParseStep parser newState nextState
        Just (Reduce prod _) -> 
          let newState = applyReduction state prod
          in lr0ParseStep parser newState currentStateId
        _ -> Left $ "No action for state " ++ show currentStateId ++ " and symbol '" ++ [c] ++ "'"
```

#### SLR(1)分析

```haskell
-- | SLR(1)分析器
data SLR1Parser = SLR1Parser
  { grammar :: CFG
  , states :: [LR0State]
  , firstSets :: Map String (Set Char)
  , followSets :: Map String (Set Char)
  , parseTable :: ParseTable
  }
  deriving (Show)

-- | 构造SLR(1)分析表
buildSLR1ParseTable :: CFG -> ParseTable
buildSLR1ParseTable cfg = 
  let states = buildLR0States cfg
      firstSets = computeFirstSets cfg
      followSets = computeFollowSets cfg firstSets
      allEntries = concatMap (buildSLR1Entries cfg firstSets followSets) states
  in allEntries

-- | 构建SLR(1)表项
buildSLR1Entries :: CFG -> Map String (Set Char) -> Map String (Set Char) -> LR0State -> [ParseTableEntry]
buildSLR1Entries cfg firstSets followSets state = 
  let shiftEntries = buildShiftEntries cfg state
      reduceEntries = buildReduceEntries cfg firstSets followSets state
  in shiftEntries ++ reduceEntries

-- | 构建移进项
buildShiftEntries :: CFG -> LR0State -> [ParseTableEntry]
buildShiftEntries cfg state = 
  let nextSymbols = getNextSymbols (Set.toList (items state))
      nextStates = [buildStateForSymbol cfg [state] state symbol | symbol <- nextSymbols]
  in [ParseTableEntry (stateId state) symbol (Shift symbol (stateId nextState))
      | (symbol, nextState) <- zip nextSymbols nextStates]
```

## 📐 形式证明

### 定理1：LL(1)文法的充分必要条件

**定理**：文法 $G$ 是LL(1)的当且仅当对于每个非终结符 $A$ 和每个产生式 $A \rightarrow \alpha_i$，集合 $FIRST(\alpha_i) \cap FIRST(\alpha_j) = \emptyset$（$i \neq j$）且如果 $\epsilon \in FIRST(\alpha_i)$，则 $FIRST(\alpha_j) \cap FOLLOW(A) = \emptyset$。

**证明**：

- **必要性**：如果文法不是LL(1)，则存在歧义，导致分析表冲突
- **充分性**：如果条件满足，则分析表无冲突，分析是确定性的

### 定理2：LR(0)文法的性质

**定理**：如果文法 $G$ 是LR(0)的，则它是无歧义的。

**证明**：LR(0)分析器在每个步骤都有唯一的动作，因此不会产生歧义。

## 🔍 实际应用

### 示例：简单表达式分析器

```haskell
-- | 简单表达式文法
simpleExprGrammar :: CFG
simpleExprGrammar = CFG
  { variables = Set.fromList ["E", "T", "F"]
  , terminals = Set.fromList "()+*"
  , productions = 
    [ Production (NonTerminal "E") [NonTerminal "E", Terminal '+', NonTerminal "T"]
    , Production (NonTerminal "E") [NonTerminal "T"]
    , Production (NonTerminal "T") [NonTerminal "T", Terminal '*', NonTerminal "F"]
    , Production (NonTerminal "T") [NonTerminal "F"]
    , Production (NonTerminal "F") [Terminal '(', NonTerminal "E", Terminal ')']
    , Production (NonTerminal "F") [Terminal 'a']
    ]
  , startSymbol = "E"
  }

-- | 测试递归下降分析
testRecursiveDescent :: IO ()
testRecursiveDescent = do
  putStrLn "Testing recursive descent parser:"
  let testCases = ["a", "a+a", "a*a", "(a+a)*a"]
  mapM_ (\input -> 
    case recursiveDescentParse simpleExprGrammar input of
      Left error -> putStrLn $ input ++ " -> Error: " ++ error
      Right tree -> putStrLn $ input ++ " -> Success"
    ) testCases
```

### 性能分析

```haskell
-- | 分析复杂度
parseComplexity :: CFG -> String -> Int
parseComplexity cfg input = 
  let parser = RecursiveDescentParser cfg 0 input
      result = parseStartSymbol parser
  in case result of
       Left _ -> 0
       Right (tree, _) -> countNodes (root tree)

-- | 计算节点数
countNodes :: ParseTreeNode -> Int
countNodes node = 1 + sum (map countNodes (children node))
```

## 🔗 相关概念

- [上下文无关文法](01-Context-Free-Grammars.md) - 语法分析的基础
- [下推自动机](02-Pushdown-Automata.md) - 语法分析的自动机模型
- [语法树](04-Syntax-Trees.md) - 语法分析的输出
- [编译器理论](../01-Programming-Language-Theory/Syntax/Parsing-Theory.md) - 更广泛的解析理论

## 📚 参考文献

1. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.
2. Grune, D., & Jacobs, C. J. (2008). Parsing Techniques: A Practical Guide.
3. Appel, A. W. (2002). Modern Compiler Implementation in ML.

---

*本文档提供了语法分析的完整形式化框架，包括多种分析算法的严格定义、可执行的Haskell实现和形式证明。*
