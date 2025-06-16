# 01-Formal-Grammars (形式文法)

## 📚 形式文法概述

形式文法是定义语言语法结构的数学工具，是编程语言设计和编译器实现的理论基础。我们研究从正则文法到上下文无关文法的完整体系。

## 🏗️ 理论框架

### 1. 基本定义

#### 形式化定义

**定义 1.1 (文法)** 一个文法 $G$ 是一个四元组 $(V_N, V_T, P, S)$，其中：

- $V_N$ 是非终结符集合
- $V_T$ 是终结符集合，且 $V_N \cap V_T = \emptyset$
- $P$ 是产生式集合，每个产生式形如 $\alpha \rightarrow \beta$
- $S \in V_N$ 是开始符号

**定义 1.2 (推导)** 对于文法 $G$，如果存在产生式 $\alpha \rightarrow \beta$，则称 $\gamma \alpha \delta \Rightarrow \gamma \beta \delta$ 为一步推导。

**定义 1.3 (语言)** 文法 $G$ 生成的语言 $L(G) = \{w \in V_T^* \mid S \Rightarrow^* w\}$。

#### Haskell实现

```haskell
-- 形式文法的基础定义
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

-- 符号类型
data Symbol = Terminal String | NonTerminal String
  deriving (Eq, Show)

-- 产生式
data Production = Production 
  { leftSide :: [Symbol]
  , rightSide :: [Symbol]
  } deriving (Eq, Show)

-- 文法
data Grammar = Grammar
  { nonTerminals :: [String]
  , terminals :: [String]
  , productions :: [Production]
  , startSymbol :: String
  } deriving (Eq, Show)

-- 推导步骤
data DerivationStep = DerivationStep
  { before :: [Symbol]
  , after :: [Symbol]
  , production :: Production
  } deriving (Eq, Show)

-- 完整推导
type Derivation = [DerivationStep]

-- 文法验证
validateGrammar :: Grammar -> Bool
validateGrammar (Grammar nt t p s) = 
  s `elem` nt && -- 开始符号在非终结符中
  all validProduction p && -- 所有产生式有效
  disjoint nt t -- 非终结符和终结符不相交
  where
    validProduction (Production left right) =
      not (null left) && -- 左部非空
      any (`elem` nt) (map getSymbolName left) -- 左部包含非终结符
    getSymbolName (Terminal name) = name
    getSymbolName (NonTerminal name) = name
    disjoint xs ys = null (xs `intersect` ys)

-- 一步推导
oneStepDerivation :: Grammar -> [Symbol] -> [DerivationStep]
oneStepDerivation grammar sententialForm = 
  concatMap (applyProduction sententialForm) (productions grammar)
  where
    applyProduction :: [Symbol] -> Production -> [DerivationStep]
    applyProduction symbols (Production left right) =
      let positions = findSubsequence left symbols
      in map (\pos -> DerivationStep symbols (replaceAt pos left right symbols) (Production left right)) positions

-- 查找子序列位置
findSubsequence :: Eq a => [a] -> [a] -> [Int]
findSubsequence sub seq = 
  [i | i <- [0..length seq - length sub], 
       sub == take (length sub) (drop i seq)]

-- 替换序列
replaceAt :: Int -> [a] -> [a] -> [a] -> [a]
replaceAt pos old new seq = 
  take pos seq ++ new ++ drop (pos + length old) seq

-- 多步推导
multiStepDerivation :: Grammar -> [Symbol] -> [[Symbol]]
multiStepDerivation grammar start = 
  let steps = oneStepDerivation grammar start
      nextForms = map after steps
  in start : concatMap (multiStepDerivation grammar) nextForms

-- 检查字符串是否属于语言
isInLanguage :: Grammar -> String -> Bool
isInLanguage grammar input = 
  let startSymbol = NonTerminal (startSymbol grammar)
      derivations = multiStepDerivation grammar [startSymbol]
      terminalStrings = map (filter isTerminal) derivations
  in any (== map Terminal (words input)) terminalStrings
  where
    isTerminal (Terminal _) = True
    isTerminal _ = False
```

### 2. 正则文法

#### 2.1 形式化定义

**定义 2.1 (正则文法)** 正则文法是一种特殊的上下文无关文法，其中所有产生式都形如：

- $A \rightarrow aB$ (右线性)
- $A \rightarrow Ba$ (左线性)
- $A \rightarrow a$ (终止产生式)

**定理 2.1** 正则文法生成的语言恰好是正则语言。

#### 2.2 Haskell实现

```haskell
-- 正则文法
data RegularGrammar = RegularGrammar
  { rgNonTerminals :: [String]
  , rgTerminals :: [String]
  , rgProductions :: [RegularProduction]
  , rgStartSymbol :: String
  } deriving (Eq, Show)

-- 正则产生式
data RegularProduction = RegularProduction
  { rgLeft :: String
  , rgRight :: Either String (String, String) -- Either terminal or (terminal, nonTerminal)
  } deriving (Eq, Show)

-- 验证正则文法
isRegularGrammar :: RegularGrammar -> Bool
isRegularGrammar (RegularGrammar nt t p s) =
  s `elem` nt &&
  all isRegularProduction p
  where
    isRegularProduction (RegularProduction left right) =
      left `elem` nt &&
      case right of
        Left terminal -> terminal `elem` t
        Right (terminal, nonTerminal) -> 
          terminal `elem` t && nonTerminal `elem` nt

-- 正则文法到有限自动机的转换
data FiniteAutomaton = FiniteAutomaton
  { states :: [String]
  , alphabet :: [String]
  , transitions :: [(String, String, String)] -- (state, symbol, nextState)
  , startState :: String
  , acceptStates :: [String]
  } deriving (Eq, Show)

-- 正则文法转有限自动机
regularGrammarToFA :: RegularGrammar -> FiniteAutomaton
regularGrammarToFA (RegularGrammar nt t p s) =
  FiniteAutomaton
    { states = nt ++ ["q_final"]
    , alphabet = t
    , transitions = concatMap productionToTransitions p
    , startState = s
    , acceptStates = ["q_final"]
    }
  where
    productionToTransitions (RegularProduction left right) =
      case right of
        Left terminal -> [(left, terminal, "q_final")]
        Right (terminal, nonTerminal) -> [(left, terminal, nonTerminal)]

-- 有限自动机执行
runFA :: FiniteAutomaton -> String -> Bool
runFA fa input = 
  let finalState = foldl step (startState fa) (words input)
  in finalState `elem` acceptStates fa
  where
    step currentState symbol =
      case lookup (currentState, symbol) (map (\(s, sy, ns) -> ((s, sy), ns)) (transitions fa)) of
        Just nextState -> nextState
        Nothing -> "reject"
```

### 3. 上下文无关文法

#### 3.1 形式化定义

**定义 3.1 (上下文无关文法)** 上下文无关文法是一种文法，其中所有产生式都形如 $A \rightarrow \alpha$，其中 $A \in V_N$，$\alpha \in (V_N \cup V_T)^*$。

**定义 3.2 (Chomsky范式)** 如果所有产生式都形如 $A \rightarrow BC$ 或 $A \rightarrow a$，则称文法为Chomsky范式。

#### 3.2 Haskell实现

```haskell
-- 上下文无关文法
data CFGrammar = CFGrammar
  { cfNonTerminals :: [String]
  , cfTerminals :: [String]
  , cfProductions :: [CFProduction]
  , cfStartSymbol :: String
  } deriving (Eq, Show)

-- CFG产生式
data CFProduction = CFProduction
  { cfLeft :: String
  , cfRight :: [String]
  } deriving (Eq, Show)

-- 验证CFG
isCFGrammar :: CFGrammar -> Bool
isCFGrammar (CFGrammar nt t p s) =
  s `elem` nt &&
  all isCFProduction p
  where
    isCFProduction (CFProduction left right) =
      left `elem` nt &&
      all (\sym -> sym `elem` nt || sym `elem` t) right

-- 消除左递归
eliminateLeftRecursion :: CFGrammar -> CFGrammar
eliminateLeftRecursion (CFGrammar nt t p s) =
  CFGrammar nt t (eliminateRecursion p) s
  where
    eliminateRecursion :: [CFProduction] -> [CFProduction]
    eliminateRecursion [] = []
    eliminateRecursion (prod:prods) =
      let (newProds, remaining) = eliminateForSymbol prod prods
      in newProds ++ eliminateRecursion remaining

    eliminateForSymbol :: CFProduction -> [CFProduction] -> ([CFProduction], [CFProduction])
    eliminateForSymbol (CFProduction left right) prods =
      let (recursive, nonRecursive) = partition (isLeftRecursive left) prods
      in if null recursive
         then ([CFProduction left right], prods)
         else let newSymbol = left ++ "'"
                  newProds = map (eliminateLeftRecursion' left newSymbol) recursive
                  nonRecProds = map (CFProduction left) (addNewSymbol nonRecursive newSymbol)
              in (nonRecProds ++ newProds, filter (not . isLeftRecursive left) prods)

    isLeftRecursive :: String -> CFProduction -> Bool
    isLeftRecursive symbol (CFProduction left right) =
      left == symbol && not (null right) && head right == symbol

    eliminateLeftRecursion' :: String -> String -> CFProduction -> CFProduction
    eliminateLeftRecursion' oldSymbol newSymbol (CFProduction left right) =
      CFProduction newSymbol (tail right ++ [newSymbol])

    addNewSymbol :: [CFProduction] -> String -> [[String]]
    addNewSymbol prods newSymbol =
      map (\(CFProduction _ right) -> right ++ [newSymbol]) prods

-- CYK算法实现
data CYKTable = CYKTable
  { table :: [[[String]]]
  , input :: [String]
  } deriving (Eq, Show)

-- CYK解析
cykParse :: CFGrammar -> [String] -> Bool
cykParse grammar input =
  let n = length input
      table = buildCYKTable grammar input n
      startSymbol = cfStartSymbol grammar
  in startSymbol `elem` (table !! 0 !! (n-1))

buildCYKTable :: CFGrammar -> [String] -> Int -> [[[String]]]
buildCYKTable grammar input n =
  let initialTable = replicate n (replicate n [])
      table1 = fillDiagonal grammar input initialTable
  in fillTable grammar table1 n

fillDiagonal :: CFGrammar -> [String] -> [[[String]]] -> [[[String]]]
fillDiagonal grammar input table =
  zipWith (\i symbol -> updateTable table i i (findNonTerminals grammar [symbol])) 
          [0..] input

fillTable :: CFGrammar -> [[[String]]] -> Int -> [[[String]]]
fillTable grammar table n =
  foldl (\t len -> fillLength grammar t len n) table [2..n]

fillLength :: CFGrammar -> [[[String]]] -> Int -> Int -> [[[String]]]
fillLength grammar table len n =
  foldl (\t i -> fillPosition grammar t i len n) table [0..n-len]

fillPosition :: CFGrammar -> [[[String]]] -> Int -> Int -> Int -> [[[String]]]
fillPosition grammar table i len n =
  foldl (\t k -> combinePositions grammar t i k len) table [0..len-1]

combinePositions :: CFGrammar -> [[[String]]] -> Int -> Int -> Int -> [[[String]]]
combinePositions grammar table i k len =
  let pos1 = table !! i !! (i + k)
      pos2 = table !! (i + k + 1) !! (i + len - 1)
      combinations = [a ++ b | a <- pos1, b <- pos2]
      nonTerminals = concatMap (findNonTerminals grammar) combinations
  in updateTable table i (i + len - 1) nonTerminals

findNonTerminals :: CFGrammar -> [String] -> [String]
findNonTerminals grammar symbols =
  [left | CFProduction left right <- cfProductions grammar, right == symbols]

updateTable :: [[[String]]] -> Int -> Int -> [String] -> [[[String]]]
updateTable table i j newSymbols =
  let row = table !! i
      newRow = take j row ++ [newSymbols] ++ drop (j + 1) row
  in take i table ++ [newRow] ++ drop (i + 1) table
```

### 4. 属性文法

#### 4.1 形式化定义

**定义 4.1 (属性文法)** 属性文法是一个三元组 $(G, A, R)$，其中：

- $G$ 是上下文无关文法
- $A$ 是属性集合
- $R$ 是语义规则集合

**定义 4.2 (综合属性)** 如果属性值从子节点计算得到，则称为综合属性。

**定义 4.3 (继承属性)** 如果属性值从父节点或兄弟节点得到，则称为继承属性。

#### 4.2 Haskell实现

```haskell
-- 属性文法
data AttributeGrammar = AttributeGrammar
  { baseGrammar :: CFGrammar
  , attributes :: [Attribute]
  , semanticRules :: [SemanticRule]
  } deriving (Eq, Show)

-- 属性
data Attribute = Attribute
  { attrName :: String
  , attrType :: String
  , attrKind :: AttributeKind
  } deriving (Eq, Show)

data AttributeKind = Synthesized | Inherited
  deriving (Eq, Show)

-- 语义规则
data SemanticRule = SemanticRule
  { ruleTarget :: String
  , ruleValue :: AttributeExpression
  } deriving (Eq, Show)

-- 属性表达式
data AttributeExpression = 
    AttrRef String String -- node.attribute
  | Literal String
  | BinaryOp String AttributeExpression AttributeExpression
  | UnaryOp String AttributeExpression
  deriving (Eq, Show)

-- 属性求值
evaluateAttributes :: AttributeGrammar -> ParseTree -> AttributeEnvironment
evaluateAttributes ag tree =
  let initialEnv = initializeAttributes ag tree
  in evaluateSynthesized ag tree initialEnv

-- 属性环境
type AttributeEnvironment = [(String, String, String)] -- (node, attribute, value)

-- 初始化属性
initializeAttributes :: AttributeGrammar -> ParseTree -> AttributeEnvironment
initializeAttributes ag tree = 
  concatMap (initializeNodeAttributes ag) (getAllNodes tree)

-- 求值综合属性
evaluateSynthesized :: AttributeGrammar -> ParseTree -> AttributeEnvironment -> AttributeEnvironment
evaluateSynthesized ag tree env =
  let synthesizedAttrs = filter (isSynthesized ag) (attributes ag)
      newEnv = foldl (\e attr -> evaluateAttribute ag tree attr e) env synthesizedAttrs
  in if env == newEnv then env else evaluateSynthesized ag tree newEnv

-- 求值单个属性
evaluateAttribute :: AttributeGrammar -> ParseTree -> Attribute -> AttributeEnvironment -> AttributeEnvironment
evaluateAttribute ag tree attr env =
  let rules = filter (\r -> ruleTarget r == attrName attr) (semanticRules ag)
      values = map (\r -> evaluateRule ag tree r env) rules
  in foldl (\e v -> updateEnvironment e (getNodeId tree) (attrName attr) v) env values

-- 求值语义规则
evaluateRule :: AttributeGrammar -> ParseTree -> SemanticRule -> AttributeEnvironment -> String
evaluateRule ag tree rule env =
  evaluateExpression ag tree (ruleValue rule) env

-- 求值表达式
evaluateExpression :: AttributeGrammar -> ParseTree -> AttributeExpression -> AttributeEnvironment -> String
evaluateExpression ag tree expr env =
  case expr of
    AttrRef node attr -> lookupAttribute env node attr
    Literal value -> value
    BinaryOp op e1 e2 -> 
      let v1 = evaluateExpression ag tree e1 env
          v2 = evaluateExpression ag tree e2 env
      in applyBinaryOp op v1 v2
    UnaryOp op e -> 
      let v = evaluateExpression ag tree e env
      in applyUnaryOp op v

-- 应用二元操作
applyBinaryOp :: String -> String -> String -> String
applyBinaryOp "+" a b = show (read a + read b)
applyBinaryOp "-" a b = show (read a - read b)
applyBinaryOp "*" a b = show (read a * read b)
applyBinaryOp "/" a b = show (read a `div` read b)
applyBinaryOp _ a b = a ++ b

-- 应用一元操作
applyUnaryOp :: String -> String -> String
applyUnaryOp "-" a = show (-read a)
applyUnaryOp "length" a = show (length a)
applyUnaryOp _ a = a

-- 查找属性值
lookupAttribute :: AttributeEnvironment -> String -> String -> String
lookupAttribute env node attr =
  case lookup (node, attr) (map (\(n, a, v) -> ((n, a), v)) env) of
    Just value -> value
    Nothing -> "undefined"

-- 更新环境
updateEnvironment :: AttributeEnvironment -> String -> String -> String -> AttributeEnvironment
updateEnvironment env node attr value =
  (node, attr, value) : filter (\(n, a, _) -> n /= node || a /= attr) env

-- 检查是否为综合属性
isSynthesized :: AttributeGrammar -> Attribute -> Bool
isSynthesized ag attr = attrKind attr == Synthesized
```

## 🎯 应用实例

### 1. 简单算术表达式文法

```haskell
-- 算术表达式文法
arithmeticGrammar :: CFGrammar
arithmeticGrammar = CFGrammar
  { cfNonTerminals = ["E", "T", "F"]
  , cfTerminals = ["+", "*", "(", ")", "id"]
  , cfProductions = 
    [ CFProduction "E" ["E", "+", "T"]
    , CFProduction "E" ["T"]
    , CFProduction "T" ["T", "*", "F"]
    , CFProduction "T" ["F"]
    , CFProduction "F" ["(", "E", ")"]
    , CFProduction "F" ["id"]
    ]
  , cfStartSymbol = "E"
  }

-- 测试文法
testArithmeticGrammar :: IO ()
testArithmeticGrammar = do
  let input1 = ["id", "+", "id", "*", "id"]
  let input2 = ["(", "id", "+", "id", ")", "*", "id"]
  
  putStrLn "Testing arithmetic grammar:"
  putStrLn $ "Input 1: " ++ show input1 ++ " -> " ++ show (cykParse arithmeticGrammar input1)
  putStrLn $ "Input 2: " ++ show input2 ++ " -> " ++ show (cykParse arithmeticGrammar input2)
```

### 2. 类型检查文法

```haskell
-- 类型检查文法
typeCheckGrammar :: CFGrammar
typeCheckGrammar = CFGrammar
  { cfNonTerminals = ["Expr", "Type", "Context"]
  , cfTerminals = ["var", "lambda", "apply", "int", "bool", "->", ":", ","]
  , cfProductions = 
    [ CFProduction "Expr" ["var"]
    , CFProduction "Expr" ["lambda", "var", ":", "Type", ".", "Expr"]
    , CFProduction "Expr" ["apply", "Expr", "Expr"]
    , CFProduction "Type" ["int"]
    , CFProduction "Type" ["bool"]
    , CFProduction "Type" ["Type", "->", "Type"]
    ]
  , cfStartSymbol = "Expr"
  }
```

## 📚 相关理论

- [解析理论](02-Parsing-Theory.md) - 解析算法和实现
- [语法分析](03-Syntax-Analysis.md) - 语法分析技术
- [编译器构造](04-Compiler-Construction.md) - 编译器实现

## 🔬 研究方向

### 当前热点

- **增量解析**：支持增量更新的解析算法
- **错误恢复**：语法错误的自动恢复
- **并行解析**：多线程解析技术
- **语法扩展**：可扩展的语法定义

### 应用领域

- **编程语言设计**：新语言的语法定义
- **编译器实现**：语法分析器的构建
- **自然语言处理**：自然语言的语法分析
- **配置文件解析**：配置文件的语法定义

---

**上一级**: [语法理论](README.md)  
**下一级**: [解析理论](02-Parsing-Theory.md) | [语法分析](03-Syntax-Analysis.md) | [编译器构造](04-Compiler-Construction.md)
