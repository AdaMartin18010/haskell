# 01. 形式语法理论 (Formal Grammar Theory)

## 📋 概述

形式语法理论是编程语言理论的基础，研究语言的结构和形式化表示。本文档从数学定义、形式化证明和Haskell实现三个维度探讨形式语法理论。

## 🎯 数学基础

### 1. 形式语法定义

#### 1.1 基本概念

**定义 1.1** (字母表)
字母表 $\Sigma$ 是一个有限的符号集合。

**定义 1.2** (字符串)
给定字母表 $\Sigma$，字符串是 $\Sigma$ 中符号的有限序列。空字符串记为 $\epsilon$。

**定义 1.3** (语言)
给定字母表 $\Sigma$，语言是 $\Sigma^*$ 的子集，其中 $\Sigma^*$ 表示所有可能字符串的集合。

#### 1.2 上下文无关文法

**定义 1.4** (上下文无关文法)
上下文无关文法是一个四元组 $G = (V, \Sigma, P, S)$，其中：

- $V$ 是非终结符集合
- $\Sigma$ 是终结符集合，且 $V \cap \Sigma = \emptyset$
- $P$ 是产生式集合，每个产生式形如 $A \rightarrow \alpha$，其中 $A \in V$，$\alpha \in (V \cup \Sigma)^*$
- $S \in V$ 是开始符号

**定理 1.1** (推导关系)
对于上下文无关文法 $G = (V, \Sigma, P, S)$，定义推导关系 $\Rightarrow_G$：

- 如果 $A \rightarrow \alpha \in P$，则 $\beta A \gamma \Rightarrow_G \beta \alpha \gamma$
- 如果 $\alpha \Rightarrow_G \beta$ 且 $\beta \Rightarrow_G \gamma$，则 $\alpha \Rightarrow_G^* \gamma$

**定义 1.5** (生成的语言)
文法 $G$ 生成的语言 $L(G) = \{w \in \Sigma^* \mid S \Rightarrow_G^* w\}$

## 🛠️ Haskell实现

### 1. 基础数据结构

```haskell
-- 字母表
type Alphabet = [String]

-- 字符串
type String = [String]

-- 空字符串
epsilon :: String
epsilon = []

-- 语言
type Language = [String]

-- 上下文无关文法
data CFG = 
    CFG {
      nonterminals :: [String],      -- 非终结符集合 V
      terminals :: [String],         -- 终结符集合 Σ
      productions :: [Production],   -- 产生式集合 P
      startSymbol :: String          -- 开始符号 S
    }
  deriving (Show, Eq)

-- 产生式
data Production = 
    Production {
      left :: String,    -- 左部 A
      right :: [String]  -- 右部 α
    }
  deriving (Show, Eq)

-- 推导步骤
data DerivationStep = 
    DerivationStep {
      before :: [String],    -- 推导前
      after :: [String],     -- 推导后
      rule :: Production     -- 使用的产生式
    }
  deriving (Show, Eq)

-- 完整推导
type Derivation = [DerivationStep]
```

### 2. 语法操作

```haskell
-- 语法类型类
class Grammar a where
  -- 基本操作
  generate :: a -> [String]
  parse :: a -> String -> Bool
  derive :: a -> String -> [Derivation]
  
  -- 语法性质
  isAmbiguous :: a -> Bool
  isLeftRecursive :: a -> Bool
  isRightRecursive :: a -> Bool
  isChomskyNormalForm :: a -> Bool
  isGreibachNormalForm :: a -> Bool
  
  -- 语法分析
  leftmostDerivation :: a -> String -> [String]
  rightmostDerivation :: a -> String -> [String]
  allDerivations :: a -> String -> [Derivation]

-- 上下文无关文法实例
instance Grammar CFG where
  generate cfg = generateFrom cfg [startSymbol cfg]
  
  parse cfg input = 
    case parseWithGrammar cfg input of
      [] -> False
      _ -> True
  
  derive cfg input = 
    allDerivations cfg input
  
  isAmbiguous cfg = 
    any (\w -> length (allDerivations cfg w) > 1) (generate cfg)
  
  isLeftRecursive cfg = 
    any (\p -> head (right p) == left p) (productions cfg)
  
  isRightRecursive cfg = 
    any (\p -> last (right p) == left p) (productions cfg)
  
  isChomskyNormalForm cfg = 
    all isChomskyProduction (productions cfg)
  
  isGreibachNormalForm cfg = 
    all isGreibachProduction (productions cfg)
  
  leftmostDerivation cfg input = 
    leftmostDerive cfg [startSymbol cfg] input
  
  rightmostDerivation cfg input = 
    rightmostDerive cfg [startSymbol cfg] input
  
  allDerivations cfg input = 
    findAllDerivations cfg [startSymbol cfg] input

-- 从非终结符生成字符串
generateFrom :: CFG -> [String] -> [String]
generateFrom cfg symbols = 
  case symbols of
    [] -> [epsilon]
    (s:ss) -> 
      if s `elem` terminals cfg
        then [s] : generateFrom cfg ss
        else 
          let prods = findProductions cfg s
              generated = concatMap (\p -> generateFrom cfg (right p ++ ss)) prods
          in generated

-- 查找产生式
findProductions :: CFG -> String -> [Production]
findProductions cfg nt = 
  filter (\p -> left p == nt) (productions cfg)

-- 语法分析
parseWithGrammar :: CFG -> String -> [ParseTree]
parseWithGrammar cfg input = 
  parseTopDown cfg input

-- 所有解析
allParses :: CFG -> String -> [ParseTree]
allParses cfg input = parseTopDown cfg input

-- 检查Chomsky范式
isChomskyProduction :: Production -> Bool
isChomskyProduction prod = 
  case right prod of
    [] -> False  -- 不允许空产生式
    [t] -> t `elem` terminals  -- A → a
    [nt1, nt2] -> nt1 `elem` nonterminals && nt2 `elem` nonterminals  -- A → BC
    _ -> False

-- 检查Greibach范式
isGreibachProduction :: Production -> Bool
isGreibachProduction prod = 
  case right prod of
    [] -> False
    (t:ts) -> t `elem` terminals && all (`elem` nonterminals) ts
```

### 3. 推导算法

```haskell
-- 左most推导
leftmostDerive :: CFG -> [String] -> String -> [String]
leftmostDerive cfg current target = 
  if current == target
    then [current]
    else 
      case findLeftmostNonterminal current of
        Nothing -> []
        Just (nt, prefix, suffix) ->
          let prods = findProductions cfg nt
              derivations = concatMap (\p -> 
                leftmostDerive cfg (prefix ++ right p ++ suffix) target) prods
          in current : derivations

-- 右most推导
rightmostDerive :: CFG -> [String] -> String -> [String]
rightmostDerive cfg current target = 
  if current == target
    then [current]
    else 
      case findRightmostNonterminal current of
        Nothing -> []
        Just (nt, prefix, suffix) ->
          let prods = findProductions cfg nt
              derivations = concatMap (\p -> 
                rightmostDerive cfg (prefix ++ right p ++ suffix) target) prods
          in current : derivations

-- 查找最左非终结符
findLeftmostNonterminal :: [String] -> Maybe (String, [String], [String])
findLeftmostNonterminal symbols = 
  case findIndex (`elem` nonterminals) symbols of
    Nothing -> Nothing
    Just i -> Just (symbols !! i, take i symbols, drop (i + 1) symbols)

-- 查找最右非终结符
findRightmostNonterminal :: [String] -> Maybe (String, [String], [String])
findRightmostNonterminal symbols = 
  case findLastIndex (`elem` nonterminals) symbols of
    Nothing -> Nothing
    Just i -> Just (symbols !! i, take i symbols, drop (i + 1) symbols)

-- 查找最后一个满足条件的元素索引
findLastIndex :: (a -> Bool) -> [a] -> Maybe Int
findLastIndex p xs = 
  case findIndex p (reverse xs) of
    Nothing -> Nothing
    Just i -> Just (length xs - 1 - i)
```

### 4. 语法分析

```haskell
-- 解析树
data ParseTree = 
    ParseTree {
      symbol :: String,
      children :: [ParseTree],
      value :: Maybe String
    }
  deriving (Show, Eq)

-- 自顶向下解析
parseTopDown :: CFG -> String -> [ParseTree]
parseTopDown cfg input = 
  parseWithSymbol cfg (startSymbol cfg) input

-- 使用符号解析
parseWithSymbol :: CFG -> String -> String -> [ParseTree]
parseWithSymbol cfg sym input = 
  if sym `elem` terminals cfg
    then 
      if input == sym
        then [ParseTree sym [] (Just input)]
        else []
    else 
      let prods = findProductions cfg sym
          parses = concatMap (\p -> parseWithProduction cfg p input) prods
      in parses

-- 使用产生式解析
parseWithProduction :: CFG -> Production -> String -> [ParseTree]
parseWithProduction cfg prod input = 
  parseWithSymbols cfg (right prod) input

-- 使用符号序列解析
parseWithSymbols :: CFG -> [String] -> String -> [ParseTree]
parseWithSymbols cfg [] input = 
  if input == epsilon
    then [ParseTree "" [] Nothing]
    else []
parseWithSymbols cfg (sym:syms) input = 
  let parses = parseWithSymbol cfg sym input
      results = concatMap (\p -> 
        let remaining = drop (length (value p)) input
            restParses = parseWithSymbols cfg syms remaining
        in [ParseTree (left prod) [p] Nothing | rest <- restParses]) parses
  in results
```

## 📊 形式化证明

### 定理 1.2 (语法等价性)

**定理**：对于任意上下文无关文法 $G$，存在等价的Chomsky范式文法 $G'$。

**证明**：

1. 消除空产生式
2. 消除单位产生式
3. 消除无用符号
4. 转换为Chomsky范式

```haskell
-- 转换为Chomsky范式
toChomskyNormalForm :: CFG -> CFG
toChomskyNormalForm cfg = 
  let cfg1 = eliminateEpsilonProductions cfg
      cfg2 = eliminateUnitProductions cfg1
      cfg3 = eliminateUselessSymbols cfg2
      cfg4 = convertToChomskyForm cfg3
  in cfg4

-- 消除空产生式
eliminateEpsilonProductions :: CFG -> CFG
eliminateEpsilonProductions cfg = 
  let nullable = findNullableSymbols cfg
      newProds = generateNewProductions cfg nullable
  in cfg { productions = newProds }

-- 查找可空符号
findNullableSymbols :: CFG -> [String]
findNullableSymbols cfg = 
  let initial = [left p | p <- productions cfg, right p == []]
      closure = transitiveClosure cfg initial
  in closure

-- 传递闭包
transitiveClosure :: CFG -> [String] -> [String]
transitiveClosure cfg nullable = 
  let newNullable = findNewNullable cfg nullable
  in if newNullable == nullable
       then nullable
       else transitiveClosure cfg newNullable

-- 查找新的可空符号
findNewNullable :: CFG -> [String] -> [String]
findNewNullable cfg nullable = 
  let prods = productions cfg
      newNullable = [left p | p <- prods, 
                             all (`elem` nullable) (right p)]
  in nub (nullable ++ newNullable)
```

## 🎯 应用示例

### 示例 1：简单算术表达式文法

```haskell
-- 算术表达式文法
arithmeticGrammar :: CFG
arithmeticGrammar = 
  CFG {
    nonterminals = ["E", "T", "F"],
    terminals = ["+", "*", "(", ")", "id"],
    productions = [
      Production "E" ["E", "+", "T"],
      Production "E" ["T"],
      Production "T" ["T", "*", "F"],
      Production "T" ["F"],
      Production "F" ["(", "E", ")"],
      Production "F" ["id"]
    ],
    startSymbol = "E"
  }

-- 测试文法
testArithmeticGrammar :: IO ()
testArithmeticGrammar = do
  putStrLn "=== 算术表达式文法测试 ==="
  
  -- 生成测试
  let generated = take 5 (generate arithmeticGrammar)
  putStrLn "生成的表达式："
  mapM_ print generated
  
  -- 解析测试
  let testInput = ["id", "+", "id", "*", "id"]
  putStrLn $ "解析输入: " ++ show testInput
  let parses = parseWithGrammar arithmeticGrammar testInput
  putStrLn $ "解析结果数量: " ++ show (length parses)
  
  -- 歧义性检查
  putStrLn $ "文法是否歧义: " ++ show (isAmbiguous arithmeticGrammar)
```

### 示例 2：正则表达式文法

```haskell
-- 正则表达式文法
regexGrammar :: CFG
regexGrammar = 
  CFG {
    nonterminals = ["R", "C", "S"],
    terminals = ["a", "b", "|", "*", "(", ")", "ε"],
    productions = [
      Production "R" ["R", "|", "C"],
      Production "R" ["C"],
      Production "C" ["C", "S"],
      Production "C" ["S"],
      Production "S" ["S", "*"],
      Production "S" ["P"],
      Production "P" ["(", "R", ")"],
      Production "P" ["a"],
      Production "P" ["b"],
      Production "P" ["ε"]
    ],
    startSymbol = "R"
  }

-- 正则表达式解析器
parseRegex :: String -> Maybe ParseTree
parseRegex input = 
  case parseWithGrammar regexGrammar (words input) of
    [] -> Nothing
    (tree:_) -> Just tree
```

## 🔗 相关链接

- [02-Parsing-Theory](./02-Parsing-Theory.md) - 语法分析理论
- [03-Syntax-Analysis](./03-Syntax-Analysis.md) - 语法分析算法
- [02-Semantics-Theory](../02-Semantics-Theory/README.md) - 语义理论
- [03-Type-System-Theory](../03-Type-System-Theory/README.md) - 类型系统理论

## 📚 参考文献

1. Hopcroft, J. E., & Ullman, J. D. (1979). Introduction to Automata Theory, Languages, and Computation.
2. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.
3. Grune, D., & Jacobs, C. J. (2008). Parsing Techniques: A Practical Guide.

---

*本文档是形式化知识体系理论层的一部分，提供了形式语法理论的完整数学定义和Haskell实现。*
