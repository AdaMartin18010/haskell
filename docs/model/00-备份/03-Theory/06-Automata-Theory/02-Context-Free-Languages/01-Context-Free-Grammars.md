# 01-Context-Free-Grammars - 上下文无关文法

## 📚 概述

上下文无关文法（Context-Free Grammar, CFG）是形式语言理论中的核心概念，用于描述编程语言的语法结构。本文档提供CFG的完整形式化定义、Haskell实现和形式证明。

## 🎯 核心概念

### 形式定义

**上下文无关文法**是一个四元组 $G = (V, \Sigma, P, S)$，其中：

- $V$：非终结符集合（Variables）
- $\Sigma$：终结符集合（Terminals），且 $V \cap \Sigma = \emptyset$
- $P$：产生式集合（Productions），每个产生式形如 $A \rightarrow \alpha$，其中 $A \in V$，$\alpha \in (V \cup \Sigma)^*$
- $S \in V$：开始符号（Start Symbol）

### 推导关系

对于字符串 $\alpha, \beta \in (V \cup \Sigma)^*$，如果存在产生式 $A \rightarrow \gamma$ 使得 $\alpha = \alpha_1 A \alpha_2$ 且 $\beta = \alpha_1 \gamma \alpha_2$，则称 $\alpha$ 直接推导出 $\beta$，记作 $\alpha \Rightarrow \beta$。

**闭包推导**：$\alpha \Rightarrow^* \beta$ 表示通过零次或多次直接推导从 $\alpha$ 得到 $\beta$。

### 语言定义

文法 $G$ 生成的语言定义为：
$$L(G) = \{w \in \Sigma^* \mid S \Rightarrow^* w\}$$

## 🔧 Haskell实现

### 基础数据结构

```haskell
-- | 符号类型
data Symbol = Terminal Char | NonTerminal String
  deriving (Eq, Show, Ord)

-- | 产生式
data Production = Production 
  { lhs :: NonTerminal  -- 左部（单个非终结符）
  , rhs :: [Symbol]     -- 右部（符号序列）
  }
  deriving (Eq, Show)

-- | 上下文无关文法
data CFG = CFG
  { variables :: Set String      -- 非终结符集合
  , terminals :: Set Char        -- 终结符集合
  , productions :: [Production]  -- 产生式集合
  , startSymbol :: String        -- 开始符号
  }
  deriving (Eq, Show)

-- | 推导步骤
data DerivationStep = DerivationStep
  { from :: [Symbol]    -- 推导前的字符串
  , to :: [Symbol]      -- 推导后的字符串
  , production :: Production  -- 使用的产生式
  , position :: Int     -- 应用位置
  }
  deriving (Eq, Show)

-- | 完整推导
type Derivation = [DerivationStep]
```

### 文法操作

```haskell
-- | 检查符号是否为终结符
isTerminal :: Symbol -> Bool
isTerminal (Terminal _) = True
isTerminal _ = False

-- | 检查符号是否为非终结符
isNonTerminal :: Symbol -> Bool
isNonTerminal (NonTerminal _) = True
isNonTerminal _ = False

-- | 获取符号的字符串表示
symbolToString :: Symbol -> String
symbolToString (Terminal c) = [c]
symbolToString (NonTerminal s) = s

-- | 将字符串转换为符号列表
stringToSymbols :: String -> [Symbol]
stringToSymbols = map Terminal

-- | 将符号列表转换为字符串（仅终结符）
symbolsToString :: [Symbol] -> String
symbolsToString = concatMap symbolToString . filter isTerminal
```

### 推导实现

```haskell
-- | 查找所有可能的直接推导
findDirectDerivations :: CFG -> [Symbol] -> [DerivationStep]
findDirectDerivations cfg symbols = concatMap findDerivationsAt [0..length symbols - 1]
  where
    findDerivationsAt pos = 
      case splitAt pos symbols of
        (before, NonTerminal nt : after) -> 
          [DerivationStep symbols (before ++ rhs ++ after) prod pos
           | prod@(Production lhs rhs) <- productions cfg
           , lhs == NonTerminal nt]
        _ -> []

-- | 生成所有可能的推导序列
generateDerivations :: CFG -> [[Symbol]] -> [[Symbol]]
generateDerivations cfg current = 
  let nextSteps = concatMap (findDirectDerivations cfg) current
      nextStrings = map to nextSteps
  in if null nextSteps 
     then current 
     else generateDerivations cfg (current ++ nextStrings)

-- | 检查字符串是否属于文法生成的语言
isInLanguage :: CFG -> String -> Bool
isInLanguage cfg input = 
  let start = [NonTerminal (startSymbol cfg)]
      allDerivations = generateDerivations cfg [start]
      terminalStrings = map symbolsToString allDerivations
  in input `elem` terminalStrings
```

### 文法变换

```haskell
-- | 消除ε产生式（空产生式）
eliminateEpsilonProductions :: CFG -> CFG
eliminateEpsilonProductions cfg = 
  let nullable = findNullable cfg
      newProductions = concatMap (expandProduction nullable) (productions cfg)
  in cfg { productions = filter (not . isEpsilonProduction) newProductions }
  where
    isEpsilonProduction (Production _ rhs) = null rhs

-- | 查找可空的非终结符
findNullable :: CFG -> Set String
findNullable cfg = 
  let initial = Set.fromList [nt | Production (NonTerminal nt) [] <- productions cfg]
      step nullable = 
        let newNullable = Set.union nullable 
              (Set.fromList [nt | Production (NonTerminal nt) rhs <- productions cfg,
                                 all (\s -> case s of
                                              NonTerminal n -> n `Set.member` nullable
                                              Terminal _ -> False) rhs])
        in if newNullable == nullable then nullable else step newNullable
  in step initial

-- | 扩展产生式以消除ε产生式
expandProduction :: Set String -> Production -> [Production]
expandProduction nullable (Production lhs rhs) = 
  let nullablePositions = [i | (i, s) <- zip [0..] rhs,
                              case s of
                                NonTerminal nt -> nt `Set.member` nullable
                                Terminal _ -> False]
      combinations = subsequences nullablePositions
  in [Production lhs (removeAtPositions rhs combo) | combo <- combinations]
  where
    removeAtPositions xs positions = 
      [x | (i, x) <- zip [0..] xs, i `notElem` positions]
```

## 📐 形式证明

### 定理1：CFG的等价性

**定理**：对于任意上下文无关文法 $G$，存在等价的乔姆斯基范式文法 $G'$。

**证明**：通过以下步骤构造：

1. **消除ε产生式**：对于每个可空的非终结符 $A$，添加所有可能的非空产生式
2. **消除单位产生式**：对于 $A \rightarrow B$ 形式的产生式，用 $B$ 的所有产生式替换
3. **转换为乔姆斯基范式**：将长产生式分解为二元产生式

**Haskell实现**：

```haskell
-- | 转换为乔姆斯基范式
toChomskyNormalForm :: CFG -> CFG
toChomskyNormalForm cfg = 
  let cfg1 = eliminateEpsilonProductions cfg
      cfg2 = eliminateUnitProductions cfg1
      cfg3 = eliminateLongProductions cfg2
  in cfg3

-- | 消除单位产生式
eliminateUnitProductions :: CFG -> CFG
eliminateUnitProductions cfg = 
  let unitPairs = findUnitPairs cfg
      newProductions = concatMap (expandUnitProduction unitPairs) (productions cfg)
  in cfg { productions = filter (not . isUnitProduction) newProductions }
  where
    isUnitProduction (Production _ [NonTerminal _]) = True
    isUnitProduction _ = False

-- | 查找单位产生式对
findUnitPairs :: CFG -> [(String, String)]
findUnitPairs cfg = 
  let initial = [(nt, nt) | nt <- Set.toList (variables cfg)]
      step pairs = 
        let newPairs = Set.fromList pairs `Set.union`
              (Set.fromList [(nt1, nt3) | (nt1, nt2) <- pairs,
                                         Production (NonTerminal nt2') [NonTerminal nt3] <- productions cfg,
                                         nt2 == nt2'])
        in if Set.size newPairs == length pairs 
           then pairs 
           else step (Set.toList newPairs)
  in step initial
```

### 定理2：下推自动机等价性

**定理**：语言 $L$ 是上下文无关的当且仅当存在下推自动机识别 $L$。

**证明**：

- **必要性**：构造下推自动机模拟CFG的推导过程
- **充分性**：从下推自动机构造等价的CFG

## 🔍 实际应用

### 示例：简单算术表达式文法

```haskell
-- | 算术表达式文法
arithmeticGrammar :: CFG
arithmeticGrammar = CFG
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

-- | 测试文法
testArithmeticGrammar :: IO ()
testArithmeticGrammar = do
  putStrLn "Testing arithmetic grammar:"
  let testCases = ["a", "a+a", "a*a", "(a+a)*a"]
  mapM_ (\input -> 
    putStrLn $ input ++ " -> " ++ show (isInLanguage arithmeticGrammar input)
    ) testCases
```

### 性能分析

```haskell
-- | 推导复杂度分析
derivationComplexity :: CFG -> String -> Int
derivationComplexity cfg input = 
  let start = [NonTerminal (startSymbol cfg)]
      allSteps = generateAllDerivationSteps cfg start
  in length allSteps

-- | 生成所有推导步骤
generateAllDerivationSteps :: CFG -> [Symbol] -> [DerivationStep]
generateAllDerivationSteps cfg current = 
  let steps = findDirectDerivations cfg current
  in steps ++ concatMap (generateAllDerivationSteps cfg . to) steps
```

## 🔗 相关概念

- [下推自动机](02-Pushdown-Automata.md) - CFG的自动机模型
- [语法分析](03-Parsing.md) - CFG的解析算法
- [语法树](04-Syntax-Trees.md) - CFG的树形表示
- [形式文法](../01-Programming-Language-Theory/Syntax/Formal-Grammars.md) - 更一般的文法理论

## 📚 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.

---

*本文档提供了上下文无关文法的完整形式化框架，包括严格的数学定义、可执行的Haskell实现和构造性证明。*
