# 010. 上下文无关文法 (Context-Free Grammars)

## 1. 概述

上下文无关文法(CFG)是形式语言理论中的核心概念，对应乔姆斯基层次结构中的2型语言。CFG能够描述嵌套结构，是编程语言语法分析、自然语言处理的理论基础。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[011-Turing-Machines]] - 图灵机理论
- [[012-Computability-Theory]] - 可计算性理论
- [[005-Denotational-Semantics]] - 指称语义

## 2. 数学基础

### 2.1 上下文无关文法定义

**定义 2.1.1** (上下文无关文法)
上下文无关文法是一个四元组 $G = (V, \Sigma, P, S)$，其中：

- $V$ 是非终结符集合
- $\Sigma$ 是终结符集合，$V \cap \Sigma = \emptyset$
- $P \subseteq V \times (V \cup \Sigma)^*$ 是产生式集合
- $S \in V$ 是开始符号

**定义 2.1.2** (推导关系)
对于文法 $G$，定义推导关系 $\Rightarrow_G$：

如果 $A \to \alpha \in P$，则对于任意 $\beta, \gamma \in (V \cup \Sigma)^*$，有：
$$\beta A \gamma \Rightarrow_G \beta \alpha \gamma$$

**定义 2.1.3** (推导闭包)
推导的传递闭包 $\Rightarrow_G^*$ 定义为：

1. $\alpha \Rightarrow_G^* \alpha$ (自反性)
2. 如果 $\alpha \Rightarrow_G \beta$ 且 $\beta \Rightarrow_G^* \gamma$，则 $\alpha \Rightarrow_G^* \gamma$ (传递性)

**定义 2.1.4** (生成的语言)
文法 $G$ 生成的语言定义为：
$$L(G) = \{w \in \Sigma^* \mid S \Rightarrow_G^* w\}$$

### 2.2 文法分类

**定义 2.2.1** (Chomsky范式)
文法 $G$ 是Chomsky范式，如果所有产生式都是以下形式之一：
- $A \to BC$ (两个非终结符)
- $A \to a$ (单个终结符)
- $S \to \varepsilon$ (仅当 $\varepsilon \in L(G)$)

**定理 2.2.1** (Chomsky范式转换)
对于任意上下文无关文法 $G$，存在等价的Chomsky范式文法 $G'$。

**证明**:
1. 消除 $\varepsilon$-产生式
2. 消除单位产生式
3. 消除无用符号
4. 转换为Chomsky范式

**定义 2.2.2** (Greibach范式)
文法 $G$ 是Greibach范式，如果所有产生式都是形式 $A \to a\alpha$，其中 $a \in \Sigma$，$\alpha \in V^*$。

**定理 2.2.2** (Greibach范式转换)
对于任意上下文无关文法 $G$，存在等价的Greibach范式文法 $G'$。

## 3. 下推自动机理论

### 3.1 非确定性下推自动机 (NPDA)

**定义 3.1.1** (NPDA)
非确定性下推自动机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限栈字母表
- $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \to 2^{Q \times \Gamma^*}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集

**定义 3.1.2** (瞬时描述)
NPDA 的瞬时描述是一个三元组 $(q, w, \gamma)$，其中：
- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\gamma \in \Gamma^*$ 是栈内容

**定义 3.1.3** (转移关系)
瞬时描述间的转移关系 $\vdash_M$ 定义为：

如果 $(q', \beta) \in \delta(q, a, A)$，则：
$$(q, aw, A\gamma) \vdash_M (q', w, \beta\gamma)$$

**定义 3.1.4** (语言接受)
NPDA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid (q_0, w, Z_0) \vdash_M^* (q, \varepsilon, \gamma), q \in F\}$$

### 3.2 确定性下推自动机 (DPDA)

**定义 3.2.1** (DPDA)
确定性下推自动机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\Gamma$ 是有限栈字母表
- $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \to (Q \times \Gamma^*) \cup \{\emptyset\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集

**定理 3.2.1** (CFG与NPDA等价)
语言 $L$ 是上下文无关语言当且仅当存在NPDA $M$ 使得 $L = L(M)$。

**证明**:
- **必要性**: 通过标准构造法将CFG转换为NPDA
- **充分性**: 通过动态规划将NPDA转换为CFG

## 4. Haskell 实现

### 4.1 上下文无关文法数据类型

```haskell
-- | 上下文无关文法
data CFG v t = CFG
  { nonTerminals :: Set v    -- 非终结符集合 V
  , terminals    :: Set t    -- 终结符集合 Σ
  , productions  :: Set (Production v t)  -- 产生式集合 P
  , startSymbol  :: v        -- 开始符号 S
  }

-- | 产生式
data Production v t = Production
  { leftSide  :: v           -- 左部 (单个非终结符)
  , rightSide :: [Symbol v t] -- 右部 (符号序列)
  } deriving (Show, Eq, Ord)

-- | 符号 (终结符或非终结符)
data Symbol v t
  = Terminal t
  | NonTerminal v
  deriving (Show, Eq, Ord)

-- | 推导步骤
data DerivationStep v t = DerivationStep
  { before :: [Symbol v t]   -- 推导前
  , after  :: [Symbol v t]   -- 推导后
  , rule   :: Production v t -- 使用的产生式
  , position :: Int          -- 应用位置
  }

-- | 完整推导
type Derivation v t = [DerivationStep v t]

-- | 文法示例：算术表达式
arithmeticGrammar :: CFG String String
arithmeticGrammar = CFG
  { nonTerminals = fromList ["E", "T", "F"]
  , terminals = fromList ["+", "*", "(", ")", "id"]
  , productions = fromList
      [ Production "E" [NonTerminal "E", Terminal "+", NonTerminal "T"]
      , Production "E" [NonTerminal "T"]
      , Production "T" [NonTerminal "T", Terminal "*", NonTerminal "F"]
      , Production "T" [NonTerminal "F"]
      , Production "F" [Terminal "(", NonTerminal "E", Terminal ")"]
      , Production "F" [Terminal "id"]
      ]
  , startSymbol = "E"
  }
```

### 4.2 推导算法

```haskell
-- | 单步推导
deriveStep :: (Ord v, Ord t) => CFG v t -> [Symbol v t] -> [DerivationStep v t]
deriveStep cfg sentential = concatMap (applyProduction cfg sentential) (toList (productions cfg))
  where
    applyProduction cfg sentential prod = 
      [DerivationStep before after prod pos | 
       (pos, before) <- findMatches (leftSide prod) sentential,
       let after = replaceAt pos (rightSide prod) sentential]

-- | 查找匹配位置
findMatches :: (Ord v, Ord t) => v -> [Symbol v t] -> [(Int, [Symbol v t])]
findMatches nt sentential = 
  [(i, take i sentential ++ [NonTerminal nt] ++ drop (i+1) sentential) |
   i <- [0..length sentential - 1],
   case sentential !! i of
     NonTerminal nt' -> nt == nt'
     Terminal _ -> False]

-- | 替换指定位置的符号
replaceAt :: Int -> [Symbol v t] -> [Symbol v t] -> [Symbol v t]
replaceAt pos replacement sentential = 
  take pos sentential ++ replacement ++ drop (pos + 1) sentential

-- | 检查是否为句子形式
isSententialForm :: (Ord v, Ord t) => CFG v t -> [Symbol v t] -> Bool
isSententialForm cfg symbols = all isValidSymbol symbols
  where
    isValidSymbol (Terminal t) = t `member` terminals cfg
    isValidSymbol (NonTerminal v) = v `member` nonTerminals cfg

-- | 生成所有可能的推导
allDerivations :: (Ord v, Ord t) => CFG v t -> Int -> [[Symbol v t]]
allDerivations cfg maxSteps = iterate deriveAll [[NonTerminal (startSymbol cfg)]] !! maxSteps
  where
    deriveAll sententials = concatMap (deriveOneStep cfg) sententials
    deriveOneStep cfg sentential = 
      [after | DerivationStep _ after _ _ <- deriveStep cfg sentential]

-- | 检查字符串是否属于语言
isInLanguage :: (Ord v, Ord t, Eq t) => CFG v t -> [t] -> Bool
isInLanguage cfg input = any (== map Terminal input) (allDerivations cfg (length input * 2))
```

### 4.3 下推自动机实现

```haskell
-- | 下推自动机
data PDA q t g = PDA
  { pdaStates :: Set q
  , pdaAlphabet :: Set t
  , pdaStackAlphabet :: Set g
  , pdaTransition :: q -> Maybe t -> g -> Set (q, [g])
  , pdaStartState :: q
  , pdaStartStack :: g
  , pdaAcceptStates :: Set q
  }

-- | 瞬时描述
data Configuration q t g = Configuration
  { confState :: q
  , confInput :: [t]
  , confStack :: [g]
  } deriving (Show, Eq, Ord)

-- | PDA 执行
executePDA :: (Ord q, Ord t, Ord g) => PDA q t g -> [t] -> Bool
executePDA pda input = any (\conf -> confState conf `member` pdaAcceptStates pda) 
                         (reachableConfigurations pda input)
  where
    reachableConfigurations pda input = 
      closure (singleton (Configuration (pdaStartState pda) input [pdaStartStack pda]))
    
    closure configs = 
      let newConfigs = unions [step pda conf | conf <- toList configs]
          allConfigs = configs `union` newConfigs
      in if newConfigs `isSubsetOf` configs 
         then configs 
         else closure allConfigs

-- | 单步转移
step :: (Ord q, Ord t, Ord g) => PDA q t g -> Configuration q t g -> Set (Configuration q t g)
step pda (Configuration q input stack) = 
  case (input, stack) of
    ([], []) -> empty
    (a:as, s:ss) -> 
      let transitions = pdaTransition pda (Just a) s
      in fromList [Configuration q' as (newStack ++ ss) | 
                   (q', newStack) <- toList transitions]
    (_, []) -> empty
    ([], s:ss) -> 
      let transitions = pdaTransition pda Nothing s
      in fromList [Configuration q' [] (newStack ++ ss) | 
                   (q', newStack) <- toList transitions]

-- | CFG 到 PDA 的转换
cfgToPDA :: (Ord v, Ord t) => CFG v t -> PDA (Either String v) t (Either String v)
cfgToPDA cfg = PDA
  { pdaStates = fromList [Left "q0", Left "q1", Left "q2"]
  , pdaAlphabet = terminals cfg
  , pdaStackAlphabet = fromList (map Right (toList (nonTerminals cfg)) ++ 
                                 map Left (toList (terminals cfg)))
  , pdaTransition = \q a s -> case (q, a, s) of
      (Left "q0", Nothing, Right nt) -> 
        fromList [(Left "q1", [Right nt, Left "Z"]) | 
                  Production nt' rhs <- toList (productions cfg), nt' == nt]
      (Left "q1", Just t, Left t') | t == t' -> 
        singleton (Left "q1", [])
      (Left "q1", Nothing, Right nt) -> 
        fromList [(Left "q1", map symbolToStack (rightSide prod)) | 
                  prod <- toList (productions cfg), leftSide prod == nt]
      (Left "q1", Nothing, Left "Z") -> 
        singleton (Left "q2", [])
      _ -> empty
  , pdaStartState = Left "q0"
  , pdaStartStack = Right (startSymbol cfg)
  , pdaAcceptStates = singleton (Left "q2")
  }
  where
    symbolToStack (Terminal t) = Left t
    symbolToStack (NonTerminal v) = Right v
```

### 4.4 语法分析器

```haskell
-- | 语法树节点
data ParseTree v t
  = Leaf t
  | Node v [ParseTree v t]
  deriving (Show, Eq)

-- | 递归下降分析器
class RecursiveDescent v t where
  parse :: CFG v t -> [t] -> Maybe (ParseTree v t)

-- | 算术表达式分析器实例
instance RecursiveDescent String String where
  parse cfg input = parseE cfg input
    where
      parseE cfg input = 
        case parseT cfg input of
          Just (tree, rest) -> 
            case rest of
              "+":rest' -> 
                case parseE cfg rest' of
                  Just (tree', rest'') -> Just (Node "E" [tree, Node "+" [], tree'], rest'')
                  Nothing -> Just (tree, rest)
              _ -> Just (tree, rest)
          Nothing -> Nothing

      parseT cfg input = 
        case parseF cfg input of
          Just (tree, rest) -> 
            case rest of
              "*":rest' -> 
                case parseT cfg rest' of
                  Just (tree', rest'') -> Just (Node "T" [tree, Node "*" [], tree'], rest'')
                  Nothing -> Just (tree, rest)
              _ -> Just (tree, rest)
          Nothing -> Nothing

      parseF cfg input = 
        case input of
          "(":rest -> 
            case parseE cfg rest of
              Just (tree, ")":rest') -> Just (Node "F" [Node "(" [], tree, Node ")" []], rest')
              _ -> Nothing
          "id":rest -> Just (Node "F" [Leaf "id"], rest)
          _ -> Nothing
```

## 5. 应用实例

### 5.1 编程语言语法

```haskell
-- | 简单编程语言语法
simpleLanguageGrammar :: CFG String String
simpleLanguageGrammar = CFG
  { nonTerminals = fromList ["Program", "Statement", "Expression", "Term", "Factor"]
  , terminals = fromList ["if", "then", "else", "while", "do", "=", "+", "*", "(", ")", "id", "num"]
  , productions = fromList
      [ Production "Program" [NonTerminal "Statement"]
      , Production "Statement" [Terminal "if", NonTerminal "Expression", Terminal "then", NonTerminal "Statement", Terminal "else", NonTerminal "Statement"]
      , Production "Statement" [Terminal "while", NonTerminal "Expression", Terminal "do", NonTerminal "Statement"]
      , Production "Statement" [Terminal "id", Terminal "=", NonTerminal "Expression"]
      , Production "Expression" [NonTerminal "Expression", Terminal "+", NonTerminal "Term"]
      , Production "Expression" [NonTerminal "Term"]
      , Production "Term" [NonTerminal "Term", Terminal "*", NonTerminal "Factor"]
      , Production "Term" [NonTerminal "Factor"]
      , Production "Factor" [Terminal "(", NonTerminal "Expression", Terminal ")"]
      , Production "Factor" [Terminal "id"]
      , Production "Factor" [Terminal "num"]
      ]
  , startSymbol = "Program"
  }

-- | 语法检查器
syntaxChecker :: [String] -> Bool
syntaxChecker tokens = isInLanguage simpleLanguageGrammar tokens
```

### 5.2 自然语言处理

```haskell
-- | 简单英语语法
englishGrammar :: CFG String String
englishGrammar = CFG
  { nonTerminals = fromList ["S", "NP", "VP", "Det", "N", "V"]
  , terminals = fromList ["the", "a", "cat", "dog", "runs", "sleeps"]
  , productions = fromList
      [ Production "S" [NonTerminal "NP", NonTerminal "VP"]
      , Production "NP" [NonTerminal "Det", NonTerminal "N"]
      , Production "VP" [NonTerminal "V"]
      , Production "Det" [Terminal "the"]
      , Production "Det" [Terminal "a"]
      , Production "N" [Terminal "cat"]
      , Production "N" [Terminal "dog"]
      , Production "V" [Terminal "runs"]
      , Production "V" [Terminal "sleeps"]
      ]
  , startSymbol = "S"
  }

-- | 句子分析
analyzeSentence :: [String] -> Maybe (ParseTree String String)
analyzeSentence words = parse englishGrammar words
```

## 6. 理论性质

### 6.1 泵引理

**定理 6.1.1** (上下文无关语言泵引理)
如果 $L$ 是上下文无关语言，则存在常数 $p > 0$，使得对于任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = uvxyz$ 满足：

1. $|vxy| \leq p$
2. $|vy| > 0$
3. 对于所有 $i \geq 0$，$uv^ixy^iz \in L$

**证明**: 设 $G$ 是生成 $L$ 的Chomsky范式文法，选择 $p = 2^{|V|}$。对于长度 $\geq p$ 的字符串，根据鸽巢原理，存在非终结符重复，可以泵入重复部分。

**应用**: 证明语言非上下文无关性
- $L = \{a^nb^nc^n \mid n \geq 0\}$ 不是上下文无关语言
- $L = \{ww \mid w \in \{a,b\}^*\}$ 不是上下文无关语言

### 6.2 歧义性

**定义 6.2.1** (歧义文法)
文法 $G$ 是歧义的，如果存在字符串 $w \in L(G)$ 有多个不同的最左推导。

**定义 6.2.2** (固有歧义语言)
语言 $L$ 是固有歧义的，如果所有生成 $L$ 的文法都是歧义的。

**定理 6.2.1** (歧义性不可判定)
给定上下文无关文法 $G$，判断 $G$ 是否歧义是不可判定的。

```haskell
-- | 歧义性检测 (简化版本)
isAmbiguous :: (Ord v, Ord t) => CFG v t -> Int -> Bool
isAmbiguous cfg maxLength = 
  any (\w -> length (allParses cfg w) > 1) 
      (allStrings cfg maxLength)
  where
    allStrings cfg maxLen = 
      concatMap (\n -> generateStrings cfg n) [1..maxLen]
    
    generateStrings cfg n = 
      filter (\s -> isInLanguage cfg s) 
             (sequence (replicate n (toList (terminals cfg))))
    
    allParses cfg input = 
      filter (\tree -> yield tree == input) 
             (allParseTrees cfg (length input * 2))
    
    yield (Leaf t) = [t]
    yield (Node _ children) = concatMap yield children
```

## 7. 复杂度分析

### 7.1 时间复杂度

- **CYK算法**: $O(n^3 \cdot |G|)$，其中 $n$ 是输入长度，$|G|$ 是文法大小
- **Earley算法**: $O(n^3)$ 最坏情况，$O(n^2)$ 平均情况
- **递归下降**: $O(n)$ 对于LL(1)文法
- **LR分析**: $O(n)$ 对于LR文法

### 7.2 空间复杂度

- **CYK算法**: $O(n^2)$
- **Earley算法**: $O(n^2)$
- **递归下降**: $O(n)$ (递归栈深度)
- **LR分析**: $O(n)$

## 8. 扩展与变体

### 8.1 属性文法

```haskell
-- | 属性文法
data AttributeGrammar v t a = AttributeGrammar
  { baseGrammar :: CFG v t
  , attributes :: Map v (Set a)  -- 每个非终结符的属性集
  , semanticRules :: Map (Production v t) [SemanticRule v t a]
  }

-- | 语义规则
data SemanticRule v t a = SemanticRule
  { target :: (v, a)  -- 目标属性
  , sources :: [(v, a)]  -- 源属性
  , computation :: [a] -> a  -- 计算函数
  }

-- | 属性计算
computeAttributes :: (Ord v, Ord t, Ord a) => 
                     AttributeGrammar v t a -> 
                     ParseTree v t -> 
                     Map (v, a) a
computeAttributes ag tree = 
  foldl applyRules initialValues (semanticRules ag)
  where
    initialValues = Map.empty
    applyRules values rule = 
      let sourceValues = map (\src -> values Map.! src) (sources rule)
          result = computation rule sourceValues
      in Map.insert (target rule) result values
```

### 8.2 概率上下文无关文法

```haskell
-- | 概率上下文无关文法
data PCFG v t = PCFG
  { pcfgGrammar :: CFG v t
  , pcfgProbabilities :: Map (Production v t) Double
  }

-- | 计算句子概率
sentenceProbability :: (Ord v, Ord t) => PCFG v t -> [t] -> Double
sentenceProbability pcfg sentence = 
  sum [parseProbability pcfg tree | 
       tree <- allParseTrees (pcfgGrammar pcfg) (length sentence * 2),
       yield tree == sentence]
  where
    parseProbability pcfg (Leaf _) = 1.0
    parseProbability pcfg (Node nt children) = 
      let prod = findProduction nt children
          prodProb = pcfgProbabilities pcfg Map.! prod
          childrenProb = product (map (parseProbability pcfg) children)
      in prodProb * childrenProb
    
    findProduction nt children = 
      head [prod | prod <- toList (productions (pcfgGrammar pcfg)),
                   leftSide prod == nt,
                   rightSide prod == map rootSymbol children]
    
    rootSymbol (Leaf t) = Terminal t
    rootSymbol (Node v _) = NonTerminal v
```

## 9. 总结

上下文无关文法理论为形式语言提供了强大的描述能力，具有以下特点：

1. **嵌套结构**: 能够描述括号匹配、表达式等嵌套结构
2. **语法分析**: 为编程语言和自然语言提供语法分析基础
3. **自动机对应**: 与下推自动机等价，提供计算模型
4. **歧义性**: 存在歧义性问题，需要特殊处理
5. **扩展性**: 支持属性文法、概率文法等扩展

上下文无关文法在编译器设计、自然语言处理、形式语言理论等领域有广泛应用。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[011-Turing-Machines]] - 图灵机理论
- [[012-Computability-Theory]] - 可计算性理论 