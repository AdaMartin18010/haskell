# 01-Language-Hierarchy - 语言层次

## 📚 概述

语言层次是形式语言理论的核心概念，描述了不同语言类之间的包含关系。乔姆斯基层次是最著名的语言层次分类，将语言按照复杂性和表达能力进行分层。本文档提供语言层次的完整形式化定义、Haskell实现和形式证明。

## 🎯 核心概念

### 乔姆斯基层次

**乔姆斯基层次**（Chomsky Hierarchy）将形式语言分为四个层次：

1. **类型0**：递归可枚举语言（Recursively Enumerable Languages）
2. **类型1**：上下文相关语言（Context-Sensitive Languages）
3. **类型2**：上下文无关语言（Context-Free Languages）
4. **类型3**：正则语言（Regular Languages）

### 层次包含关系

**严格包含关系**：
$$\text{Regular} \subset \text{Context-Free} \subset \text{Context-Sensitive} \subset \text{Recursively-Enumerable}$$

### 语言类定义

#### 正则语言（Type 3）

**定义**：语言 $L$ 是正则的，当且仅当存在正则表达式 $R$ 使得 $L = L(R)$。

**等价定义**：

- 被有限自动机识别
- 被右线性文法生成
- 被左线性文法生成

#### 上下文无关语言（Type 2）

**定义**：语言 $L$ 是上下文无关的，当且仅当存在上下文无关文法 $G$ 使得 $L = L(G)$。

**等价定义**：

- 被下推自动机识别
- 被乔姆斯基范式文法生成

#### 上下文相关语言（Type 1）

**定义**：语言 $L$ 是上下文相关的，当且仅当存在上下文相关文法 $G$ 使得 $L = L(G)$。

**等价定义**：

- 被线性有界自动机识别
- 产生式形如 $\alpha A \beta \rightarrow \alpha \gamma \beta$，其中 $|\gamma| \geq 1$

#### 递归可枚举语言（Type 0）

**定义**：语言 $L$ 是递归可枚举的，当且仅当存在图灵机 $M$ 使得 $L = L(M)$。

**等价定义**：

- 被图灵机识别
- 被无限制文法生成

## 🔧 Haskell实现

### 基础数据结构

```haskell
-- | 语言类型
data LanguageType = 
    Regular
  | ContextFree
  | ContextSensitive
  | RecursivelyEnumerable
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | 语言类
data LanguageClass = LanguageClass
  { languageType :: LanguageType
  , alphabet :: Set Char
  , strings :: Set String
  , description :: String
  }
  deriving (Eq, Show)

-- | 层次关系
data HierarchyRelation = HierarchyRelation
  { fromType :: LanguageType
  , toType :: LanguageType
  , isStrict :: Bool
  , proof :: String
  }
  deriving (Eq, Show)

-- | 语言层次
data LanguageHierarchy = LanguageHierarchy
  { levels :: [LanguageType]
  , relations :: [HierarchyRelation]
  , examples :: Map LanguageType [String]
  }
  deriving (Show)
```

### 层次关系实现

```haskell
-- | 创建乔姆斯基层次
chomskyHierarchy :: LanguageHierarchy
chomskyHierarchy = LanguageHierarchy
  { levels = [Regular, ContextFree, ContextSensitive, RecursivelyEnumerable]
  , relations = 
    [ HierarchyRelation Regular ContextFree True "Regular languages are properly contained in CFL"
    , HierarchyRelation ContextFree ContextSensitive True "CFL are properly contained in CSL"
    , HierarchyRelation ContextSensitive RecursivelyEnumerable True "CSL are properly contained in REL"
    ]
  , examples = Map.fromList
    [ (Regular, ["a*", "a+b", "(ab)*"])
    , (ContextFree, ["a^n b^n", "palindromes", "balanced parentheses"])
    , (ContextSensitive, ["a^n b^n c^n", "a^n b^n c^n d^n"])
    , (RecursivelyEnumerable, ["halting problem", "diagonal language"])
    ]
  }

-- | 检查包含关系
isContainedIn :: LanguageType -> LanguageType -> Bool
isContainedIn from to = 
  let fromIndex = fromEnum from
      toIndex = fromEnum to
  in fromIndex <= toIndex

-- | 检查严格包含关系
isStrictlyContainedIn :: LanguageType -> LanguageType -> Bool
isStrictlyContainedIn from to = 
  let fromIndex = fromEnum from
      toIndex = fromEnum to
  in fromIndex < toIndex

-- | 获取包含关系
getContainmentRelation :: LanguageType -> LanguageType -> Maybe HierarchyRelation
getContainmentRelation from to = 
  let hierarchy = chomskyHierarchy
      relations = filter (\r -> fromType r == from && toType r == to) (relations hierarchy)
  in case relations of
       [] -> Nothing
       (r:_) -> Just r
```

### 语言类操作

```haskell
-- | 创建正则语言
createRegularLanguage :: Set Char -> [String] -> LanguageClass
createRegularLanguage alphabet strings = LanguageClass
  { languageType = Regular
  , alphabet = alphabet
  , strings = Set.fromList strings
  , description = "Regular language defined by finite automaton or regular expression"
  }

-- | 创建上下文无关语言
createContextFreeLanguage :: Set Char -> [String] -> LanguageClass
createContextFreeLanguage alphabet strings = LanguageClass
  { languageType = ContextFree
  , alphabet = alphabet
  , strings = Set.fromList strings
  , description = "Context-free language defined by context-free grammar"
  }

-- | 创建上下文相关语言
createContextSensitiveLanguage :: Set Char -> [String] -> LanguageClass
createContextSensitiveLanguage alphabet strings = LanguageClass
  { languageType = ContextSensitive
  , alphabet = alphabet
  , strings = Set.fromList strings
  , description = "Context-sensitive language defined by context-sensitive grammar"
  }

-- | 创建递归可枚举语言
createRecursivelyEnumerableLanguage :: Set Char -> [String] -> LanguageClass
createRecursivelyEnumerableLanguage alphabet strings = LanguageClass
  { languageType = RecursivelyEnumerable
  , alphabet = alphabet
  , strings = Set.fromList strings
  , description = "Recursively enumerable language defined by Turing machine"
  }

-- | 检查语言类型
checkLanguageType :: LanguageClass -> LanguageType
checkLanguageType = languageType

-- | 获取语言描述
getLanguageDescription :: LanguageClass -> String
getLanguageDescription = description
```

### 层次分析

```haskell
-- | 分析语言层次
analyzeHierarchy :: LanguageHierarchy -> String
analyzeHierarchy hierarchy = 
  let levelInfo = map showLevel (levels hierarchy)
      relationInfo = map showRelation (relations hierarchy)
  in unlines (levelInfo ++ relationInfo)

-- | 显示层次级别
showLevel :: LanguageType -> String
showLevel level = 
  case level of
    Regular -> "Level 3: Regular Languages"
    ContextFree -> "Level 2: Context-Free Languages"
    ContextSensitive -> "Level 1: Context-Sensitive Languages"
    RecursivelyEnumerable -> "Level 0: Recursively Enumerable Languages"

-- | 显示关系
showRelation :: HierarchyRelation -> String
showRelation relation = 
  let fromStr = show (fromType relation)
      toStr = show (toType relation)
      strictStr = if isStrict relation then "strictly contained in" else "contained in"
  in fromStr ++ " is " ++ strictStr ++ " " ++ toStr

-- | 获取层次路径
getHierarchyPath :: LanguageType -> LanguageType -> [LanguageType]
getHierarchyPath from to = 
  let fromIndex = fromEnum from
      toIndex = fromEnum to
  in if fromIndex <= toIndex
     then [toEnum i | i <- [fromIndex..toIndex]]
     else []

-- | 检查是否为最小包含
isMinimalContainment :: LanguageType -> LanguageType -> Bool
isMinimalContainment from to = 
  let fromIndex = fromEnum from
      toIndex = fromEnum to
  in toIndex == fromIndex + 1
```

## 📐 形式证明

### 定理1：层次包含关系

**定理**：对于任意 $i > j$，类型 $i$ 语言类包含类型 $j$ 语言类。

**证明**：

- **正则 ⊆ 上下文无关**：每个正则文法都是上下文无关文法
- **上下文无关 ⊆ 上下文相关**：每个上下文无关文法都是上下文相关文法
- **上下文相关 ⊆ 递归可枚举**：每个上下文相关文法都是无限制文法

### 定理2：严格包含关系

**定理**：层次包含关系是严格的，即存在语言属于类型 $i$ 但不属于类型 $j$（$i > j$）。

**证明**：

- **$L = \{a^n b^n \mid n \geq 0\}$**：上下文无关但不是正则
- **$L = \{a^n b^n c^n \mid n \geq 0\}$**：上下文相关但不是上下文无关
- **停机问题的语言**：递归可枚举但不是上下文相关

### 定理3：语言类的封闭性

**定理**：不同语言类在基本运算下的封闭性不同。

**证明**：

#### 正则语言封闭性

- **并集**：封闭
- **交集**：封闭
- **补集**：封闭
- **连接**：封闭
- **闭包**：封闭

#### 上下文无关语言封闭性

- **并集**：封闭
- **连接**：封闭
- **闭包**：封闭
- **交集**：不封闭
- **补集**：不封闭

**Haskell实现**：

```haskell
-- | 检查语言类封闭性
checkClosureProperties :: LanguageType -> Map String Bool
checkClosureProperties langType = 
  case langType of
    Regular -> Map.fromList
      [ ("union", True)
      , ("intersection", True)
      , ("complement", True)
      , ("concatenation", True)
      , ("kleene_star", True)
      ]
    ContextFree -> Map.fromList
      [ ("union", True)
      , ("intersection", False)
      , ("complement", False)
      , ("concatenation", True)
      , ("kleene_star", True)
      ]
    ContextSensitive -> Map.fromList
      [ ("union", True)
      , ("intersection", True)
      , ("complement", True)
      , ("concatenation", True)
      , ("kleene_star", True)
      ]
    RecursivelyEnumerable -> Map.fromList
      [ ("union", True)
      , ("intersection", True)
      , ("complement", False)
      , ("concatenation", True)
      , ("kleene_star", True)
      ]
```

## 🔍 实际应用

### 示例：语言分类

```haskell
-- | 示例语言
exampleLanguages :: Map String LanguageClass
exampleLanguages = Map.fromList
  [ ("even_a", createRegularLanguage (Set.fromList "ab") ["", "aa", "aaaa", "aaaaaa"])
  , ("a^n_b^n", createContextFreeLanguage (Set.fromList "ab") ["", "ab", "aabb", "aaabbb"])
  , ("a^n_b^n_c^n", createContextSensitiveLanguage (Set.fromList "abc") ["", "abc", "aabbcc", "aaabbbccc"])
  , ("halting", createRecursivelyEnumerableLanguage (Set.fromList "01") ["0", "1", "00", "01"])
  ]

-- | 测试语言层次
testLanguageHierarchy :: IO ()
testLanguageHierarchy = do
  putStrLn "Testing language hierarchy:"
  
  -- 测试包含关系
  putStrLn "Containment relations:"
  putStrLn $ "Regular ⊆ ContextFree: " ++ show (isContainedIn Regular ContextFree)
  putStrLn $ "ContextFree ⊆ ContextSensitive: " ++ show (isContainedIn ContextFree ContextSensitive)
  putStrLn $ "ContextSensitive ⊆ RecursivelyEnumerable: " ++ show (isContainedIn ContextSensitive RecursivelyEnumerable)
  
  -- 测试严格包含
  putStrLn "Strict containment:"
  putStrLn $ "Regular ⊂ ContextFree: " ++ show (isStrictlyContainedIn Regular ContextFree)
  
  -- 显示层次分析
  putStrLn "Hierarchy analysis:"
  putStrLn (analyzeHierarchy chomskyHierarchy)
```

### 性能分析

```haskell
-- | 语言类复杂度分析
languageComplexity :: LanguageType -> (Int, String)
languageComplexity langType = 
  case langType of
    Regular -> (1, "Linear time")
    ContextFree -> (2, "Polynomial time")
    ContextSensitive -> (3, "Exponential time")
    RecursivelyEnumerable -> (4, "Undecidable")

-- | 层次深度分析
hierarchyDepth :: LanguageType -> Int
hierarchyDepth = fromEnum

-- | 包含链分析
containmentChain :: LanguageType -> [LanguageType]
containmentChain langType = 
  let currentIndex = fromEnum langType
  in [toEnum i | i <- [currentIndex..3]]
```

## 🔗 相关概念

- [有限自动机](01-有限自动机/01-Basic-Concepts.md) - 识别正则语言
- [下推自动机](02-上下文无关语言/02-Pushdown-Automata.md) - 识别上下文无关语言
- [图灵机](03-图灵机理论/01-Basic-Turing-Machines.md) - 识别递归可枚举语言
- [语法理论](02-Grammar-Theory.md) - 生成不同语言类的文法

## 📚 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Chomsky, N. (1956). Three models for the description of language.

---

*本文档提供了语言层次的完整形式化框架，包括乔姆斯基层次的严格定义、可执行的Haskell实现和构造性证明。*
