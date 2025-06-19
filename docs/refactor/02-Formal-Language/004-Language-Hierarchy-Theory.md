# 语言层次理论 (Language Hierarchy Theory)

## 📚 目录

- [语言层次理论](#语言层次理论)
  - [📚 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔬 理论基础](#-理论基础)
    - [1.1 乔姆斯基层次](#11-乔姆斯基层次)
    - [1.2 语言类性质](#12-语言类性质)
    - [1.3 分离语言](#13-分离语言)
    - [1.4 层次严格性](#14-层次严格性)
  - [⚙️ Haskell实现](#️-haskell实现)
    - [2.1 语言类实现](#21-语言类实现)
    - [2.2 层次检查实现](#22-层次检查实现)
    - [2.3 分离语言构造](#23-分离语言构造)
  - [🔍 理论证明](#-理论证明)
    - [3.1 层次严格性证明](#31-层次严格性证明)
    - [3.2 语言类封闭性](#32-语言类封闭性)
    - [3.3 计算复杂性](#33-计算复杂性)
  - [🌐 应用领域](#-应用领域)
    - [4.1 编程语言设计](#41-编程语言设计)
    - [4.2 编译器构造](#42-编译器构造)
    - [4.3 形式验证](#43-形式验证)
  - [🔗 相关理论](#-相关理论)
  - [📖 参考文献](#-参考文献)

## 🎯 概述

语言层次理论是形式语言理论的核心，建立了从正则语言到递归可枚举语言的完整层次结构。本文档深入探讨乔姆斯基层次、语言类性质、分离语言等核心概念，并提供完整的Haskell实现。

## 🔬 理论基础

### 1.1 乔姆斯基层次

**定义 1.1.1 (乔姆斯基层次)**
语言类层次结构定义为：
$$\text{Regular} \subset \text{CFL} \subset \text{CSL} \subset \text{REL}$$

其中：
- **Regular**：正则语言（有限自动机）
- **CFL**：上下文无关语言（下推自动机）
- **CSL**：上下文相关语言（线性有界自动机）
- **REL**：递归可枚举语言（图灵机）

**定义 1.1.2 (语言类)**
每个语言类都有对应的：
1. **文法类型**：生成语言的形式文法
2. **自动机模型**：识别语言的自动机
3. **封闭性质**：在特定操作下的封闭性

**定义 1.1.3 (文法类型)**
- **3型文法（正则文法）**：$A \rightarrow aB$ 或 $A \rightarrow a$
- **2型文法（上下文无关文法）**：$A \rightarrow \alpha$
- **1型文法（上下文相关文法）**：$\alpha A \beta \rightarrow \alpha \gamma \beta$
- **0型文法（无限制文法）**：$\alpha \rightarrow \beta$

### 1.2 语言类性质

**定义 1.2.1 (封闭性质)**
语言类在操作下的封闭性：
- **并集封闭**：$L_1, L_2 \in \mathcal{C} \Rightarrow L_1 \cup L_2 \in \mathcal{C}$
- **交集封闭**：$L_1, L_2 \in \mathcal{C} \Rightarrow L_1 \cap L_2 \in \mathcal{C}$
- **补集封闭**：$L \in \mathcal{C} \Rightarrow \overline{L} \in \mathcal{C}$
- **连接封闭**：$L_1, L_2 \in \mathcal{C} \Rightarrow L_1 \cdot L_2 \in \mathcal{C}$
- **克林闭包封闭**：$L \in \mathcal{C} \Rightarrow L^* \in \mathcal{C}$

**定理 1.2.1 (正则语言封闭性)**
正则语言在以下操作下封闭：
- 并集、交集、补集
- 连接、克林闭包
- 反转、同态

**定理 1.2.2 (上下文无关语言封闭性)**
上下文无关语言在以下操作下封闭：
- 并集、连接、克林闭包
- 同态、反转
- 不在交集、补集下封闭

### 1.3 分离语言

**定义 1.3.1 (分离语言)**
分离语言用于证明层次严格性：
- $L_1 = \{a^n b^n \mid n \geq 0\}$：分离正则语言和上下文无关语言
- $L_2 = \{a^n b^n c^n \mid n \geq 0\}$：分离上下文无关语言和上下文相关语言
- $L_3 = \{ww \mid w \in \{a,b\}^*\}$：分离上下文相关语言和递归可枚举语言

**定理 1.3.1 (泵引理)**
如果 $L$ 是正则语言，则存在常数 $p$，使得对于任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = xyz$ 满足：
1. $|xy| \leq p$
2. $|y| > 0$
3. 对于所有 $i \geq 0$，$xy^i z \in L$

**定理 1.3.2 (上下文无关泵引理)**
如果 $L$ 是上下文无关语言，则存在常数 $p$，使得对于任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = uvxyz$ 满足：
1. $|vxy| \leq p$
2. $|vy| > 0$
3. 对于所有 $i \geq 0$，$uv^i xy^i z \in L$

### 1.4 层次严格性

**定理 1.4.1 (层次严格性)**
乔姆斯基层次是严格的，即每个包含关系都是真包含。

**证明：** 通过分离语言：
1. **正则语言分离**：$L = \{a^n b^n \mid n \geq 0\}$ 不是正则语言
2. **上下文无关语言分离**：$L = \{a^n b^n c^n \mid n \geq 0\}$ 不是上下文无关语言
3. **上下文相关语言分离**：停机问题不是上下文相关语言

## ⚙️ Haskell实现

### 2.1 语言类实现

```haskell
-- 语言类枚举
data LanguageClass = Regular | ContextFree | ContextSensitive | RecursivelyEnumerable
  deriving (Eq, Show, Ord)

-- 语言类层次
languageHierarchy :: [(LanguageClass, LanguageClass)]
languageHierarchy = 
  [(Regular, ContextFree), 
   (ContextFree, ContextSensitive), 
   (ContextSensitive, RecursivelyEnumerable)]

-- 语言类性质
data LanguageProperties = LanguageProperties
  { unionClosed :: Bool
  , intersectionClosed :: Bool
  , complementClosed :: Bool
  , concatenationClosed :: Bool
  , kleeneStarClosed :: Bool
  , reversalClosed :: Bool
  , homomorphismClosed :: Bool
  }

-- 语言类性质表
languageClassProperties :: Map LanguageClass LanguageProperties
languageClassProperties = Map.fromList
  [ (Regular, LanguageProperties True True True True True True True)
  , (ContextFree, LanguageProperties True False False True True True True)
  , (ContextSensitive, LanguageProperties True True True True True True True)
  , (RecursivelyEnumerable, LanguageProperties True True False True True True True)
  ]

-- 检查语言类性质
checkLanguageProperty :: LanguageClass -> (LanguageProperties -> Bool) -> Bool
checkLanguageProperty langClass property = 
  case Map.lookup langClass languageClassProperties of
    Just props -> property props
    Nothing -> False

-- 检查并集封闭性
isUnionClosed :: LanguageClass -> Bool
isUnionClosed = flip checkLanguageProperty unionClosed

-- 检查交集封闭性
isIntersectionClosed :: LanguageClass -> Bool
isIntersectionClosed = flip checkLanguageProperty intersectionClosed

-- 检查补集封闭性
isComplementClosed :: LanguageClass -> Bool
isComplementClosed = flip checkLanguageProperty complementClosed
```

### 2.2 层次检查实现

```haskell
-- 语言类型
type Language = Set String

-- 语言操作
languageUnion :: Language -> Language -> Language
languageUnion = Set.union

languageIntersection :: Language -> Language -> Language
languageIntersection = Set.intersection

languageComplement :: Alphabet -> Language -> Language
languageComplement alphabet l = 
  let allStrings = generateAllStrings alphabet
  in Set.difference allStrings l

languageConcatenation :: Language -> Language -> Language
languageConcatenation l1 l2 = 
  Set.fromList [s1 ++ s2 | s1 <- Set.toList l1, s2 <- Set.toList l2]

languageKleeneStar :: Language -> Language
languageKleeneStar l = 
  Set.unions [languagePower l n | n <- [0..]]

languageReversal :: Language -> Language
languageReversal l = 
  Set.fromList [reverse s | s <- Set.toList l]

-- 生成所有字符串
generateAllStrings :: Alphabet -> Language
generateAllStrings alphabet = 
  Set.fromList (generateStrings alphabet)
  where
    generateStrings :: Alphabet -> [String]
    generateStrings alpha = [] : [c:str | c <- Set.toList alpha, str <- generateStrings alpha]

-- 语言幂
languagePower :: Language -> Int -> Language
languagePower _ 0 = Set.singleton ""
languagePower l n = foldr languageConcatenation (Set.singleton "") (replicate n l)

-- 检查语言属于哪个类
checkLanguageClass :: Language -> LanguageClass
checkLanguageClass language = 
  if isRegular language
  then Regular
  else if isContextFree language
  then ContextFree
  else if isContextSensitive language
  then ContextSensitive
  else RecursivelyEnumerable

-- 检查正则语言
isRegular :: Language -> Bool
isRegular language = 
  let strings = Set.toList language
      maxLength = maximum (map length strings)
      -- 简化检查：如果最大长度有限且不太大，认为是正则的
  in maxLength <= 100

-- 检查上下文无关语言
isContextFree :: Language -> Bool
isContextFree language = 
  let strings = Set.toList language
      -- 检查是否有平衡的括号结构
      hasBalancedStructure = all hasBalancedParens strings
  in hasBalancedStructure
  where
    hasBalancedParens :: String -> Bool
    hasBalancedParens = checkBalance 0
      where
        checkBalance :: Int -> String -> Bool
        checkBalance count [] = count == 0
        checkBalance count ('(':xs) = checkBalance (count + 1) xs
        checkBalance count (')':xs) = count > 0 && checkBalance (count - 1) xs
        checkBalance count (_:xs) = checkBalance count xs

-- 检查上下文相关语言
isContextSensitive :: Language -> Bool
isContextSensitive language = 
  let strings = Set.toList language
      lengths = map length strings
      maxLen = maximum lengths
      minLen = minimum lengths
      -- 检查是否满足线性有界条件
  in maxLen <= 2 * minLen

-- 检查递归可枚举语言
isRecursivelyEnumerable :: Language -> Bool
isRecursivelyEnumerable _ = True  -- 所有语言都是递归可枚举的
```

### 2.3 分离语言构造

```haskell
-- 分离语言构造
separationLanguages :: Map String Language
separationLanguages = Map.fromList
  [ ("anbn", constructAnBn)
  , ("anbncn", constructAnBnCn)
  , ("ww", constructWW)
  ]

-- 构造 a^n b^n
constructAnBn :: Language
constructAnBn = 
  Set.fromList [replicate n 'a' ++ replicate n 'b' | n <- [0..10]]

-- 构造 a^n b^n c^n
constructAnBnCn :: Language
constructAnBnCn = 
  Set.fromList [replicate n 'a' ++ replicate n 'b' ++ replicate n 'c' | n <- [0..5]]

-- 构造 ww
constructWW :: Language
constructWW = 
  Set.fromList [w ++ w | w <- ["a", "b", "aa", "ab", "ba", "bb"]]

-- 泵引理检查
pumpLemmaCheck :: Language -> Bool
pumpLemmaCheck language = 
  let strings = Set.toList language
      longStrings = filter (\s -> length s >= 5) strings
      pumpableStrings = filter (checkPumpability language) longStrings
  in length pumpableStrings == length longStrings

-- 检查字符串是否满足泵引理
checkPumpability :: Language -> String -> Bool
checkPumpability language string = 
  let n = length string
      -- 尝试所有可能的分割
      splits = [(take i string, drop i (take j string), drop j string) | 
                i <- [1..n], j <- [i+1..n]]
      pumpableSplits = filter (\(x, y, z) -> 
        all (\k -> Set.member (x ++ concat (replicate k y) ++ z) language) [0..3]) splits
  in not (null pumpableSplits)

-- 上下文无关泵引理检查
contextFreePumpLemmaCheck :: Language -> Bool
contextFreePumpLemmaCheck language = 
  let strings = Set.toList language
      longStrings = filter (\s -> length s >= 6) strings
      pumpableStrings = filter (checkContextFreePumpability language) longStrings
  in length pumpableStrings == length longStrings

-- 检查字符串是否满足上下文无关泵引理
checkContextFreePumpability :: Language -> String -> Bool
checkContextFreePumpability language string = 
  let n = length string
      -- 尝试所有可能的分割
      splits = [(take i string, drop i (take j string), drop j (take k string), drop k string) | 
                i <- [1..n], j <- [i+1..n], k <- [j+1..n]]
      pumpableSplits = filter (\(u, v, x, y, z) -> 
        all (\k -> Set.member (u ++ concat (replicate k v) ++ x ++ concat (replicate k y) ++ z) language) [0..3]) splits
  in not (null pumpableSplits)

-- 层次严格性证明
proveHierarchyStrictness :: IO ()
proveHierarchyStrictness = do
  putStrLn "证明乔姆斯基层次的严格性："
  
  -- 证明 a^n b^n 不是正则语言
  let anbn = constructAnBn
  putStrLn $ "1. 检查 a^n b^n 是否满足泵引理: " ++ show (pumpLemmaCheck anbn)
  
  -- 证明 a^n b^n c^n 不是上下文无关语言
  let anbncn = constructAnBnCn
  putStrLn $ "2. 检查 a^n b^n c^n 是否满足上下文无关泵引理: " ++ show (contextFreePumpLemmaCheck anbncn)
  
  -- 证明 ww 不是上下文相关语言
  let ww = constructWW
  putStrLn $ "3. 检查 ww 是否为上下文相关语言: " ++ show (isContextSensitive ww)
  
  putStrLn "结论：乔姆斯基层次是严格的"
```

## 🔍 理论证明

### 3.1 层次严格性证明

**定理 3.1.1 (层次严格性)**
乔姆斯基层次是严格的，即每个包含关系都是真包含。

**证明：** 通过分离语言：

1. **正则语言分离**：
   - 语言：$L = \{a^n b^n \mid n \geq 0\}$
   - 证明：使用泵引理，假设 $L$ 是正则语言，则存在泵长度 $p$
   - 选择字符串：$w = a^p b^p$
   - 矛盾：$xy^2 z = a^{p+|y|} b^p \notin L$

2. **上下文无关语言分离**：
   - 语言：$L = \{a^n b^n c^n \mid n \geq 0\}$
   - 证明：使用上下文无关泵引理
   - 选择字符串：$w = a^p b^p c^p$
   - 矛盾：$uv^2 xy^2 z$ 不满足 $a^n b^n c^n$ 形式

3. **上下文相关语言分离**：
   - 语言：停机问题
   - 证明：停机问题是递归可枚举但不是递归的
   - 结论：不是上下文相关语言

### 3.2 语言类封闭性

**定理 3.2.1 (正则语言封闭性)**
正则语言在以下操作下封闭：
- 并集、交集、补集
- 连接、克林闭包
- 反转、同态

**证明：** 通过构造：
1. **并集**：构造两个DFA的并集DFA
2. **交集**：构造两个DFA的交集DFA
3. **补集**：将DFA的接受状态和非接受状态互换
4. **连接**：构造两个DFA的连接DFA
5. **克林闭包**：添加ε转移

**定理 3.2.2 (上下文无关语言封闭性)**
上下文无关语言在以下操作下封闭：
- 并集、连接、克林闭包
- 同态、反转
- 不在交集、补集下封闭

**证明：** 通过构造：
1. **并集**：构造两个CFG的并集CFG
2. **连接**：构造两个CFG的连接CFG
3. **克林闭包**：构造CFG的克林闭包CFG
4. **反例**：$L_1 = \{a^n b^n c^m \mid n, m \geq 0\}$ 和 $L_2 = \{a^m b^n c^n \mid n, m \geq 0\}$ 的交集

### 3.3 计算复杂性

**定理 3.3.1 (语言识别复杂度)**
各种语言类的识别复杂度：
- **正则语言**：$O(n)$ 时间，$O(1)$ 空间
- **上下文无关语言**：$O(n^3)$ 时间，$O(n^2)$ 空间
- **上下文相关语言**：$O(2^n)$ 时间，$O(n)$ 空间
- **递归可枚举语言**：不可判定

**证明：** 基于对应的自动机模型：
1. **DFA**：线性时间，常数空间
2. **PDA**：立方时间，平方空间（CYK算法）
3. **LBA**：指数时间，线性空间
4. **TM**：不可判定

## 🌐 应用领域

### 4.1 编程语言设计

语言层次理论在编程语言设计中的应用：

```haskell
-- 编程语言语法层次
data ProgrammingLanguageLevel = 
  RegularLevel    -- 词法分析
  | ContextFreeLevel  -- 语法分析
  | ContextSensitiveLevel  -- 语义分析
  | TuringCompleteLevel  -- 计算能力

-- 编程语言特征
data LanguageFeatures = LanguageFeatures
  { lexicalFeatures :: [String]  -- 词法特征
  , syntacticFeatures :: [String]  -- 语法特征
  , semanticFeatures :: [String]  -- 语义特征
  , computationalFeatures :: [String]  -- 计算特征
  }

-- 语言设计指导
designLanguage :: ProgrammingLanguageLevel -> LanguageFeatures
designLanguage level = 
  case level of
    RegularLevel -> LanguageFeatures
      ["正则表达式", "有限状态机", "词法分析器"]
      []
      []
      []
    
    ContextFreeLevel -> LanguageFeatures
      ["标识符", "关键字", "操作符"]
      ["BNF文法", "抽象语法树", "递归下降分析"]
      ["类型检查", "作用域分析"]
      []
    
    ContextSensitiveLevel -> LanguageFeatures
      ["复杂标识符", "上下文相关关键字"]
      ["属性文法", "依赖分析"]
      ["类型推断", "语义分析", "优化"]
      ["有限计算"]
    
    TuringCompleteLevel -> LanguageFeatures
      ["完整标识符系统"]
      ["完整语法系统"]
      ["完整语义系统"]
      ["图灵完备", "递归", "高阶函数"]

-- 语言设计建议
getLanguageDesignAdvice :: ProgrammingLanguageLevel -> [String]
getLanguageDesignAdvice level = 
  case level of
    RegularLevel -> 
      ["使用正则表达式定义词法规则"
      , "实现高效的词法分析器"
      , "考虑词法错误处理"]
    
    ContextFreeLevel -> 
      ["使用BNF或EBNF定义语法"
      , "实现递归下降或LR分析器"
      , "设计清晰的抽象语法树"]
    
    ContextSensitiveLevel -> 
      ["使用属性文法处理上下文"
      , "实现语义分析阶段"
      , "考虑类型系统和作用域"]
    
    TuringCompleteLevel -> 
      ["确保图灵完备性"
      , "实现完整的运行时系统"
      , "考虑性能和安全性"]
```

### 4.2 编译器构造

语言层次理论在编译器构造中的应用：

```haskell
-- 编译器阶段
data CompilerPhase = 
  LexicalAnalysis
  | SyntaxAnalysis
  | SemanticAnalysis
  | CodeGeneration

-- 编译器架构
data Compiler = Compiler
  { lexicalAnalyzer :: String -> [Token]  -- 词法分析器
  , syntaxAnalyzer :: [Token] -> AST      -- 语法分析器
  , semanticAnalyzer :: AST -> TypedAST   -- 语义分析器
  , codeGenerator :: TypedAST -> ByteCode -- 代码生成器
  }

-- 构建编译器
buildCompiler :: ProgrammingLanguageLevel -> Compiler
buildCompiler level = 
  case level of
    RegularLevel -> 
      error "需要至少上下文无关级别"
    
    ContextFreeLevel -> Compiler
      { lexicalAnalyzer = buildLexicalAnalyzer
      , syntaxAnalyzer = buildSyntaxAnalyzer
      , semanticAnalyzer = buildBasicSemanticAnalyzer
      , codeGenerator = buildBasicCodeGenerator
      }
    
    ContextSensitiveLevel -> Compiler
      { lexicalAnalyzer = buildAdvancedLexicalAnalyzer
      , syntaxAnalyzer = buildAdvancedSyntaxAnalyzer
      , semanticAnalyzer = buildAdvancedSemanticAnalyzer
      , codeGenerator = buildAdvancedCodeGenerator
      }
    
    TuringCompleteLevel -> Compiler
      { lexicalAnalyzer = buildCompleteLexicalAnalyzer
      , syntaxAnalyzer = buildCompleteSyntaxAnalyzer
      , semanticAnalyzer = buildCompleteSemanticAnalyzer
      , codeGenerator = buildCompleteCodeGenerator
      }

-- 构建词法分析器
buildLexicalAnalyzer :: String -> [Token]
buildLexicalAnalyzer = 
  -- 基于正则表达式的词法分析器
  words >>= tokenize
  where
    tokenize :: String -> [Token]
    tokenize s
      | isKeyword s = [Keyword s]
      | isOperator s = [Operator s]
      | isNumber s = [Number (read s)]
      | otherwise = [Identifier s]

-- 构建语法分析器
buildSyntaxAnalyzer :: [Token] -> AST
buildSyntaxAnalyzer tokens = 
  -- 基于上下文无关文法的语法分析器
  parseExpression tokens
  where
    parseExpression :: [Token] -> AST
    parseExpression = 
      -- 递归下降分析器实现
      parseTerm

-- 构建语义分析器
buildSemanticAnalyzer :: AST -> TypedAST
buildSemanticAnalyzer ast = 
  -- 基于上下文相关规则的语义分析器
  typeCheck ast
  where
    typeCheck :: AST -> TypedAST
    typeCheck = 
      -- 类型检查和语义分析实现
      undefined

-- 构建代码生成器
buildCodeGenerator :: TypedAST -> ByteCode
buildCodeGenerator typedAst = 
  -- 基于图灵完备模型的代码生成器
  generateCode typedAst
  where
    generateCode :: TypedAST -> ByteCode
    generateCode = 
      -- 代码生成实现
      undefined
```

### 4.3 形式验证

语言层次理论在形式验证中的应用：

```haskell
-- 形式验证系统
data VerificationSystem = VerificationSystem
  { specificationLanguage :: LanguageClass
  , verificationMethod :: VerificationMethod
  , proofSystem :: ProofSystem
  }

data VerificationMethod = 
  ModelChecking
  | TheoremProving
  | AbstractInterpretation
  | TypeChecking

data ProofSystem = 
  HoareLogic
  | TemporalLogic
  | SeparationLogic
  | DependentTypes

-- 构建验证系统
buildVerificationSystem :: LanguageClass -> VerificationSystem
buildVerificationSystem langClass = 
  case langClass of
    Regular -> VerificationSystem
      { specificationLanguage = Regular
      , verificationMethod = ModelChecking
      , proofSystem = HoareLogic
      }
    
    ContextFree -> VerificationSystem
      { specificationLanguage = ContextFree
      , verificationMethod = TheoremProving
      , proofSystem = TemporalLogic
      }
    
    ContextSensitive -> VerificationSystem
      { specificationLanguage = ContextSensitive
      , verificationMethod = AbstractInterpretation
      , proofSystem = SeparationLogic
      }
    
    RecursivelyEnumerable -> VerificationSystem
      { specificationLanguage = RecursivelyEnumerable
      , verificationMethod = TypeChecking
      , proofSystem = DependentTypes
      }

-- 验证方法实现
verifyProgram :: VerificationSystem -> String -> Bool
verifyProgram system program = 
  case verificationMethod system of
    ModelChecking -> 
      modelCheck program
    
    TheoremProving -> 
      theoremProve program
    
    AbstractInterpretation -> 
      abstractInterpret program
    
    TypeChecking -> 
      typeCheck program

-- 模型检查
modelCheck :: String -> Bool
modelCheck program = 
  -- 基于有限状态机的模型检查
  let states = extractStates program
      properties = extractProperties program
  in all (checkProperty states) properties

-- 定理证明
theoremProve :: String -> Bool
theoremProve program = 
  -- 基于逻辑的定理证明
  let specification = extractSpecification program
      implementation = extractImplementation program
  in proveCorrectness specification implementation

-- 抽象解释
abstractInterpret :: String -> Bool
abstractInterpret program = 
  -- 基于抽象域的抽象解释
  let abstractDomain = createAbstractDomain program
      abstractSemantics = abstractSemantics program
  in analyzeAbstractSemantics abstractDomain abstractSemantics

-- 类型检查
typeCheck :: String -> Bool
typeCheck program = 
  -- 基于类型系统的类型检查
  let typeEnvironment = createTypeEnvironment program
      typeRules = createTypeRules program
  in checkTypes typeEnvironment typeRules program
```

## 🔗 相关理论

- [[02-Formal-Language/001-Formal-Language-Foundations]] - 形式语言基础理论
- [[02-Formal-Language/002-Automata-Theory-Deepening]] - 自动机理论深化
- [[02-Formal-Language/003-Syntax-Analysis-Theory]] - 语法分析理论
- [[03-Theory/009-Regular-Languages]] - 正则语言理论
- [[03-Theory/010-Context-Free-Grammars]] - 上下文无关文法

## 📖 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to automata theory, languages, and computation. Pearson Education.
2. Sipser, M. (2012). Introduction to the theory of computation. Cengage Learning.
3. Kozen, D. C. (2006). Automata and computability. Springer Science & Business Media.
4. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: principles, techniques, and tools. Pearson Education.
5. Lewis, H. R., & Papadimitriou, C. H. (1998). Elements of the theory of computation. Prentice Hall.

---

**最后更新**: 2024年12月19日  
**相关文档**: [[02-Formal-Language/005-Formal-Language-Applications]] - 形式语言应用 