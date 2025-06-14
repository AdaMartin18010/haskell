# 线性时态逻辑语法语义

## 📋 概述

线性时态逻辑（Linear Temporal Logic, LTL）是一种用于描述系统时间相关性质的形式化语言。它基于线性时间模型，即每个执行路径都被视为一个无限的时间序列。LTL广泛应用于模型检测、程序验证和协议验证等领域。

## 🎯 核心概念

### LTL语法

#### 基本语法定义

```haskell
-- LTL公式的语法定义
data LTLFormula = 
    LTLTrue                    -- 真值
  | LTLFalse                   -- 假值
  | LTLProp String             -- 原子命题
  | LTLNot LTLFormula          -- 否定
  | LTLAnd LTLFormula LTLFormula -- 合取
  | LTLOr LTLFormula LTLFormula  -- 析取
  | LTLImplies LTLFormula LTLFormula -- 蕴含
  | LTLNext LTLFormula         -- 下一个
  | LTLUntil LTLFormula LTLFormula -- 直到
  | LTLRelease LTLFormula LTLFormula -- 释放
  | LTLFinally LTLFormula      -- 最终
  | LTLGlobally LTLFormula     -- 总是
  deriving (Eq, Show)

-- 派生操作符
ltlFinally :: LTLFormula -> LTLFormula
ltlFinally phi = LTLUntil LTLTrue phi

ltlGlobally :: LTLFormula -> LTLFormula
ltlGlobally phi = LTLNot (LTLUntil LTLTrue (LTLNot phi))

ltlWeakUntil :: LTLFormula -> LTLFormula -> LTLFormula
ltlWeakUntil phi psi = LTLOr (LTLUntil phi psi) (ltlGlobally phi)
```

#### 语法规则

```haskell
-- 语法规则定义
data LTLGrammar = LTLGrammar
    { atoms :: [String]        -- 原子命题集合
    , formulas :: [LTLFormula] -- 公式集合
    }

-- 语法检查函数
isValidLTL :: LTLFormula -> Bool
isValidLTL LTLTrue = True
isValidLTL LTLFalse = True
isValidLTL (LTLProp _) = True
isValidLTL (LTLNot phi) = isValidLTL phi
isValidLTL (LTLAnd phi psi) = isValidLTL phi && isValidLTL psi
isValidLTL (LTLOr phi psi) = isValidLTL phi && isValidLTL psi
isValidLTL (LTLImplies phi psi) = isValidLTL phi && isValidLTL psi
isValidLTL (LTLNext phi) = isValidLTL phi
isValidLTL (LTLUntil phi psi) = isValidLTL phi && isValidLTL psi
isValidLTL (LTLRelease phi psi) = isValidLTL phi && isValidLTL psi
isValidLTL (LTLFinally phi) = isValidLTL phi
isValidLTL (LTLGlobally phi) = isValidLTL phi
```

### LTL语义

#### Kripke结构

```haskell
-- Kripke结构定义
data KripkeStructure = KripkeStructure
    { states :: [String]                    -- 状态集合
    , initialStates :: [String]             -- 初始状态集合
    , transitions :: [(String, String)]     -- 转换关系
    , labeling :: String -> [String]        -- 标记函数
    }

-- 路径定义
type Path = [String]

-- 路径生成
generatePaths :: KripkeStructure -> [Path]
generatePaths ks = 
    concatMap (\s -> generatePathsFrom ks s) (initialStates ks)

generatePathsFrom :: KripkeStructure -> String -> [Path]
generatePathsFrom ks s = 
    s : concatMap (\s' -> generatePathsFrom ks s') (nextStates ks s)

nextStates :: KripkeStructure -> String -> [String]
nextStates ks s = 
    [s' | (s1, s') <- transitions ks, s1 == s]
```

#### 语义函数

```haskell
-- LTL语义函数
type LTLModel = KripkeStructure
type LTLPath = [String]
type LTLState = String

-- 语义关系
satisfies :: LTLModel -> LTLPath -> LTLState -> LTLFormula -> Bool
satisfies model path state formula = 
    case formula of
        LTLTrue -> True
        LTLFalse -> False
        LTLProp p -> p `elem` (labeling model state)
        LTLNot phi -> not (satisfies model path state phi)
        LTLAnd phi psi -> 
            satisfies model path state phi && 
            satisfies model path state psi
        LTLOr phi psi -> 
            satisfies model path state phi || 
            satisfies model path state psi
        LTLImplies phi psi -> 
            not (satisfies model path state phi) || 
            satisfies model path state psi
        LTLNext phi -> 
            case dropWhile (/= state) path of
                (_:next:_) -> satisfies model path next phi
                _ -> False
        LTLUntil phi psi -> 
            satisfiesUntil model path state phi psi
        LTLRelease phi psi -> 
            satisfiesRelease model path state phi psi
        LTLFinally phi -> 
            satisfies model path state (ltlFinally phi)
        LTLGlobally phi -> 
            satisfies model path state (ltlGlobally phi)

-- 直到操作符的语义
satisfiesUntil :: LTLModel -> LTLPath -> LTLState -> LTLFormula -> LTLFormula -> Bool
satisfiesUntil model path state phi psi = 
    case dropWhile (/= state) path of
        [] -> False
        (s:rest) -> 
            satisfies model path s psi || 
            (satisfies model path s phi && 
             satisfiesUntil model path (head rest) phi psi)

-- 释放操作符的语义
satisfiesRelease :: LTLModel -> LTLPath -> LTLState -> LTLFormula -> LTLFormula -> Bool
satisfiesRelease model path state phi psi = 
    case dropWhile (/= state) path of
        [] -> satisfies model path state psi
        (s:rest) -> 
            satisfies model path s psi && 
            (satisfies model path s phi || 
             satisfiesRelease model path (head rest) phi psi)
```

## 🔧 Haskell实现

### LTL解析器

```haskell
-- LTL解析器
module LTLParser where

import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

-- 词法分析器
lexer :: TokenParser ()
lexer = makeTokenParser $ 
    emptyDef { 
        reservedNames = ["true", "false", "next", "until", "release", "finally", "globally"]
    ,   reservedOpNames = ["!", "&", "|", "->", "X", "U", "R", "F", "G"]
    }

-- 解析器组合子
parens :: Parser a -> Parser a
parens = getToken lexer . parens

reserved :: String -> Parser ()
reserved = getToken lexer . reserved

reservedOp :: String -> Parser ()
reservedOp = getToken lexer . reservedOp

identifier :: Parser String
identifier = getToken lexer . identifier

-- LTL公式解析器
parseLTL :: String -> Either ParseError LTLFormula
parseLTL = parse ltlFormula ""

ltlFormula :: Parser LTLFormula
ltlFormula = buildExpressionParser operators term

operators :: [[Operator String () Identity LTLFormula]]
operators = [
    [Prefix (reservedOp "!" >> return LTLNot)],
    [Prefix (reservedOp "X" >> return LTLNext)],
    [Prefix (reservedOp "F" >> return LTLFinally)],
    [Prefix (reservedOp "G" >> return LTLGlobally)],
    [Infix (reservedOp "&" >> return LTLAnd) AssocLeft],
    [Infix (reservedOp "|" >> return LTLOr) AssocLeft],
    [Infix (reservedOp "->" >> return LTLImplies) AssocRight],
    [Infix (reservedOp "U" >> return LTLUntil) AssocLeft],
    [Infix (reservedOp "R" >> return LTLRelease) AssocLeft]
    ]

term :: Parser LTLFormula
term = parens ltlFormula
    <|> (reserved "true" >> return LTLTrue)
    <|> (reserved "false" >> return LTLFalse)
    <|> (LTLProp <$> identifier)
```

### LTL模型检测器

```haskell
-- LTL模型检测器
module LTLModelChecker where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

-- Büchi自动机
data BuchiAutomaton = BuchiAutomaton
    { states :: Set String
    , alphabet :: Set String
    , transitions :: Map (String, String) (Set String)
    , initialStates :: Set String
    , acceptingStates :: Set String
    }

-- 从LTL公式构造Büchi自动机
ltlToBuchi :: LTLFormula -> BuchiAutomaton
ltlToBuchi formula = 
    let closure = computeClosure formula
        states = generateStates closure
        transitions = generateTransitions states closure
        initialStates = Set.singleton (initialState closure)
        acceptingStates = computeAcceptingStates states formula
    in BuchiAutomaton states (computeAlphabet formula) 
                      transitions initialStates acceptingStates

-- 计算闭包
computeClosure :: LTLFormula -> Set LTLFormula
computeClosure formula = 
    Set.insert formula $ 
    case formula of
        LTLNot phi -> computeClosure phi
        LTLAnd phi psi -> 
            Set.union (computeClosure phi) (computeClosure psi)
        LTLOr phi psi -> 
            Set.union (computeClosure phi) (computeClosure psi)
        LTLNext phi -> computeClosure phi
        LTLUntil phi psi -> 
            Set.union (computeClosure phi) (computeClosure psi)
        LTLRelease phi psi -> 
            Set.union (computeClosure phi) (computeClosure psi)
        _ -> Set.empty

-- 生成状态
generateStates :: Set LTLFormula -> Set (Set LTLFormula)
generateStates closure = 
    Set.fromList [s | s <- Set.powerSet closure, isConsistent s]

-- 一致性检查
isConsistent :: Set LTLFormula -> Bool
isConsistent formulas = 
    not (LTLTrue `Set.member` formulas && LTLFalse `Set.member` formulas) &&
    not (any (\f -> LTLNot f `Set.member` formulas && f `Set.member` formulas) formulas)
```

## 📊 LTL公式示例

### 基本性质

```haskell
-- 安全性性质：坏事永远不会发生
safetyProperty :: LTLFormula
safetyProperty = ltlGlobally (LTLNot (LTLProp "error"))

-- 活性性质：好事最终会发生
livenessProperty :: LTLFormula
livenessProperty = ltlFinally (LTLProp "success")

-- 公平性性质：如果请求总是发生，那么响应最终会发生
fairnessProperty :: LTLFormula
fairnessProperty = ltlGlobally (LTLImplies (LTLProp "request") 
                                          (ltlFinally (LTLProp "response")))

-- 响应性质：请求后最终会有响应
responseProperty :: LTLFormula
responseProperty = ltlGlobally (LTLImplies (LTLProp "request") 
                                          (LTLUntil LTLTrue (LTLProp "response")))
```

### 复杂性质

```haskell
-- 互斥性质：两个进程不能同时进入临界区
mutualExclusion :: LTLFormula
mutualExclusion = ltlGlobally (LTLNot (LTLAnd (LTLProp "in_cs1") (LTLProp "in_cs2")))

-- 无饥饿性质：如果进程请求进入临界区，最终会进入
noStarvation :: LTLFormula
noStarvation = ltlGlobally (LTLImplies (LTLProp "request1") 
                                      (ltlFinally (LTLProp "in_cs1")))

-- 顺序性质：事件必须按特定顺序发生
orderingProperty :: LTLFormula
orderingProperty = ltlGlobally (LTLImplies (LTLProp "event2") 
                                          (LTLUntil LTLTrue (LTLProp "event1")))
```

## 🎯 应用示例

### 简单验证示例

```haskell
-- 示例Kripke结构
exampleModel :: KripkeStructure
exampleModel = KripkeStructure
    { states = ["s0", "s1", "s2"]
    , initialStates = ["s0"]
    , transitions = [("s0", "s1"), ("s1", "s2"), ("s2", "s1")]
    , labeling = \s -> case s of
        "s0" -> ["start"]
        "s1" -> ["running"]
        "s2" -> ["error"]
        _ -> []
    }

-- 验证示例
exampleVerification :: IO ()
exampleVerification = do
    let model = exampleModel
    let safety = ltlGlobally (LTLNot (LTLProp "error"))
    
    case verifyLTL model safety of
        Left msg -> putStrLn $ "Safety property holds: " ++ msg
        Right counterExample -> 
            putStrLn $ "Safety property violated. Counter-example: " ++ show counterExample
```

## 📚 理论基础

### 数学基础

LTL基于以下数学基础：

1. **模态逻辑**：LTL作为模态逻辑的扩展
2. **线性时间模型**：时间被建模为线性序列
3. **ω-正则语言**：无限序列的语言理论

### 形式化语义

LTL的形式化语义包括：

1. **Kripke结构**：状态转换系统的形式化模型
2. **路径语义**：基于执行路径的语义解释
3. **时态操作符**：描述时间相关性质的逻辑操作符

### 算法基础

LTL模型检测基于以下算法：

1. **Büchi自动机构造**：将LTL公式转换为自动机
2. **语言包含检查**：检查系统语言是否包含在性质语言中
3. **反例生成**：生成违反性质的执行路径

## 🔗 相关链接

- [LTL模型检测](02-LTL-Model-Checking.md)
- [LTL可满足性](03-LTL-Satisfiability.md)
- [LTL综合](04-LTL-Synthesis.md)
- [计算树逻辑](../02-Computation-Tree-Logic/01-CTL-Syntax-Semantics.md)

---

*本文档提供了线性时态逻辑语法语义的完整介绍，包括形式化定义、Haskell实现和应用示例。*
