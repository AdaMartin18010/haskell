# 模型检测中的时态逻辑

## 📋 概述

时态逻辑是模型检测的核心语言，用于描述系统的动态性质。它提供了一套形式化语言来描述"总是"、"最终"、"直到"等时间概念，使模型检测器能够自动验证系统是否满足这些性质。

## 🎯 核心概念

### 时态逻辑基础

#### 基本时态操作符

```haskell
-- 时态逻辑操作符
data TemporalOperator = 
    Always                    -- 总是 (G)
  | Eventually               -- 最终 (F)
  | Next                     -- 下一个 (X)
  | Until                    -- 直到 (U)
  | Release                  -- 释放 (R)
  | WeakUntil                -- 弱直到 (W)
  deriving (Show)

-- 时态逻辑公式
data TemporalFormula = 
    TTrue
  | TFalse
  | TProp String
  | TNot TemporalFormula
  | TAnd TemporalFormula TemporalFormula
  | TOr TemporalFormula TemporalFormula
  | TImplies TemporalFormula TemporalFormula
  | TAlways TemporalFormula
  | TEventually TemporalFormula
  | TNext TemporalFormula
  | TUntil TemporalFormula TemporalFormula
  | TRelease TemporalFormula TemporalFormula
  deriving (Show)
```

#### 线性时态逻辑 (LTL)

```haskell
-- LTL公式语法
data LTLFormula = 
    LTLTrue
  | LTLFalse
  | LTLProp String
  | LTLNot LTLFormula
  | LTLAnd LTLFormula LTLFormula
  | LTLOr LTLFormula LTLFormula
  | LTLNext LTLFormula
  | LTLUntil LTLFormula LTLFormula
  | LTLRelease LTLFormula LTLFormula
  deriving (Show)

-- LTL派生操作符
ltlFinally :: LTLFormula -> LTLFormula
ltlFinally phi = LTLUntil LTLTrue phi

ltlGlobally :: LTLFormula -> LTLFormula
ltlGlobally phi = LTLNot (LTLUntil LTLTrue (LTLNot phi))

ltlWeakUntil :: LTLFormula -> LTLFormula -> LTLFormula
ltlWeakUntil phi psi = LTLOr (LTLUntil phi psi) (ltlGlobally phi)
```

#### 计算树逻辑 (CTL)

```haskell
-- CTL路径量词
data PathQuantifier = 
    A  -- 对所有路径
  | E  -- 存在路径
  deriving (Show)

-- CTL状态量词
data StateQuantifier = 
    X  -- 下一个
  | F  -- 最终
  | G  -- 总是
  | U  -- 直到
  deriving (Show)

-- CTL公式
data CTLFormula = 
    CTLTrue
  | CTLFalse
  | CTLProp String
  | CTLNot CTLFormula
  | CTLAnd CTLFormula CTLFormula
  | CTLOr CTLFormula CTLFormula
  | CTLNext CTLFormula
  | CTLFinally CTLFormula
  | CTLGlobally CTLFormula
  | CTLUntil CTLFormula CTLFormula
  | CTLForAll CTLFormula  -- A phi
  | CTLExists CTLFormula  -- E phi
  deriving (Show)
```

### 模型检测语义

#### Kripke结构

```haskell
-- Kripke结构定义
data KripkeStructure = KripkeStructure
    { states :: Set String
    , initialStates :: Set String
    , transitions :: Map String (Set String)
    , labeling :: String -> Set String
    }

-- 路径定义
type Path = [String]

-- 生成所有路径
generatePaths :: KripkeStructure -> [Path]
generatePaths ks = 
    concatMap (\s -> generatePathsFrom ks s) (Set.toList $ initialStates ks)

generatePathsFrom :: KripkeStructure -> String -> [Path]
generatePathsFrom ks s = 
    s : concatMap (\s' -> generatePathsFrom ks s') 
                  (Set.toList $ Map.findWithDefault Set.empty s (transitions ks))
```

#### 语义函数

```haskell
-- LTL语义函数
satisfiesLTL :: KripkeStructure -> Path -> Int -> LTLFormula -> Bool
satisfiesLTL ks path i formula = 
    case formula of
        LTLTrue -> True
        LTLFalse -> False
        LTLProp p -> p `Set.member` (labeling ks (path !! i))
        LTLNot phi -> not (satisfiesLTL ks path i phi)
        LTLAnd phi psi -> 
            satisfiesLTL ks path i phi && satisfiesLTL ks path i psi
        LTLOr phi psi -> 
            satisfiesLTL ks path i phi || satisfiesLTL ks path i psi
        LTLNext phi -> 
            if i + 1 < length path 
            then satisfiesLTL ks path (i + 1) phi
            else False
        LTLUntil phi psi -> 
            satisfiesUntilLTL ks path i phi psi
        LTLRelease phi psi -> 
            satisfiesReleaseLTL ks path i phi psi

-- 直到操作符语义
satisfiesUntilLTL :: KripkeStructure -> Path -> Int -> LTLFormula -> LTLFormula -> Bool
satisfiesUntilLTL ks path i phi psi = 
    any (\j -> satisfiesLTL ks path j psi && 
               all (\k -> satisfiesLTL ks path k phi) [i..j-1]) [i..length path - 1]

-- 释放操作符语义
satisfiesReleaseLTL :: KripkeStructure -> Path -> Int -> LTLFormula -> LTLFormula -> Bool
satisfiesReleaseLTL ks path i phi psi = 
    all (\j -> satisfiesLTL ks path j psi || 
               any (\k -> satisfiesLTL ks path k phi) [i..j]) [i..length path - 1]

-- CTL语义函数
satisfiesCTL :: KripkeStructure -> String -> CTLFormula -> Bool
satisfiesCTL ks state formula = 
    case formula of
        CTLTrue -> True
        CTLFalse -> False
        CTLProp p -> p `Set.member` (labeling ks state)
        CTLNot phi -> not (satisfiesCTL ks state phi)
        CTLAnd phi psi -> 
            satisfiesCTL ks state phi && satisfiesCTL ks state psi
        CTLOr phi psi -> 
            satisfiesCTL ks state phi || satisfiesCTL ks state psi
        CTLNext phi -> 
            any (\s' -> satisfiesCTL ks s' phi) 
                (Set.toList $ Map.findWithDefault Set.empty state (transitions ks))
        CTLFinally phi -> 
            satisfiesCTL ks state (CTLOr phi (CTLNext (CTLFinally phi)))
        CTLGlobally phi -> 
            satisfiesCTL ks state (CTLAnd phi (CTLNext (CTLGlobally phi)))
        CTLUntil phi psi -> 
            satisfiesCTL ks state (CTLOr psi (CTLAnd phi (CTLNext (CTLUntil phi psi)))))
        CTLForAll phi -> 
            all (\path -> satisfiesPathCTL ks path 0 phi) 
                (generatePathsFrom ks state)
        CTLExists phi -> 
            any (\path -> satisfiesPathCTL ks path 0 phi) 
                (generatePathsFrom ks state)
```

## 🔧 Haskell实现

### 模型检测器

```haskell
-- 模型检测器
module ModelChecker where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

-- 模型检测状态
data ModelCheckingState = ModelCheckingState
    { visitedStates :: Set String
    , counterExamples :: [Path]
    , verificationResults :: Map String Bool
    }

-- 模型检测器单子
type ModelChecker = State ModelCheckingState

-- 验证LTL公式
verifyLTL :: KripkeStructure -> LTLFormula -> Either String Path
verifyLTL ks formula = 
    case find (not . satisfiesPathLTL ks formula) (generatePaths ks) of
        Just path -> Right path
        Nothing -> Left "Formula is satisfied by all paths"

-- 路径满足性检查
satisfiesPathLTL :: KripkeStructure -> LTLFormula -> Path -> Bool
satisfiesPathLTL ks formula path = 
    all (\i -> satisfiesLTL ks path i formula) [0..length path - 1]

-- 验证CTL公式
verifyCTL :: KripkeStructure -> CTLFormula -> Either String String
verifyCTL ks formula = 
    case find (not . satisfiesCTL ks) (Set.toList $ initialStates ks) of
        Just state -> Right state
        Nothing -> Left "Formula is satisfied by all initial states"
```

### Büchi自动机构造

```haskell
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

## 📊 应用示例

### 互斥协议验证

```haskell
-- 互斥协议模型
mutualExclusionModel :: KripkeStructure
mutualExclusionModel = KripkeStructure
    { states = Set.fromList ["idle1,idle2", "wait1,idle2", "idle1,wait2", "cs1,idle2", "idle1,cs2"]
    , initialStates = Set.singleton "idle1,idle2"
    , transitions = Map.fromList [
        ("idle1,idle2", Set.fromList ["wait1,idle2", "idle1,wait2"]),
        ("wait1,idle2", Set.fromList ["cs1,idle2", "wait1,wait2"]),
        ("idle1,wait2", Set.fromList ["wait1,wait2", "idle1,cs2"]),
        ("cs1,idle2", Set.fromList ["idle1,idle2"]),
        ("idle1,cs2", Set.fromList ["idle1,idle2"]),
        ("wait1,wait2", Set.fromList ["cs1,idle2", "idle1,cs2"])
        ]
    , labeling = \s -> Set.fromList $ words $ map (\c -> if c == ',' then ' ' else c) s
    }

-- 互斥性质
mutualExclusionProperty :: LTLFormula
mutualExclusionProperty = ltlGlobally (LTLNot (LTLAnd (LTLProp "cs1") (LTLProp "cs2")))

-- 无饥饿性质
noStarvationProperty :: LTLFormula
noStarvationProperty = ltlGlobally (LTLImplies (LTLProp "wait1") (ltlFinally (LTLProp "cs1")))

-- 验证示例
verifyMutualExclusion :: IO ()
verifyMutualExclusion = do
    let model = mutualExclusionModel
    
    -- 验证互斥性质
    case verifyLTL model mutualExclusionProperty of
        Left msg -> putStrLn $ "Mutual exclusion holds: " ++ msg
        Right counterExample -> 
            putStrLn $ "Mutual exclusion violated: " ++ show counterExample
    
    -- 验证无饥饿性质
    case verifyLTL model noStarvationProperty of
        Left msg -> putStrLn $ "No starvation holds: " ++ msg
        Right counterExample -> 
            putStrLn $ "No starvation violated: " ++ show counterExample
```

### 交通灯系统验证

```haskell
-- 交通灯系统模型
trafficLightModel :: KripkeStructure
trafficLightModel = KripkeStructure
    { states = Set.fromList ["red", "yellow", "green"]
    , initialStates = Set.singleton "red"
    , transitions = Map.fromList [
        ("red", Set.singleton "green"),
        ("green", Set.singleton "yellow"),
        ("yellow", Set.singleton "red")
        ]
    , labeling = \s -> Set.singleton s
    }

-- 安全性性质：不能同时为红绿
safetyProperty :: LTLFormula
safetyProperty = ltlGlobally (LTLNot (LTLAnd (LTLProp "red") (LTLProp "green")))

-- 活性性质：最终会变绿
livenessProperty :: LTLFormula
livenessProperty = ltlGlobally (ltlFinally (LTLProp "green"))

-- 公平性性质：每个状态都会出现
fairnessProperty :: LTLFormula
fairnessProperty = ltlGlobally (LTLAnd (ltlFinally (LTLProp "red")) 
                                      (LTLAnd (ltlFinally (LTLProp "yellow")) 
                                             (ltlFinally (LTLProp "green"))))
```

## 📚 理论基础

### 数学基础

时态逻辑模型检测基于以下数学基础：

1. **模态逻辑**：时态逻辑作为模态逻辑的扩展
2. **自动机理论**：Büchi自动机和ω-正则语言
3. **图论**：状态转换图和可达性分析

### 算法基础

模型检测算法包括：

1. **状态空间探索**：深度优先搜索和广度优先搜索
2. **符号表示**：使用BDD和SAT求解器
3. **反例生成**：生成违反性质的执行路径

### 复杂度分析

模型检测的复杂度：

1. **LTL模型检测**：PSPACE完全
2. **CTL模型检测**：多项式时间
3. **符号模型检测**：指数时间但实际效率高

## 🔗 相关链接

- [状态空间探索](02-State-Space-Exploration.md)
- [符号模型检测](03-Symbolic-Model-Checking.md)
- [有界模型检测](04-Bounded-Model-Checking.md)
- [时态逻辑理论](../07-Temporal-Logic/)

---

*本文档提供了模型检测中时态逻辑的完整介绍，包括形式化定义、Haskell实现和应用示例。* 