# 形式逻辑 (Formal Logic)

## 概述

形式逻辑研究推理的有效性和形式结构，是哲学和数学的基础。本节将从形式化角度分析不同的逻辑系统，并用Haskell实现相关的概念和证明。

## 主要逻辑系统

### 1. 命题逻辑 (Propositional Logic)

命题逻辑研究命题之间的逻辑关系。

#### 形式化定义

```haskell
-- 命题逻辑的形式化表达
class PropositionalLogic a where
  -- 命题
  proposition :: a -> String
  -- 真值
  truthValue :: a -> Bool
  -- 逻辑连接词
  logicalConnective :: a -> Connective

-- 逻辑连接词
data Connective = 
  And
  | Or
  | Not
  | Implies
  | Iff
  deriving (Show, Eq)

-- 命题
data Proposition = 
  Atomic String Bool
  | Compound Connective [Proposition]
  deriving (Show, Eq)

-- 命题逻辑实例
instance PropositionalLogic Proposition where
  proposition (Atomic name _) = name
  proposition (Compound conn props) = 
    show conn ++ "(" ++ unwords (map proposition props) ++ ")"
  
  truthValue (Atomic _ value) = value
  truthValue (Compound conn props) = 
    case conn of
      And -> all truthValue props
      Or -> any truthValue props
      Not -> not (truthValue (head props))
      Implies -> not (truthValue (head props)) || truthValue (props !! 1)
      Iff -> truthValue (head props) == truthValue (props !! 1)

-- 逻辑连接词实例
instance Show Connective where
  show And = "∧"
  show Or = "∨"
  show Not = "¬"
  show Implies = "→"
  show Iff = "↔"

-- 命题逻辑运算
class PropositionalOperations a where
  -- 合取
  conjunction :: a -> a -> a
  -- 析取
  disjunction :: a -> a -> a
  -- 否定
  negation :: a -> a
  -- 蕴含
  implication :: a -> a -> a
  -- 等价
  equivalence :: a -> a -> a

-- 命题逻辑运算实例
instance PropositionalOperations Proposition where
  conjunction p1 p2 = Compound And [p1, p2]
  disjunction p1 p2 = Compound Or [p1, p2]
  negation p = Compound Not [p]
  implication p1 p2 = Compound Implies [p1, p2]
  equivalence p1 p2 = Compound Iff [p1, p2]

-- 示例：命题逻辑
exampleProposition :: Proposition
exampleProposition = 
  implication 
    (conjunction (Atomic "P" True) (Atomic "Q" True))
    (disjunction (Atomic "R" False) (Atomic "S" True))
```

#### 真值表

```haskell
-- 真值表生成
generateTruthTable :: [String] -> [Proposition] -> [[Bool]]
generateTruthTable variables propositions = 
  let combinations = generateCombinations (length variables)
  in map (\combo -> map (\prop -> evaluateWithValues prop (zip variables combo))) propositions
  where
    generateCombinations n = 
      if n == 0 then [[]]
      else [True:combo | combo <- generateCombinations (n-1)] ++
           [False:combo | combo <- generateCombinations (n-1)]
    
    evaluateWithValues :: Proposition -> [(String, Bool)] -> Bool
    evaluateWithValues (Atomic name _) values = 
      case lookup name values of
        Just value -> value
        Nothing -> False
    evaluateWithValues (Compound conn props) values = 
      case conn of
        And -> all (\p -> evaluateWithValues p values) props
        Or -> any (\p -> evaluateWithValues p values) props
        Not -> not (evaluateWithValues (head props) values)
        Implies -> not (evaluateWithValues (head props) values) || 
                   evaluateWithValues (props !! 1) values
        Iff -> evaluateWithValues (head props) values == 
               evaluateWithValues (props !! 1) values

-- 示例：真值表
exampleTruthTable :: [[Bool]]
exampleTruthTable = 
  generateTruthTable ["P", "Q"] [
    Atomic "P" True,
    Atomic "Q" True,
    Compound And [Atomic "P" True, Atomic "Q" True]
  ]
```

### 2. 谓词逻辑 (Predicate Logic)

谓词逻辑研究量化和谓词的逻辑。

#### 形式化定义

```haskell
-- 谓词逻辑的形式化表达
class PredicateLogic a where
  -- 谓词
  predicate :: a -> String
  -- 变量
  variables :: a -> [String]
  -- 量词
  quantifiers :: a -> [Quantifier]

-- 量词类型
data Quantifier = 
  ForAll String  -- 全称量词
  | Exists String  -- 存在量词
  deriving (Show, Eq)

-- 谓词公式
data PredicateFormula = 
  Predicate String [String]  -- 谓词符号和参数
  | Quantified Quantifier PredicateFormula
  | Logical Compound Connective [PredicateFormula]
  deriving (Show, Eq)

-- 谓词逻辑实例
instance PredicateLogic PredicateFormula where
  predicate (Predicate name _) = name
  predicate (Quantified _ formula) = predicate formula
  predicate (Logical _ formulas) = 
    "compound(" ++ unwords (map predicate formulas) ++ ")"
  
  variables (Predicate _ args) = args
  variables (Quantified (ForAll var) formula) = 
    var : variables formula
  variables (Quantified (Exists var) formula) = 
    var : variables formula
  variables (Logical _ formulas) = 
    concatMap variables formulas
  
  quantifiers (Predicate _ _) = []
  quantifiers (Quantified q formula) = 
    q : quantifiers formula
  quantifiers (Logical _ formulas) = 
    concatMap quantifiers formulas

-- 谓词逻辑运算
class PredicateOperations a where
  -- 全称量化
  universalQuantification :: String -> a -> a
  -- 存在量化
  existentialQuantification :: String -> a -> a
  -- 谓词应用
  predicateApplication :: String -> [String] -> a

-- 谓词逻辑运算实例
instance PredicateOperations PredicateFormula where
  universalQuantification var formula = 
    Quantified (ForAll var) formula
  existentialQuantification var formula = 
    Quantified (Exists var) formula
  predicateApplication name args = 
    Predicate name args

-- 示例：谓词逻辑
examplePredicate :: PredicateFormula
examplePredicate = 
  universalQuantification "x" 
    (implication 
      (predicateApplication "Human" ["x"])
      (predicateApplication "Mortal" ["x"]))
  where
    implication p1 p2 = Logical Compound Implies [p1, p2]
```

#### 量词推理

```haskell
-- 量词推理规则
class QuantifierInference a where
  -- 全称实例化
  universalInstantiation :: a -> String -> String -> a
  -- 存在概括
  existentialGeneralization :: a -> String -> String -> a
  -- 全称概括
  universalGeneralization :: a -> String -> a
  -- 存在实例化
  existentialInstantiation :: a -> String -> a

-- 量词推理实例
instance QuantifierInference PredicateFormula where
  universalInstantiation formula var constant = 
    substituteVariable formula var constant
  
  existentialGeneralization formula var constant = 
    substituteVariable formula constant var
  
  universalGeneralization formula var = 
    Quantified (ForAll var) formula
  
  existentialInstantiation formula var = 
    Quantified (Exists var) formula

-- 变量替换
substituteVariable :: PredicateFormula -> String -> String -> PredicateFormula
substituteVariable (Predicate name args) old new = 
  Predicate name (map (\arg -> if arg == old then new else arg) args)
substituteVariable (Quantified q formula) old new = 
  Quantified q (substituteVariable formula old new)
substituteVariable (Logical conn formulas) old new = 
  Logical conn (map (\f -> substituteVariable f old new) formulas)

-- 示例：量词推理
exampleInference :: PredicateFormula
exampleInference = 
  universalInstantiation 
    (universalQuantification "x" 
      (predicateApplication "Human" ["x"]))
    "x" "Socrates"
```

### 3. 模态逻辑 (Modal Logic)

模态逻辑研究必然性和可能性的逻辑。

#### 形式化定义

```haskell
-- 模态逻辑的形式化表达
class ModalLogic a where
  -- 必然性
  necessity :: a -> a
  -- 可能性
  possibility :: a -> a
  -- 模态公式
  modalFormula :: a -> String

-- 模态算子
data ModalOperator = 
  Necessity
  | Possibility
  deriving (Show, Eq)

-- 模态公式
data ModalFormula = 
  Modal Atomic ModalOperator ModalFormula
  | Propositional Proposition
  deriving (Show, Eq)

-- 模态逻辑实例
instance ModalLogic ModalFormula where
  necessity formula = Modal Atomic Necessity formula
  possibility formula = Modal Atomic Possibility formula
  modalFormula (Modal _ op formula) = 
    show op ++ "(" ++ modalFormula formula ++ ")"
  modalFormula (Propositional prop) = proposition prop

-- 模态算子实例
instance Show ModalOperator where
  show Necessity = "□"
  show Possibility = "◇"

-- 模态逻辑运算
class ModalOperations a where
  -- 必然性运算
  necessary :: a -> a
  -- 可能性运算
  possible :: a -> a
  -- 模态等价
  modalEquivalence :: a -> a -> a

-- 模态逻辑运算实例
instance ModalOperations ModalFormula where
  necessary = necessity
  possible = possibility
  modalEquivalence f1 f2 = 
    Logical Compound Iff [f1, f2]

-- 示例：模态逻辑
exampleModal :: ModalFormula
exampleModal = 
  implication 
    (necessary (Propositional (Atomic "P" True)))
    (possible (Propositional (Atomic "P" True)))
  where
    implication f1 f2 = Logical Compound Implies [f1, f2]
```

#### 可能世界语义

```haskell
-- 可能世界语义
data PossibleWorld = PossibleWorld {
  worldId :: String,
  propositions :: [(String, Bool)],
  accessibility :: [String]  -- 可通达的世界
} deriving (Show, Eq)

-- 模态模型
data ModalModel = ModalModel {
  worlds :: [PossibleWorld],
  actualWorld :: String
} deriving (Show, Eq)

-- 模态语义
class ModalSemantics a where
  -- 在可能世界中为真
  trueInWorld :: a -> PossibleWorld -> Bool
  -- 在所有可通达世界中为真
  trueInAllAccessible :: a -> PossibleWorld -> [PossibleWorld] -> Bool
  -- 在某个可通达世界中为真
  trueInSomeAccessible :: a -> PossibleWorld -> [PossibleWorld] -> Bool

-- 模态语义实例
instance ModalSemantics ModalFormula where
  trueInWorld (Modal _ Necessity formula) world = 
    -- 在所有可通达世界中为真
    True  -- 简化实现
  trueInWorld (Modal _ Possibility formula) world = 
    -- 在某个可通达世界中为真
    True  -- 简化实现
  trueInWorld (Propositional prop) world = 
    case lookup (proposition prop) (propositions world) of
      Just value -> value
      Nothing -> False
  
  trueInAllAccessible formula world accessibleWorlds = 
    all (\w -> trueInWorld formula w) accessibleWorlds
  
  trueInSomeAccessible formula world accessibleWorlds = 
    any (\w -> trueInWorld formula w) accessibleWorlds

-- 示例：可能世界
exampleWorld :: PossibleWorld
exampleWorld = PossibleWorld {
  worldId = "w1",
  propositions = [
    ("P", True),
    ("Q", False),
    ("R", True)
  ],
  accessibility = ["w2", "w3"]
}

-- 示例：模态模型
exampleModel :: ModalModel
exampleModel = ModalModel {
  worlds = [exampleWorld],
  actualWorld = "w1"
}
```

### 4. 时序逻辑 (Temporal Logic)

时序逻辑研究时间和变化的逻辑。

#### 形式化定义

```haskell
-- 时序逻辑的形式化表达
class TemporalLogic a where
  -- 将来
  future :: a -> a
  -- 过去
  past :: a -> a
  -- 总是
  always :: a -> a
  -- 最终
  eventually :: a -> a

-- 时序算子
data TemporalOperator = 
  Future
  | Past
  | Always
  | Eventually
  | Until
  | Since
  deriving (Show, Eq)

-- 时序公式
data TemporalFormula = 
  Temporal Atomic TemporalOperator TemporalFormula
  | TemporalBinary TemporalOperator TemporalFormula TemporalFormula
  | TemporalPropositional Proposition
  deriving (Show, Eq)

-- 时序逻辑实例
instance TemporalLogic TemporalFormula where
  future formula = Temporal Atomic Future formula
  past formula = Temporal Atomic Past formula
  always formula = Temporal Atomic Always formula
  eventually formula = Temporal Atomic Eventually formula

-- 时序算子实例
instance Show TemporalOperator where
  show Future = "F"
  show Past = "P"
  show Always = "G"
  show Eventually = "F"
  show Until = "U"
  show Since = "S"

-- 时序逻辑运算
class TemporalOperations a where
  -- 将来运算
  next :: a -> a
  -- 过去运算
  previous :: a -> a
  -- 直到运算
  until :: a -> a -> a
  -- 自从运算
  since :: a -> a -> a

-- 时序逻辑运算实例
instance TemporalOperations TemporalFormula where
  next = future
  previous = past
  until f1 f2 = TemporalBinary Until f1 f2
  since f1 f2 = TemporalBinary Since f1 f2

-- 示例：时序逻辑
exampleTemporal :: TemporalFormula
exampleTemporal = 
  until 
    (TemporalPropositional (Atomic "P" True))
    (TemporalPropositional (Atomic "Q" True))
```

#### 线性时间语义

```haskell
-- 时间点
data TimePoint = TimePoint {
  time :: Int,
  propositions :: [(String, Bool)]
} deriving (Show, Eq)

-- 时间序列
data TimeSequence = TimeSequence {
  points :: [TimePoint],
  current :: Int
} deriving (Show, Eq)

-- 时序语义
class TemporalSemantics a where
  -- 在时间点中为真
  trueAtTime :: a -> TimePoint -> Bool
  -- 在时间序列中为真
  trueInSequence :: a -> TimeSequence -> Bool

-- 时序语义实例
instance TemporalSemantics TemporalFormula where
  trueAtTime (Temporal _ Future formula) timePoint = 
    -- 在将来某个时间点为真
    True  -- 简化实现
  trueAtTime (Temporal _ Past formula) timePoint = 
    -- 在过去某个时间点为真
    True  -- 简化实现
  trueAtTime (Temporal _ Always formula) timePoint = 
    -- 在所有时间点为真
    True  -- 简化实现
  trueAtTime (Temporal _ Eventually formula) timePoint = 
    -- 在某个时间点为真
    True  -- 简化实现
  trueAtTime (TemporalBinary _ f1 f2) timePoint = 
    trueAtTime f1 timePoint && trueAtTime f2 timePoint
  trueAtTime (TemporalPropositional prop) timePoint = 
    case lookup (proposition prop) (propositions timePoint) of
      Just value -> value
      Nothing -> False
  
  trueInSequence formula sequence = 
    trueAtTime formula (points sequence !! current sequence)

-- 示例：时间点
exampleTimePoint :: TimePoint
exampleTimePoint = TimePoint {
  time = 0,
  propositions = [
    ("P", True),
    ("Q", False)
  ]
}

-- 示例：时间序列
exampleTimeSequence :: TimeSequence
exampleTimeSequence = TimeSequence {
  points = [exampleTimePoint],
  current = 0
}
```

### 5. 非单调逻辑 (Non-monotonic Logic)

非单调逻辑研究可修正的推理。

#### 形式化定义

```haskell
-- 非单调逻辑的形式化表达
class NonMonotonicLogic a where
  -- 默认推理
  defaultInference :: a -> a -> Bool
  -- 异常处理
  exceptionHandling :: a -> [a] -> Bool
  -- 可修正性
  revisability :: a -> a -> Bool

-- 默认规则
data DefaultRule = DefaultRule {
  premise :: String,
  conclusion :: String,
  exceptions :: [String]
} deriving (Show, Eq)

-- 非单调推理
data NonMonotonicInference = NonMonotonicInference {
  rules :: [DefaultRule],
  facts :: [String],
  conclusions :: [String]
} deriving (Show, Eq)

-- 非单调逻辑实例
instance NonMonotonicLogic NonMonotonicInference where
  defaultInference inference rule = 
    premise rule `elem` facts inference &&
    not (any (\exc -> exc `elem` facts inference) (exceptions rule))
  
  exceptionHandling inference exceptions = 
    not (any (\exc -> exc `elem` facts inference) exceptions)
  
  revisability inference newFact = 
    newFact `notElem` facts inference

-- 默认推理系统
class DefaultReasoning a where
  -- 应用默认规则
  applyDefaultRule :: a -> DefaultRule -> a
  -- 检查异常
  checkException :: a -> DefaultRule -> Bool
  -- 修正推理
  reviseInference :: a -> String -> a

-- 默认推理实例
instance DefaultReasoning NonMonotonicInference where
  applyDefaultRule inference rule = 
    if defaultInference inference rule && 
       not (checkException inference rule)
    then inference { conclusions = conclusion rule : conclusions inference }
    else inference
  
  checkException inference rule = 
    any (\exc -> exc `elem` facts inference) (exceptions rule)
  
  reviseInference inference newFact = 
    inference { 
      facts = newFact : facts inference,
      conclusions = filter (\c -> c /= conclusion (head rules inference)) (conclusions inference)
    }

-- 示例：默认推理
exampleDefault :: DefaultRule
exampleDefault = DefaultRule {
  premise = "鸟(x)",
  conclusion = "飞(x)",
  exceptions = ["企鹅(x)", "鸵鸟(x)"]
}

-- 示例：非单调推理
exampleNonMonotonic :: NonMonotonicInference
exampleNonMonotonic = NonMonotonicInference {
  rules = [exampleDefault],
  facts = ["鸟(企鹅)"],
  conclusions = []
}
```

## 形式化证明

### 逻辑推理的形式化证明

```haskell
-- 推理规则
data InferenceRule = 
  ModusPonens
  | ModusTollens
  | HypotheticalSyllogism
  | DisjunctiveSyllogism
  | Conjunction
  | Simplification
  | Addition
  deriving (Show, Eq)

-- 证明步骤
data ProofStep = ProofStep {
  stepNumber :: Int,
  formula :: String,
  rule :: InferenceRule,
  premises :: [Int]
} deriving (Show, Eq)

-- 证明
data Proof = Proof {
  steps :: [ProofStep],
  conclusion :: String
} deriving (Show, Eq)

-- 证明验证
validateProof :: Proof -> Bool
validateProof proof = 
  all validateStep (steps proof) &&
  conclusion proof == formula (last (steps proof))

-- 步骤验证
validateStep :: ProofStep -> Bool
validateStep step = 
  case rule step of
    ModusPonens -> length (premises step) == 2
    ModusTollens -> length (premises step) == 2
    HypotheticalSyllogism -> length (premises step) == 2
    DisjunctiveSyllogism -> length (premises step) == 2
    Conjunction -> length (premises step) == 2
    Simplification -> length (premises step) == 1
    Addition -> length (premises step) == 1

-- 示例：证明
exampleProof :: Proof
exampleProof = Proof {
  steps = [
    ProofStep 1 "P→Q" ModusPonens [],
    ProofStep 2 "P" ModusPonens [],
    ProofStep 3 "Q" ModusPonens [1, 2]
  ],
  conclusion = "Q"
}
```

### 逻辑系统的一致性

```haskell
-- 逻辑系统
data LogicalSystem = LogicalSystem {
  axioms :: [String],
  rules :: [InferenceRule],
  theorems :: [String]
} deriving (Show, Eq)

-- 一致性检查
checkConsistency :: LogicalSystem -> Bool
checkConsistency system = 
  not (any (\theorem -> theorem == "⊥") (theorems system))

-- 完备性检查
checkCompleteness :: LogicalSystem -> [String] -> Bool
checkCompleteness system formulas = 
  all (\formula -> formula `elem` theorems system) formulas

-- 示例：逻辑系统
exampleSystem :: LogicalSystem
exampleSystem = LogicalSystem {
  axioms = [
    "P→(Q→P)",
    "(P→(Q→R))→((P→Q)→(P→R))",
    "(¬P→¬Q)→(Q→P)"
  ],
  rules = [ModusPonens],
  theorems = [
    "P→(Q→P)",
    "(P→(Q→R))→((P→Q)→(P→R))",
    "(¬P→¬Q)→(Q→P)"
  ]
}
```

## 应用与意义

### 在计算机科学中的应用

```haskell
-- 程序验证的逻辑基础
class ProgramVerification a where
  -- 前置条件
  precondition :: a -> String
  -- 后置条件
  postcondition :: a -> String
  -- 程序正确性
  correctness :: a -> Bool

-- 程序规范
data ProgramSpecification = ProgramSpecification {
  program :: String,
  precondition :: String,
  postcondition :: String,
  invariants :: [String]
} deriving (Show, Eq)

instance ProgramVerification ProgramSpecification where
  precondition = precondition
  postcondition = postcondition
  correctness spec = 
    length (precondition spec) > 0 &&
    length (postcondition spec) > 0

-- 示例：程序规范
exampleSpec :: ProgramSpecification
exampleSpec = ProgramSpecification {
  program = "x := x + 1",
  precondition = "x >= 0",
  postcondition = "x > 0",
  invariants = ["x >= 0"]
}
```

### 在人工智能中的应用

```haskell
-- 知识表示的逻辑基础
class KnowledgeRepresentation a where
  -- 知识表示
  representation :: a -> String
  -- 推理规则
  inferenceRules :: a -> [InferenceRule]
  -- 知识一致性
  consistency :: a -> Bool

-- 知识库
data KnowledgeBase = KnowledgeBase {
  facts :: [String],
  rules :: [DefaultRule],
  queries :: [String]
} deriving (Show, Eq)

instance KnowledgeRepresentation KnowledgeBase where
  representation kb = 
    "Facts: " ++ show (facts kb) ++ 
    "\nRules: " ++ show (rules kb)
  inferenceRules kb = [ModusPonens, ModusTollens]
  consistency kb = 
    not (any (\fact -> fact == "⊥") (facts kb))

-- 示例：知识库
exampleKB :: KnowledgeBase
exampleKB = KnowledgeBase {
  facts = [
    "鸟(企鹅)",
    "企鹅(企鹅)"
  ],
  rules = [exampleDefault],
  queries = [
    "飞(企鹅)?"
  ]
}
```

## 总结

形式逻辑为推理提供了严格的基础：

1. **命题逻辑**研究命题间的逻辑关系
2. **谓词逻辑**研究量化和谓词的逻辑
3. **模态逻辑**研究必然性和可能性
4. **时序逻辑**研究时间和变化的逻辑
5. **非单调逻辑**研究可修正的推理

通过Haskell的形式化实现，我们可以：
- 精确表达不同逻辑系统的核心概念
- 验证各种推理规则的有效性
- 分析不同逻辑在计算机科学中的应用
- 为人工智能提供逻辑基础

这种多表征的方式不仅有助于理解逻辑的本质，也为计算机科学和人工智能提供了坚实的理论基础。 