# 形式逻辑 (Formal Logic)

## 概述

形式逻辑是研究推理形式和有效性的数学分支，为计算机科学和人工智能提供理论基础。本文档涵盖从经典逻辑到现代逻辑编程的完整体系。

## 目录结构

### 01-经典逻辑 (Classical-Logic)
- [基本概念](01-Classical-Logic/01-Basic-Concepts.md)
- [命题逻辑](01-Classical-Logic/02-Propositional-Logic.md)
- [一阶逻辑](01-Classical-Logic/03-First-Order-Logic.md)
- [高阶逻辑](01-Classical-Logic/04-Higher-Order-Logic.md)

### 02-模态逻辑 (Modal-Logic)
- [基本概念](02-Modal-Logic/01-Basic-Concepts.md)
- [可能世界语义](02-Modal-Logic/02-Possible-Worlds-Semantics.md)
- [时态逻辑](02-Modal-Logic/03-Temporal-Logic.md)
- [认知逻辑](02-Modal-Logic/04-Epistemic-Logic.md)

### 03-非经典逻辑 (Non-Classical-Logic)
- [直觉逻辑](03-Non-Classical-Logic/01-Intuitionistic-Logic.md)
- [模糊逻辑](03-Non-Classical-Logic/02-Fuzzy-Logic.md)
- [多值逻辑](03-Non-Classical-Logic/03-Many-Valued-Logic.md)
- [线性逻辑](03-Non-Classical-Logic/04-Linear-Logic.md)

### 04-逻辑编程 (Logic-Programming)
- [基本概念](04-Logic-Programming/01-Basic-Concepts.md)
- [Prolog基础](04-Logic-Programming/02-Prolog-Basics.md)
- [约束逻辑编程](04-Logic-Programming/03-Constraint-Logic-Programming.md)
- [答案集编程](04-Logic-Programming/04-Answer-Set-Programming.md)

## 形式化表达

### 逻辑系统的基本结构

```haskell
-- 逻辑系统
data LogicalSystem = LogicalSystem {
    language :: Language,        -- 语言
    semantics :: Semantics,      -- 语义
    proofSystem :: ProofSystem,  -- 证明系统
    metalogic :: Metalogic       -- 元逻辑
}

-- 语言
data Language = Language {
    alphabet :: [Symbol],        -- 字母表
    syntax :: SyntaxRules,       -- 语法规则
    formulas :: [Formula]        -- 公式集
}

-- 语义
data Semantics = Semantics {
    interpretation :: Interpretation,
    satisfaction :: Satisfaction,
    validity :: Validity
}

-- 证明系统
data ProofSystem = ProofSystem {
    axioms :: [Formula],         -- 公理
    rules :: [InferenceRule],    -- 推理规则
    theorems :: [Formula]        -- 定理
}
```

### 经典逻辑的形式化

```haskell
-- 命题逻辑
data PropositionalFormula = 
    Atom String                  -- 原子命题
  | Not PropositionalFormula     -- 否定
  | And PropositionalFormula PropositionalFormula  -- 合取
  | Or PropositionalFormula PropositionalFormula   -- 析取
  | Implies PropositionalFormula PropositionalFormula  -- 蕴含
  | Iff PropositionalFormula PropositionalFormula  -- 等价

-- 一阶逻辑
data FirstOrderFormula = 
    Predicate String [Term]      -- 谓词
  | Equal Term Term              -- 相等
  | Not FirstOrderFormula        -- 否定
  | And FirstOrderFormula FirstOrderFormula  -- 合取
  | Or FirstOrderFormula FirstOrderFormula   -- 析取
  | Implies FirstOrderFormula FirstOrderFormula  -- 蕴含
  | ForAll String FirstOrderFormula  -- 全称
  | Exists String FirstOrderFormula  -- 存在

-- 项
data Term = 
    Variable String              -- 变量
  | Constant String              -- 常量
  | Function String [Term]       -- 函数
```

### 模态逻辑的形式化

```haskell
-- 模态公式
data ModalFormula = 
    Atom String                  -- 原子命题
  | Not ModalFormula             -- 否定
  | And ModalFormula ModalFormula  -- 合取
  | Or ModalFormula ModalFormula   -- 析取
  | Implies ModalFormula ModalFormula  -- 蕴含
  | Necessarily ModalFormula     -- 必然
  | Possibly ModalFormula        -- 可能

-- 可能世界模型
data KripkeModel = KripkeModel {
    worlds :: [World],           -- 可能世界集
    accessibility :: World -> [World],  -- 可达关系
    valuation :: World -> String -> Bool  -- 赋值函数
}

-- 模态语义
modalSatisfaction :: KripkeModel -> World -> ModalFormula -> Bool
modalSatisfaction model world formula = case formula of
    Atom p -> valuation model world p
    Not phi -> not (modalSatisfaction model world phi)
    And phi psi -> modalSatisfaction model world phi && 
                   modalSatisfaction model world psi
    Or phi psi -> modalSatisfaction model world phi || 
                  modalSatisfaction model world psi
    Implies phi psi -> not (modalSatisfaction model world phi) || 
                       modalSatisfaction model world psi
    Necessarily phi -> all (\w -> modalSatisfaction model w phi) 
                           (accessibility model world)
    Possibly phi -> any (\w -> modalSatisfaction model w phi) 
                        (accessibility model world)
```

### 非经典逻辑的形式化

```haskell
-- 直觉逻辑
data IntuitionisticFormula = 
    Atom String
  | Not IntuitionisticFormula
  | And IntuitionisticFormula IntuitionisticFormula
  | Or IntuitionisticFormula IntuitionisticFormula
  | Implies IntuitionisticFormula IntuitionisticFormula

-- 模糊逻辑
data FuzzyFormula = 
    Atom String
  | Not FuzzyFormula
  | And FuzzyFormula FuzzyFormula
  | Or FuzzyFormula FuzzyFormula
  | Implies FuzzyFormula FuzzyFormula

-- 模糊语义
fuzzySatisfaction :: FuzzyInterpretation -> FuzzyFormula -> Double
fuzzySatisfaction interp formula = case formula of
    Atom p -> interp p
    Not phi -> 1.0 - fuzzySatisfaction interp phi
    And phi psi -> min (fuzzySatisfaction interp phi) 
                      (fuzzySatisfaction interp psi)
    Or phi psi -> max (fuzzySatisfaction interp phi) 
                     (fuzzySatisfaction interp psi)
    Implies phi psi -> min 1.0 (1.0 - fuzzySatisfaction interp phi + 
                                   fuzzySatisfaction interp psi)
```

### 逻辑编程的形式化

```haskell
-- Horn子句
data HornClause = 
    Fact Atom                    -- 事实
  | Rule Atom [Atom]             -- 规则
  | Goal [Atom]                  -- 目标

-- 逻辑程序
data LogicProgram = LogicProgram {
    facts :: [Atom],             -- 事实集
    rules :: [Rule],             -- 规则集
    goals :: [Goal]              -- 目标集
}

-- 证明树
data ProofTree = 
    Leaf Atom                    -- 叶节点
  | Node Atom [ProofTree]        -- 内部节点

-- 统一算法
unify :: Term -> Term -> Maybe Substitution
unify (Variable x) t = Just [(x, t)]
unify t (Variable x) = Just [(x, t)]
unify (Constant c1) (Constant c2) = 
    if c1 == c2 then Just [] else Nothing
unify (Function f1 args1) (Function f2 args2) =
    if f1 == f2 && length args1 == length args2
    then foldr combine (Just []) (zip args1 args2)
    else Nothing
  where
    combine (t1, t2) acc = do
        sub1 <- acc
        sub2 <- unify (applySubstitution sub1 t1) 
                      (applySubstitution sub1 t2)
        return (sub1 ++ sub2)
```

## 逻辑系统性质

### 1. 可靠性 (Soundness)

```haskell
-- 可靠性：所有可证明的公式都是有效的
isSound :: LogicalSystem -> Bool
isSound system = all (\theorem -> 
    isValid (semantics system) theorem) 
    (theorems (proofSystem system))
```

### 2. 完全性 (Completeness)

```haskell
-- 完全性：所有有效的公式都是可证明的
isComplete :: LogicalSystem -> Bool
isComplete system = all (\valid -> 
    isProvable (proofSystem system) valid) 
    (validFormulas (semantics system))
```

### 3. 一致性 (Consistency)

```haskell
-- 一致性：不能同时证明一个公式和它的否定
isConsistent :: LogicalSystem -> Bool
isConsistent system = 
    not (any (\theorem -> 
        isProvable (proofSystem system) (Not theorem)) 
        (theorems (proofSystem system)))
```

## 应用示例

### 1. 自动定理证明

```haskell
-- 归结原理
resolution :: [Clause] -> [Clause]
resolution clauses = 
    let newClauses = [resolve c1 c2 | c1 <- clauses, c2 <- clauses, c1 /= c2]
    in clauses ++ filter (not . isTautology) newClauses

-- 归结证明
resolutionProof :: [Clause] -> Clause -> Bool
resolutionProof premises goal = 
    let allClauses = premises ++ [negateClause goal]
        saturated = iterate resolution allClauses
    in any (elem emptyClause) saturated
```

### 2. 模型检测

```haskell
-- 模型检测算法
modelCheck :: KripkeModel -> ModalFormula -> Bool
modelCheck model formula = 
    all (\world -> modalSatisfaction model world formula) 
        (worlds model)

-- 时态逻辑模型检测
temporalModelCheck :: TransitionSystem -> TemporalFormula -> Bool
temporalModelCheck system formula = 
    all (\state -> temporalSatisfaction system state formula) 
        (initialStates system)
```

## 与理论层的关系

形式逻辑为理论层提供：

1. **语义基础**：编程语言语义的形式化基础
2. **类型理论**：类型系统的逻辑基础
3. **验证方法**：程序验证的逻辑方法
4. **推理系统**：自动推理的理论基础

## 与具体科学层的关系

形式逻辑指导具体科学层的应用：

1. **人工智能**：知识表示和推理的逻辑基础
2. **软件工程**：形式化验证的逻辑方法
3. **数据库**：查询语言的逻辑语义
4. **编译器**：程序分析的逻辑框架

## 学习路径

1. **经典逻辑**：掌握基本的逻辑推理
2. **模态逻辑**：理解可能性和必然性
3. **非经典逻辑**：探索不同的逻辑系统
4. **逻辑编程**：应用逻辑于程序设计

## 相关链接

- [形式科学层主索引](../README.md)
- [数学基础](../01-Mathematics/README.md)
- [范畴论](../03-Category-Theory/README.md)
- [类型论](../04-Type-Theory/README.md)
- [理论层](../../03-Theory/README.md) 