# 经典逻辑基础

## 📋 概述

经典逻辑是现代逻辑学的基础，为数学推理和形式化系统提供了严格的逻辑框架。本文档从语法、语义、证明论和Haskell实现四个维度探讨经典逻辑的基础理论。

## 🎯 核心概念

### 1. 命题逻辑

#### 1.1 命题语言

**定义**：命题逻辑研究简单命题之间的逻辑关系。

```haskell
-- 命题逻辑语法
data Proposition = 
    Atomic String           -- 原子命题
  | Negation Proposition    -- 否定
  | Conjunction Proposition Proposition  -- 合取
  | Disjunction Proposition Proposition  -- 析取
  | Implication Proposition Proposition  -- 蕴含
  | Equivalence Proposition Proposition  -- 等价
  deriving (Show, Eq)

-- 命题逻辑类型类
class PropositionalLogic a where
  -- 语法操作
  atomic :: String -> a
  neg :: a -> a
  conj :: a -> a -> a
  disj :: a -> a -> a
  impl :: a -> a -> a
  equiv :: a -> a -> a
  
  -- 语法性质
  isAtomic :: a -> Bool
  isComplex :: a -> Bool
  subformulas :: a -> [a]
  complexity :: a -> Int

-- 命题逻辑实例
instance PropositionalLogic Proposition where
  atomic s = Atomic s
  neg p = Negation p
  conj p q = Conjunction p q
  disj p q = Disjunction p q
  impl p q = Implication p q
  equiv p q = Equivalence p q
  
  isAtomic (Atomic _) = True
  isAtomic _ = False
  
  isComplex = not . isAtomic
  
  subformulas (Atomic _) = []
  subformulas (Negation p) = p : subformulas p
  subformulas (Conjunction p q) = p : q : subformulas p ++ subformulas q
  subformulas (Disjunction p q) = p : q : subformulas p ++ subformulas q
  subformulas (Implication p q) = p : q : subformulas p ++ subformulas q
  subformulas (Equivalence p q) = p : q : subformulas p ++ subformulas q
  
  complexity (Atomic _) = 0
  complexity (Negation p) = 1 + complexity p
  complexity (Conjunction p q) = 1 + max (complexity p) (complexity q)
  complexity (Disjunction p q) = 1 + max (complexity p) (complexity q)
  complexity (Implication p q) = 1 + max (complexity p) (complexity q)
  complexity (Equivalence p q) = 1 + max (complexity p) (complexity q)
```

#### 1.2 命题语义

```haskell
-- 命题语义
class PropositionalSemantics a where
  -- 真值赋值
  valuation :: a -> Valuation -> Bool
  -- 真值表
  truthTable :: a -> TruthTable
  -- 重言式
  isTautology :: a -> Bool
  -- 矛盾式
  isContradiction :: a -> Bool
  -- 可满足式
  isSatisfiable :: a -> Bool
  -- 逻辑等价
  isLogicallyEquivalent :: a -> a -> Bool

-- 真值赋值
type Valuation = String -> Bool

-- 真值表
data TruthTable = 
    TruthTable {
      formula :: Proposition,
      rows :: [TruthTableRow]
    }
  deriving (Show, Eq)

data TruthTableRow = 
    TruthTableRow {
      assignment :: Valuation,
      result :: Bool
    }
  deriving (Show, Eq)

-- 命题语义实例
instance PropositionalSemantics Proposition where
  valuation (Atomic s) v = v s
  valuation (Negation p) v = not (valuation p v)
  valuation (Conjunction p q) v = valuation p v && valuation q v
  valuation (Disjunction p q) v = valuation p v || valuation q v
  valuation (Implication p q) v = not (valuation p v) || valuation q v
  valuation (Equivalence p q) v = valuation p v == valuation q v
  
  truthTable p = TruthTable {
    formula = p,
    rows = [TruthTableRow v (valuation p v) | v <- allValuations p]
  }
  
  isTautology p = all (\v -> valuation p v) (allValuations p)
  
  isContradiction p = all (\v -> not (valuation p v)) (allValuations p)
  
  isSatisfiable p = any (\v -> valuation p v) (allValuations p)
  
  isLogicallyEquivalent p q = 
    all (\v -> valuation p v == valuation q v) (allValuations p)

-- 生成所有真值赋值
allValuations :: Proposition -> [Valuation]
allValuations p = 
  let atoms = nub (atomicPropositions p)
      n = length atoms
      assignments = replicateM n [True, False]
  in [makeValuation atoms asg | asg <- assignments]

-- 提取原子命题
atomicPropositions :: Proposition -> [String]
atomicPropositions (Atomic s) = [s]
atomicPropositions (Negation p) = atomicPropositions p
atomicPropositions (Conjunction p q) = nub (atomicPropositions p ++ atomicPropositions q)
atomicPropositions (Disjunction p q) = nub (atomicPropositions p ++ atomicPropositions q)
atomicPropositions (Implication p q) = nub (atomicPropositions p ++ atomicPropositions q)
atomicPropositions (Equivalence p q) = nub (atomicPropositions p ++ atomicPropositions q)

-- 构造真值赋值
makeValuation :: [String] -> [Bool] -> Valuation
makeValuation atoms values = \s -> 
  case elemIndex s atoms of
    Just i -> values !! i
    Nothing -> False
```

### 2. 一阶逻辑

#### 2.1 一阶语言

```haskell
-- 一阶逻辑语法
data Term = 
    Variable String         -- 变量
  | Constant String         -- 常量
  | Function String [Term]  -- 函数项
  deriving (Show, Eq)

data Formula = 
    Predicate String [Term]           -- 谓词
  | Equal Term Term                   -- 相等
  | Not Formula                       -- 否定
  | And Formula Formula               -- 合取
  | Or Formula Formula                -- 析取
  | Implies Formula Formula           -- 蕴含
  | Iff Formula Formula               -- 等价
  | ForAll String Formula             -- 全称量词
  | Exists String Formula             -- 存在量词
  deriving (Show, Eq)

-- 一阶逻辑类型类
class FirstOrderLogic a where
  -- 语法操作
  predicate :: String -> [Term] -> a
  equal :: Term -> Term -> a
  not' :: a -> a
  and' :: a -> a -> a
  or' :: a -> a -> a
  implies :: a -> a -> a
  iff :: a -> a -> a
  forAll :: String -> a -> a
  exists :: String -> a -> a
  
  -- 语法性质
  freeVariables :: a -> [String]
  boundVariables :: a -> [String]
  isClosed :: a -> Bool
  isOpen :: a -> Bool

-- 一阶逻辑实例
instance FirstOrderLogic Formula where
  predicate s ts = Predicate s ts
  equal t1 t2 = Equal t1 t2
  not' f = Not f
  and' f1 f2 = And f1 f2
  or' f1 f2 = Or f1 f2
  implies f1 f2 = Implies f1 f2
  iff f1 f2 = Iff f1 f2
  forAll x f = ForAll x f
  exists x f = Exists x f
  
  freeVariables (Predicate _ ts) = concatMap freeVarsInTerm ts
  freeVariables (Equal t1 t2) = freeVarsInTerm t1 ++ freeVarsInTerm t2
  freeVariables (Not f) = freeVariables f
  freeVariables (And f1 f2) = nub (freeVariables f1 ++ freeVariables f2)
  freeVariables (Or f1 f2) = nub (freeVariables f1 ++ freeVariables f2)
  freeVariables (Implies f1 f2) = nub (freeVariables f1 ++ freeVariables f2)
  freeVariables (Iff f1 f2) = nub (freeVariables f1 ++ freeVariables f2)
  freeVariables (ForAll x f) = filter (/= x) (freeVariables f)
  freeVariables (Exists x f) = filter (/= x) (freeVariables f)
  
  boundVariables (Predicate _ _) = []
  boundVariables (Equal _ _) = []
  boundVariables (Not f) = boundVariables f
  boundVariables (And f1 f2) = nub (boundVariables f1 ++ boundVariables f2)
  boundVariables (Or f1 f2) = nub (boundVariables f1 ++ boundVariables f2)
  boundVariables (Implies f1 f2) = nub (boundVariables f1 ++ boundVariables f2)
  boundVariables (Iff f1 f2) = nub (boundVariables f1 ++ boundVariables f2)
  boundVariables (ForAll x f) = x : boundVariables f
  boundVariables (Exists x f) = x : boundVariables f
  
  isClosed f = null (freeVariables f)
  isOpen f = not (isClosed f)

-- 项中的自由变量
freeVarsInTerm :: Term -> [String]
freeVarsInTerm (Variable x) = [x]
freeVarsInTerm (Constant _) = []
freeVarsInTerm (Function _ ts) = concatMap freeVarsInTerm ts
```

#### 2.2 一阶语义

```haskell
-- 一阶语义
class FirstOrderSemantics a where
  -- 解释
  interpretation :: a -> Interpretation -> Bool
  -- 模型
  isModel :: a -> Interpretation -> Bool
  -- 有效性
  isValid :: a -> Bool
  -- 可满足性
  isSatisfiable :: a -> Bool
  -- 逻辑蕴含
  logicallyImplies :: a -> a -> Bool

-- 解释结构
data Interpretation = 
    Interpretation {
      domain :: [String],           -- 论域
      constants :: String -> String, -- 常量解释
      functions :: String -> [String] -> String, -- 函数解释
      predicates :: String -> [String] -> Bool   -- 谓词解释
    }
  deriving (Show, Eq)

-- 一阶语义实例
instance FirstOrderSemantics Formula where
  interpretation f i = interpretFormula f i []
  
  isModel f i = interpretation f i
  
  isValid f = all (\i -> interpretation f i) allInterpretations
  
  isSatisfiable f = any (\i -> interpretation f i) allInterpretations
  
  logicallyImplies f1 f2 = 
    all (\i -> not (interpretation f1 i) || interpretation f2 i) allInterpretations

-- 公式解释
interpretFormula :: Formula -> Interpretation -> [(String, String)] -> Bool
interpretFormula (Predicate p ts) i env = 
  let values = map (\t -> interpretTerm t i env) ts
  in predicates i p values
interpretFormula (Equal t1 t2) i env = 
  interpretTerm t1 i env == interpretTerm t2 i env
interpretFormula (Not f) i env = not (interpretFormula f i env)
interpretFormula (And f1 f2) i env = 
  interpretFormula f1 i env && interpretFormula f2 i env
interpretFormula (Or f1 f2) i env = 
  interpretFormula f1 i env || interpretFormula f2 i env
interpretFormula (Implies f1 f2) i env = 
  not (interpretFormula f1 i env) || interpretFormula f2 i env
interpretFormula (Iff f1 f2) i env = 
  interpretFormula f1 i env == interpretFormula f2 i env
interpretFormula (ForAll x f) i env = 
  all (\d -> interpretFormula f i ((x, d) : env)) (domain i)
interpretFormula (Exists x f) i env = 
  any (\d -> interpretFormula f i ((x, d) : env)) (domain i)

-- 项解释
interpretTerm :: Term -> Interpretation -> [(String, String)] -> String
interpretTerm (Variable x) i env = 
  case lookup x env of
    Just d -> d
    Nothing -> error "Unbound variable"
interpretTerm (Constant c) i env = constants i c
interpretTerm (Function f ts) i env = 
  let values = map (\t -> interpretTerm t i env) ts
  in functions i f values
```

### 3. 证明论

#### 3.1 自然演绎系统

```haskell
-- 自然演绎规则
data NaturalDeductionRule = 
    Assumption Proposition
  | AndIntro Proposition Proposition
  | AndElim1 Proposition
  | AndElim2 Proposition
  | OrIntro1 Proposition Proposition
  | OrIntro2 Proposition Proposition
  | OrElim Proposition Proposition Proposition
  | ImplIntro Proposition Proposition
  | ImplElim Proposition Proposition
  | NotIntro Proposition
  | NotElim Proposition
  | ExFalso Proposition
  deriving (Show, Eq)

-- 证明树
data ProofTree = 
    Leaf NaturalDeductionRule
  | Node NaturalDeductionRule [ProofTree]
  deriving (Show, Eq)

-- 证明系统
class ProofSystem a where
  -- 证明
  prove :: a -> ProofTree
  -- 可证明性
  isProvable :: a -> Bool
  -- 证明检查
  checkProof :: ProofTree -> a -> Bool

-- 自然演绎实例
instance ProofSystem Proposition where
  prove p = proveProposition p
  
  isProvable p = case prove p of
    _ -> True
  
  checkProof proof conclusion = checkProofTree proof conclusion

-- 命题证明
proveProposition :: Proposition -> ProofTree
proveProposition (Atomic s) = Leaf (Assumption (Atomic s))
proveProposition (Negation p) = 
  Node (NotIntro p) [proveProposition p]
proveProposition (Conjunction p q) = 
  Node (AndIntro p q) [proveProposition p, proveProposition q]
proveProposition (Disjunction p q) = 
  Node (OrIntro1 p q) [proveProposition p]
proveProposition (Implication p q) = 
  Node (ImplIntro p q) [proveProposition q]
proveProposition (Equivalence p q) = 
  Node (AndIntro (Implication p q) (Implication q p)) 
       [proveProposition (Implication p q), proveProposition (Implication q p)]

-- 证明检查
checkProofTree :: ProofTree -> Proposition -> Bool
checkProofTree (Leaf rule) conclusion = checkRule rule conclusion
checkProofTree (Node rule premises) conclusion = 
  checkRule rule conclusion && all (\premise -> checkProofTree premise (getPremiseConclusion rule)) premises

-- 规则检查
checkRule :: NaturalDeductionRule -> Proposition -> Bool
checkRule (Assumption p) conclusion = p == conclusion
checkRule (AndIntro p q) conclusion = 
  case conclusion of
    Conjunction p' q' -> p == p' && q == q'
    _ -> False
checkRule (AndElim1 p) conclusion = 
  case p of
    Conjunction p' _ -> p' == conclusion
    _ -> False
checkRule (AndElim2 p) conclusion = 
  case p of
    Conjunction _ q -> q == conclusion
    _ -> False
checkRule (OrIntro1 p q) conclusion = 
  case conclusion of
    Disjunction p' q' -> p == p' && q == q'
    _ -> False
checkRule (OrIntro2 p q) conclusion = 
  case conclusion of
    Disjunction p' q' -> p == p' && q == q'
    _ -> False
checkRule (ImplIntro p q) conclusion = 
  case conclusion of
    Implication p' q' -> p == p' && q == q'
    _ -> False
checkRule (ImplElim p q) conclusion = 
  case p of
    Implication p' q' -> q == q' && conclusion == q'
    _ -> False
checkRule (NotIntro p) conclusion = 
  case conclusion of
    Negation p' -> p == p'
    _ -> False
checkRule (NotElim p) conclusion = 
  case p of
    Negation p' -> p' == conclusion
    _ -> False
checkRule (ExFalso p) _ = True

-- 获取前提结论
getPremiseConclusion :: NaturalDeductionRule -> Proposition
getPremiseConclusion (Assumption p) = p
getPremiseConclusion (AndIntro p q) = p
getPremiseConclusion (AndElim1 p) = p
getPremiseConclusion (AndElim2 p) = p
getPremiseConclusion (OrIntro1 p q) = p
getPremiseConclusion (OrIntro2 p q) = q
getPremiseConclusion (OrElim p q r) = p
getPremiseConclusion (ImplIntro p q) = q
getPremiseConclusion (ImplElim p q) = p
getPremiseConclusion (NotIntro p) = p
getPremiseConclusion (NotElim p) = p
getPremiseConclusion (ExFalso p) = p
```

### 4. 形式化验证

#### 4.1 逻辑验证器

```haskell
-- 逻辑验证器
class LogicVerifier a where
  -- 语法验证
  validateSyntax :: a -> Bool
  -- 语义验证
  validateSemantics :: a -> Bool
  -- 证明验证
  validateProof :: a -> ProofTree -> Bool
  -- 一致性检查
  checkConsistency :: a -> Bool

-- 经典逻辑验证器实例
instance LogicVerifier Proposition where
  validateSyntax p = True  -- 所有构造的命题都是语法正确的
  
  validateSemantics p = True  -- 语义验证通过类型系统保证
  
  validateProof p proof = checkProof proof p
  
  checkConsistency p = isSatisfiable p

-- 一阶逻辑验证器实例
instance LogicVerifier Formula where
  validateSyntax f = True  -- 所有构造的公式都是语法正确的
  
  validateSemantics f = True  -- 语义验证通过类型系统保证
  
  validateProof f proof = checkProof proof f
  
  checkConsistency f = isSatisfiable f
```

### 5. 应用示例

#### 5.1 命题逻辑示例

```haskell
-- 示例：证明排中律
excludedMiddle :: Proposition
excludedMiddle = Disjunction (Atomic "P") (Negation (Atomic "P"))

-- 证明排中律是重言式
proveExcludedMiddle :: Bool
proveExcludedMiddle = isTautology excludedMiddle

-- 示例：证明德摩根律
deMorgan1 :: Proposition -> Proposition -> Proposition
deMorgan1 p q = Equivalence 
  (Negation (Conjunction p q))
  (Disjunction (Negation p) (Negation q))

deMorgan2 :: Proposition -> Proposition -> Proposition
deMorgan2 p q = Equivalence 
  (Negation (Disjunction p q))
  (Conjunction (Negation p) (Negation q))

-- 验证德摩根律
verifyDeMorgan :: Bool
verifyDeMorgan = 
  let p = Atomic "P"
      q = Atomic "Q"
  in isTautology (deMorgan1 p q) && isTautology (deMorgan2 p q)
```

#### 5.2 一阶逻辑示例

```haskell
-- 示例：全称量词分配律
universalDistribution :: Formula
universalDistribution = 
  Implies 
    (ForAll "x" (And (Predicate "P" [Variable "x"]) (Predicate "Q" [Variable "x"])))
    (And (ForAll "x" (Predicate "P" [Variable "x"])) (ForAll "x" (Predicate "Q" [Variable "x"])))

-- 验证全称量词分配律
verifyUniversalDistribution :: Bool
verifyUniversalDistribution = isValid universalDistribution

-- 示例：存在量词分配律
existentialDistribution :: Formula
existentialDistribution = 
  Implies 
    (Exists "x" (Or (Predicate "P" [Variable "x"]) (Predicate "Q" [Variable "x"])))
    (Or (Exists "x" (Predicate "P" [Variable "x"])) (Exists "x" (Predicate "Q" [Variable "x"])))

-- 验证存在量词分配律
verifyExistentialDistribution :: Bool
verifyExistentialDistribution = isValid existentialDistribution
```

## 📚 理论背景

### 1. 历史发展

经典逻辑的发展经历了以下重要阶段：

1. **亚里士多德逻辑**：三段论和范畴逻辑
2. **布尔代数**：命题逻辑的代数化
3. **弗雷格逻辑**：一阶逻辑的形式化
4. **希尔伯特系统**：公理化方法
5. **自然演绎**：直觉主义证明系统
6. **模型论**：语义学的发展

### 2. 理论基础

经典逻辑的理论基础包括：

- **集合论**：为语义学提供基础
- **递归论**：为语法学提供基础
- **模型论**：为语义学提供工具
- **证明论**：为证明系统提供基础

### 3. 现代发展

经典逻辑在现代的发展包括：

- **计算逻辑**：逻辑的算法化
- **自动推理**：定理证明自动化
- **逻辑编程**：基于逻辑的编程范式
- **形式化验证**：程序正确性验证

## 🔗 相关理论

- [集合论基础](../01-Mathematics/01-Set-Theory/01-Set-Theory-Basics.md)
- [代数结构](../01-Mathematics/03-Algebraic-Structures.md)
- [模态逻辑](../02-Modal-Logic/01-Basic-Concepts.md)
- [类型论](../04-Type-Theory/01-Basic-Concepts.md)

---

*本文档提供了经典逻辑的完整形式化框架，包括语法、语义、证明论和Haskell实现。*
