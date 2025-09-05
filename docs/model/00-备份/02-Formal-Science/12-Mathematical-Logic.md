# 数学逻辑 (Mathematical Logic)

## 概述

数学逻辑是形式科学的核心基础，为计算机科学和软件工程提供了严格的推理工具。本章节涵盖命题逻辑、谓词逻辑、模态逻辑等核心内容，并提供Haskell实现。

## 1. 命题逻辑 (Propositional Logic)

### 1.1 基本概念

命题逻辑研究简单命题之间的逻辑关系，是形式逻辑的基础。

#### 形式化定义

**定义 1.1.1 (命题)** 命题是一个具有确定真值的陈述句。

**定义 1.1.2 (命题变元)** 命题变元是表示命题的符号，通常用 $p, q, r$ 等表示。

**定义 1.1.3 (逻辑连接词)** 基本逻辑连接词包括：

- 否定 (¬): $\neg p$
- 合取 (∧): $p \land q$
- 析取 (∨): $p \lor q$
- 蕴含 (→): $p \rightarrow q$
- 等价 (↔): $p \leftrightarrow q$

#### Haskell实现

```haskell
-- 命题逻辑的Haskell实现
module PropositionalLogic where

-- 命题变元
type Proposition = String

-- 命题公式的数据类型
data Formula = 
    Var Proposition                    -- 命题变元
  | Not Formula                        -- 否定
  | And Formula Formula                -- 合取
  | Or Formula Formula                 -- 析取
  | Implies Formula Formula            -- 蕴含
  | Equiv Formula Formula              -- 等价
  deriving (Eq, Show)

-- 真值赋值
type Valuation = Proposition -> Bool

-- 求值函数
eval :: Formula -> Valuation -> Bool
eval (Var p) v = v p
eval (Not f) v = not (eval f v)
eval (And f1 f2) v = eval f1 v && eval f2 v
eval (Or f1 f2) v = eval f1 v || eval f2 v
eval (Implies f1 f2) v = not (eval f1 v) || eval f2 v
eval (Equiv f1 f2) v = eval f1 v == eval f2 v

-- 重言式检查
isTautology :: Formula -> Bool
isTautology f = all (\v -> eval f v) allValuations
  where
    allValuations = generateAllValuations (getPropositions f)

-- 获取公式中的所有命题变元
getPropositions :: Formula -> [Proposition]
getPropositions (Var p) = [p]
getPropositions (Not f) = getPropositions f
getPropositions (And f1 f2) = nub (getPropositions f1 ++ getPropositions f2)
getPropositions (Or f1 f2) = nub (getPropositions f1 ++ getPropositions f2)
getPropositions (Implies f1 f2) = nub (getPropositions f1 ++ getPropositions f2)
getPropositions (Equiv f1 f2) = nub (getPropositions f1 ++ getPropositions f2)

-- 生成所有可能的真值赋值
generateAllValuations :: [Proposition] -> [Valuation]
generateAllValuations props = map makeValuation (generateAllCombinations props)
  where
    generateAllCombinations [] = [[]]
    generateAllCombinations (p:ps) = 
      [True:comb | comb <- generateAllCombinations ps] ++
      [False:comb | comb <- generateAllCombinations ps]
    
    makeValuation values = \p -> 
      case elemIndex p props of
        Just i -> values !! i
        Nothing -> False

-- 示例：德摩根定律
deMorganExample :: Formula
deMorganExample = Equiv 
  (Not (And (Var "p") (Var "q")))
  (Or (Not (Var "p")) (Not (Var "q")))

-- 验证德摩根定律
verifyDeMorgan :: Bool
verifyDeMorgan = isTautology deMorganExample
```

### 1.2 推理规则

#### 形式化定义

**定义 1.2.1 (推理规则)** 推理规则是从前提推导结论的形式化方法。

**定理 1.2.1 (假言推理)** 如果 $p \rightarrow q$ 和 $p$ 都为真，则 $q$ 为真。

**证明**：

1. $p \rightarrow q$ (前提)
2. $p$ (前提)
3. 根据蕴含的定义，$p \rightarrow q$ 等价于 $\neg p \lor q$
4. 由于 $p$ 为真，$\neg p$ 为假
5. 因此 $q$ 必须为真

#### Haskell实现

```haskell
-- 推理规则实现
module InferenceRules where

import PropositionalLogic

-- 假言推理
modusPonens :: Formula -> Formula -> Maybe Formula
modusPonens premise1 premise2 = 
  case (premise1, premise2) of
    (Implies p q, Var p') | p == Var p' -> Just q
    _ -> Nothing

-- 反证法
proofByContradiction :: Formula -> Formula -> Bool
proofByContradiction assumption conclusion =
  isTautology (Implies (And assumption (Not conclusion)) (And (Var "p") (Not (Var "p"))))

-- 自然演绎系统
data NaturalDeduction = 
    Assumption Formula
  | ModusPonens NaturalDeduction NaturalDeduction
  | AndIntro NaturalDeduction NaturalDeduction
  | AndElim1 NaturalDeduction
  | AndElim2 NaturalDeduction
  | OrIntro1 Formula NaturalDeduction
  | OrIntro2 Formula NaturalDeduction
  | OrElim NaturalDeduction NaturalDeduction NaturalDeduction
  | NotIntro NaturalDeduction
  | NotElim NaturalDeduction NaturalDeduction
  deriving Show

-- 验证自然演绎证明
validateProof :: NaturalDeduction -> Formula -> Bool
validateProof proof conclusion = 
  case proof of
    Assumption f -> f == conclusion
    ModusPonens p1 p2 -> 
      case (getConclusion p1, getConclusion p2) of
        (Implies p q, p') | p == p' -> q == conclusion
        _ -> False
    AndIntro p1 p2 -> 
      And (getConclusion p1) (getConclusion p2) == conclusion
    AndElim1 p -> 
      case getConclusion p of
        And f1 f2 -> f1 == conclusion
        _ -> False
    AndElim2 p -> 
      case getConclusion p of
        And f1 f2 -> f2 == conclusion
        _ -> False
    OrIntro1 f p -> 
      Or f (getConclusion p) == conclusion
    OrIntro2 f p -> 
      Or (getConclusion p) f == conclusion
    OrElim p1 p2 p3 -> 
      case (getConclusion p1, getConclusion p2, getConclusion p3) of
        (Or f1 f2, f1', f2') | f1 == f1' && f2 == f2' -> 
          f1' == conclusion || f2' == conclusion
        _ -> False
    NotIntro p -> 
      Not (getConclusion p) == conclusion
    NotElim p1 p2 -> 
      case (getConclusion p1, getConclusion p2) of
        (Not f1, f2) | f1 == f2 -> False == conclusion
        _ -> False
  where
    getConclusion :: NaturalDeduction -> Formula
    getConclusion (Assumption f) = f
    getConclusion (ModusPonens p1 p2) = 
      case getConclusion p1 of
        Implies p q -> q
        _ -> error "Invalid modus ponens"
    getConclusion (AndIntro p1 p2) = 
      And (getConclusion p1) (getConclusion p2)
    getConclusion (AndElim1 p) = 
      case getConclusion p of
        And f1 f2 -> f1
        _ -> error "Invalid and elimination"
    getConclusion (AndElim2 p) = 
      case getConclusion p of
        And f1 f2 -> f2
        _ -> error "Invalid and elimination"
    getConclusion (OrIntro1 f p) = 
      Or f (getConclusion p)
    getConclusion (OrIntro2 f p) = 
      Or (getConclusion p) f
    getConclusion (OrElim p1 p2 p3) = 
      case getConclusion p1 of
        Or f1 f2 -> 
          if getConclusion p2 == f1 then getConclusion p2
          else getConclusion p3
        _ -> error "Invalid or elimination"
    getConclusion (NotIntro p) = 
      Not (getConclusion p)
    getConclusion (NotElim p1 p2) = 
      case (getConclusion p1, getConclusion p2) of
        (Not f1, f2) | f1 == f2 -> Var "⊥"
        _ -> error "Invalid not elimination"
```

## 2. 谓词逻辑 (Predicate Logic)

### 2.1 基本概念

谓词逻辑扩展了命题逻辑，引入了量词和谓词，能够表达更复杂的逻辑关系。

#### 形式化定义

**定义 2.1.1 (谓词)** 谓词是描述对象性质的函数，记作 $P(x_1, x_2, \ldots, x_n)$。

**定义 2.1.2 (量词)**

- 全称量词 (∀): $\forall x P(x)$ 表示"对所有 $x$，$P(x)$ 成立"
- 存在量词 (∃): $\exists x P(x)$ 表示"存在 $x$，使得 $P(x)$ 成立"

**定义 2.1.3 (项)** 项是常量、变量或函数应用的组合。

#### Haskell实现

```haskell
-- 谓词逻辑的Haskell实现
module PredicateLogic where

import Data.List (nub)

-- 项的数据类型
data Term = 
    Constant String
  | Variable String
  | Function String [Term]
  deriving (Eq, Show)

-- 原子公式
data AtomicFormula = 
    Predicate String [Term]
  | Equal Term Term
  deriving (Eq, Show)

-- 谓词逻辑公式
data PredicateFormula = 
    Atomic AtomicFormula
  | NotPred PredicateFormula
  | AndPred PredicateFormula PredicateFormula
  | OrPred PredicateFormula PredicateFormula
  | ImpliesPred PredicateFormula PredicateFormula
  | ForAll String PredicateFormula
  | Exists String PredicateFormula
  deriving (Eq, Show)

-- 解释 (Interpretation)
data Interpretation = Interpretation {
  domain :: [String],
  constants :: String -> String,
  functions :: String -> [String] -> String,
  predicates :: String -> [String] -> Bool
}

-- 变量赋值
type VariableAssignment = String -> String

-- 项求值
evalTerm :: Term -> Interpretation -> VariableAssignment -> String
evalTerm (Constant c) _ _ = c
evalTerm (Variable v) _ assignment = assignment v
evalTerm (Function f args) interp assignment = 
  functions interp f (map (\t -> evalTerm t interp assignment) args)

-- 原子公式求值
evalAtomic :: AtomicFormula -> Interpretation -> VariableAssignment -> Bool
evalAtomic (Predicate p args) interp assignment = 
  predicates interp p (map (\t -> evalTerm t interp assignment) args)
evalAtomic (Equal t1 t2) interp assignment = 
  evalTerm t1 interp assignment == evalTerm t2 interp assignment

-- 自由变量
freeVars :: PredicateFormula -> [String]
freeVars (Atomic _) = []
freeVars (NotPred f) = freeVars f
freeVars (AndPred f1 f2) = nub (freeVars f1 ++ freeVars f2)
freeVars (OrPred f1 f2) = nub (freeVars f1 ++ freeVars f2)
freeVars (ImpliesPred f1 f2) = nub (freeVars f1 ++ freeVars f2)
freeVars (ForAll x f) = filter (/= x) (freeVars f)
freeVars (Exists x f) = filter (/= x) (freeVars f)

-- 公式求值
evalPredicate :: PredicateFormula -> Interpretation -> VariableAssignment -> Bool
evalPredicate (Atomic a) interp assignment = evalAtomic a interp assignment
evalPredicate (NotPred f) interp assignment = not (evalPredicate f interp assignment)
evalPredicate (AndPred f1 f2) interp assignment = 
  evalPredicate f1 interp assignment && evalPredicate f2 interp assignment
evalPredicate (OrPred f1 f2) interp assignment = 
  evalPredicate f1 interp assignment || evalPredicate f2 interp assignment
evalPredicate (ImpliesPred f1 f2) interp assignment = 
  not (evalPredicate f1 interp assignment) || evalPredicate f2 interp assignment
evalPredicate (ForAll x f) interp assignment = 
  all (\d -> evalPredicate f interp (updateAssignment assignment x d)) (domain interp)
evalPredicate (Exists x f) interp assignment = 
  any (\d -> evalPredicate f interp (updateAssignment assignment x d)) (domain interp)
  where
    updateAssignment :: VariableAssignment -> String -> String -> VariableAssignment
    updateAssignment old x d = \y -> if y == x then d else old y

-- 示例：全称量词和存在量词的关系
quantifierExample :: PredicateFormula
quantifierExample = EquivPred 
  (NotPred (ForAll "x" (Atomic (Predicate "P" [Variable "x"]))))
  (Exists "x" (NotPred (Atomic (Predicate "P" [Variable "x"]))))

-- 验证量词对偶性
verifyQuantifierDuality :: Bool
verifyQuantifierDuality = 
  let interp = Interpretation {
    domain = ["a", "b", "c"],
    constants = \c -> c,
    functions = \f args -> head args,
    predicates = \p args -> length args > 0
  }
  in all (\assignment -> 
    evalPredicate quantifierExample interp assignment) 
    (generateAllAssignments (freeVars quantifierExample) (domain interp))

-- 生成所有变量赋值
generateAllAssignments :: [String] -> [String] -> [VariableAssignment]
generateAllAssignments [] _ = [\x -> ""]
generateAllAssignments (v:vs) domain = 
  [\x -> if x == v then d else assignment x 
   | d <- domain, assignment <- generateAllAssignments vs domain]
```

### 2.2 推理规则

#### 形式化定义

**定理 2.2.1 (全称实例化)** 如果 $\forall x P(x)$ 为真，则对任意项 $t$，$P(t)$ 为真。

**定理 2.2.2 (存在概括)** 如果 $P(t)$ 为真，则 $\exists x P(x)$ 为真。

#### Haskell实现

```haskell
-- 谓词逻辑推理规则
module PredicateInference where

import PredicateLogic

-- 全称实例化
universalInstantiation :: PredicateFormula -> Term -> Maybe PredicateFormula
universalInstantiation (ForAll x f) t = 
  Just (substitute f x t)
universalInstantiation _ _ = Nothing

-- 存在概括
existentialGeneralization :: PredicateFormula -> String -> Maybe PredicateFormula
existentialGeneralization f x = 
  Just (Exists x f)

-- 替换函数
substitute :: PredicateFormula -> String -> Term -> PredicateFormula
substitute (Atomic (Predicate p args)) x t = 
  Atomic (Predicate p (map (substituteTerm x t) args))
substitute (Atomic (Equal t1 t2)) x t = 
  Atomic (Equal (substituteTerm x t t1) (substituteTerm x t t2))
substitute (NotPred f) x t = 
  NotPred (substitute f x t)
substitute (AndPred f1 f2) x t = 
  AndPred (substitute f1 x t) (substitute f2 x t)
substitute (OrPred f1 f2) x t = 
  OrPred (substitute f1 x t) (substitute f2 x t)
substitute (ImpliesPred f1 f2) x t = 
  ImpliesPred (substitute f1 x t) (substitute f2 x t)
substitute (ForAll y f) x t = 
  if x == y then ForAll y f
  else ForAll y (substitute f x t)
substitute (Exists y f) x t = 
  if x == y then Exists y f
  else Exists y (substitute f x t)

-- 项替换
substituteTerm :: String -> Term -> Term -> Term
substituteTerm x t (Variable y) = 
  if x == y then t else Variable y
substituteTerm x t (Constant c) = Constant c
substituteTerm x t (Function f args) = 
  Function f (map (substituteTerm x t) args)

-- 自然演绎系统扩展
data PredicateNaturalDeduction = 
    PredAssumption PredicateFormula
  | PredModusPonens PredicateNaturalDeduction PredicateNaturalDeduction
  | UniversalIntro String PredicateNaturalDeduction
  | UniversalElim PredicateNaturalDeduction Term
  | ExistentialIntro PredicateNaturalDeduction Term String
  | ExistentialElim PredicateNaturalDeduction PredicateNaturalDeduction String
  deriving Show

-- 验证谓词逻辑证明
validatePredicateProof :: PredicateNaturalDeduction -> PredicateFormula -> Bool
validatePredicateProof proof conclusion = 
  case proof of
    PredAssumption f -> f == conclusion
    PredModusPonens p1 p2 -> 
      case (getPredConclusion p1, getPredConclusion p2) of
        (ImpliesPred p q, p') | p == p' -> q == conclusion
        _ -> False
    UniversalIntro x p -> 
      ForAll x (getPredConclusion p) == conclusion
    UniversalElim p t -> 
      case getPredConclusion p of
        ForAll x f -> substitute f x t == conclusion
        _ -> False
    ExistentialIntro p t x -> 
      Exists x (substitute (getPredConclusion p) x t) == conclusion
    ExistentialElim p1 p2 x -> 
      case getPredConclusion p1 of
        Exists y f | y == x -> getPredConclusion p2 == conclusion
        _ -> False
  where
    getPredConclusion :: PredicateNaturalDeduction -> PredicateFormula
    getPredConclusion (PredAssumption f) = f
    getPredConclusion (PredModusPonens p1 p2) = 
      case getPredConclusion p1 of
        ImpliesPred p q -> q
        _ -> error "Invalid modus ponens"
    getPredConclusion (UniversalIntro x p) = 
      ForAll x (getPredConclusion p)
    getPredConclusion (UniversalElim p t) = 
      case getPredConclusion p of
        ForAll x f -> substitute f x t
        _ -> error "Invalid universal elimination"
    getPredConclusion (ExistentialIntro p t x) = 
      Exists x (substitute (getPredConclusion p) x t)
    getPredConclusion (ExistentialElim p1 p2 x) = 
      getPredConclusion p2
```

## 3. 模态逻辑 (Modal Logic)

### 3.1 基本概念

模态逻辑研究必然性和可能性的逻辑关系，在计算机科学中广泛应用于程序验证和人工智能。

#### 形式化定义

**定义 3.1.1 (模态算子)**

- 必然算子 (□): $\Box p$ 表示"必然 $p$"
- 可能算子 (◇): $\Diamond p$ 表示"可能 $p$"

**定义 3.1.2 (Kripke模型)** Kripke模型是一个三元组 $\mathcal{M} = (W, R, V)$，其中：

- $W$ 是可能世界的集合
- $R \subseteq W \times W$ 是可达关系
- $V: W \times \text{Prop} \to \{\text{true}, \text{false}\}$ 是赋值函数

#### Haskell实现

```haskell
-- 模态逻辑的Haskell实现
module ModalLogic where

import Data.Map (Map)
import qualified Data.Map as Map

-- 可能世界
type World = String

-- 可达关系
type Accessibility = Map World [World]

-- 赋值函数
type Valuation = Map (World, String) Bool

-- Kripke模型
data KripkeModel = KripkeModel {
  worlds :: [World],
  accessibility :: Accessibility,
  valuation :: Valuation
}

-- 模态逻辑公式
data ModalFormula = 
    ModalVar String
  | ModalNot ModalFormula
  | ModalAnd ModalFormula ModalFormula
  | ModalOr ModalFormula ModalFormula
  | ModalImplies ModalFormula ModalFormula
  | Necessarily ModalFormula
  | Possibly ModalFormula
  deriving (Eq, Show)

-- 模态逻辑求值
evalModal :: ModalFormula -> KripkeModel -> World -> Bool
evalModal (ModalVar p) model w = 
  Map.findWithDefault False (w, p) (valuation model)
evalModal (ModalNot f) model w = 
  not (evalModal f model w)
evalModal (ModalAnd f1 f2) model w = 
  evalModal f1 model w && evalModal f2 model w
evalModal (ModalOr f1 f2) model w = 
  evalModal f1 model w || evalModal f2 model w
evalModal (ModalImplies f1 f2) model w = 
  not (evalModal f1 model w) || evalModal f2 model w
evalModal (Necessarily f) model w = 
  all (\w' -> evalModal f model w') (accessibleWorlds model w)
evalModal (Possibly f) model w = 
  any (\w' -> evalModal f model w') (accessibleWorlds model w)

-- 获取可达世界
accessibleWorlds :: KripkeModel -> World -> [World]
accessibleWorlds model w = 
  Map.findWithDefault [] w (accessibility model)

-- 模态逻辑公理系统
data ModalAxiom = 
    K -- K公理: □(p→q) → (□p→□q)
  | T -- T公理: □p → p
  | B -- B公理: p → □◇p
  | D -- D公理: □p → ◇p
  | Four -- 4公理: □p → □□p
  | Five -- 5公理: ◇p → □◇p
  deriving Show

-- 验证公理
verifyAxiom :: ModalAxiom -> KripkeModel -> Bool
verifyAxiom K model = 
  all (\w -> 
    let f = ModalImplies 
              (Necessarily (ModalImplies (ModalVar "p") (ModalVar "q")))
              (ModalImplies (Necessarily (ModalVar "p")) (Necessarily (ModalVar "q")))
    in evalModal f model w) (worlds model)

verifyAxiom T model = 
  all (\w -> 
    let f = ModalImplies (Necessarily (ModalVar "p")) (ModalVar "p")
    in evalModal f model w) (worlds model)

verifyAxiom B model = 
  all (\w -> 
    let f = ModalImplies (ModalVar "p") (Necessarily (Possibly (ModalVar "p")))
    in evalModal f model w) (worlds model)

verifyAxiom D model = 
  all (\w -> 
    let f = ModalImplies (Necessarily (ModalVar "p")) (Possibly (ModalVar "p"))
    in evalModal f model w) (worlds model)

verifyAxiom Four model = 
  all (\w -> 
    let f = ModalImplies (Necessarily (ModalVar "p")) (Necessarily (Necessarily (ModalVar "p")))
    in evalModal f model w) (worlds model)

verifyAxiom Five model = 
  all (\w -> 
    let f = ModalImplies (Possibly (ModalVar "p")) (Necessarily (Possibly (ModalVar "p")))
    in evalModal f model w) (worlds model)

-- 示例：S5模态逻辑
s5Example :: KripkeModel
s5Example = KripkeModel {
  worlds = ["w1", "w2", "w3"],
  accessibility = Map.fromList [
    ("w1", ["w1", "w2", "w3"]),
    ("w2", ["w1", "w2", "w3"]),
    ("w3", ["w1", "w2", "w3"])
  ],
  valuation = Map.fromList [
    (("w1", "p"), True),
    (("w2", "p"), False),
    (("w3", "p"), True)
  ]
}

-- 验证S5公理
verifyS5 :: Bool
verifyS5 = 
  verifyAxiom T s5Example &&
  verifyAxiom Four s5Example &&
  verifyAxiom Five s5Example
```

## 4. 时态逻辑 (Temporal Logic)

### 4.1 线性时态逻辑 (LTL)

#### 形式化定义

**定义 4.1.1 (线性时态逻辑)** 线性时态逻辑用于描述程序执行路径上的时态性质。

**时态算子**：

- $\mathbf{X} \phi$: 下一个时刻 $\phi$ 为真
- $\mathbf{F} \phi$: 将来某个时刻 $\phi$ 为真
- $\mathbf{G} \phi$: 将来所有时刻 $\phi$ 为真
- $\phi \mathbf{U} \psi$: $\phi$ 为真直到 $\psi$ 为真

#### Haskell实现

```haskell
-- 线性时态逻辑实现
module LinearTemporalLogic where

-- 时态逻辑公式
data LTLFormula = 
    LTLVar String
  | LTLNot LTLFormula
  | LTLAnd LTLFormula LTLFormula
  | LTLOr LTLFormula LTLFormula
  | LTLImplies LTLFormula LTLFormula
  | Next LTLFormula
  | Finally LTLFormula
  | Globally LTLFormula
  | Until LTLFormula LTLFormula
  deriving (Eq, Show)

-- 执行路径
type Path = [Map String Bool]

-- LTL求值
evalLTL :: LTLFormula -> Path -> Int -> Bool
evalLTL (LTLVar p) path i = 
  Map.findWithDefault False p (path !! i)
evalLTL (LTLNot f) path i = 
  not (evalLTL f path i)
evalLTL (LTLAnd f1 f2) path i = 
  evalLTL f1 path i && evalLTL f2 path i
evalLTL (LTLOr f1 f2) path i = 
  evalLTL f1 path i || evalLTL f2 path i
evalLTL (LTLImplies f1 f2) path i = 
  not (evalLTL f1 path i) || evalLTL f2 path i
evalLTL (Next f) path i = 
  if i + 1 < length path then evalLTL f path (i + 1) else False
evalLTL (Finally f) path i = 
  any (\j -> j >= i && evalLTL f path j) [0..length path - 1]
evalLTL (Globally f) path i = 
  all (\j -> j >= i -> evalLTL f path j) [0..length path - 1]
evalLTL (Until f1 f2) path i = 
  any (\j -> j >= i && evalLTL f2 path j && 
       all (\k -> k >= i && k < j -> evalLTL f1 path k) [i..j-1]) [i..length path - 1]

-- 模型检测
modelCheck :: LTLFormula -> Path -> Bool
modelCheck f path = evalLTL f path 0

-- 示例：安全性性质
safetyExample :: LTLFormula
safetyExample = Globally (LTLImplies (LTLVar "request") (LTLVar "grant"))

-- 示例：活性性质
livenessExample :: LTLFormula
livenessExample = Globally (LTLImplies (LTLVar "request") (Finally (LTLVar "grant")))
```

## 5. 应用实例

### 5.1 程序验证

```haskell
-- 程序验证示例
module ProgramVerification where

import LinearTemporalLogic

-- 简单的互斥锁程序
data ProgramState = ProgramState {
  process1 :: Bool,  -- 进程1是否在临界区
  process2 :: Bool,  -- 进程2是否在临界区
  lock :: Bool       -- 锁的状态
}

-- 程序状态转换
nextState :: ProgramState -> [ProgramState]
nextState s = 
  if not (lock s) then
    -- 锁空闲，任一进程可以获取
    [s { process1 = True, lock = True },
     s { process2 = True, lock = True }]
  else if process1 s then
    -- 进程1在临界区，可以释放锁
    [s { process1 = False, lock = False }]
  else if process2 s then
    -- 进程2在临界区，可以释放锁
    [s { process2 = False, lock = False }]
  else
    [s]

-- 验证互斥性质
verifyMutualExclusion :: Bool
verifyMutualExclusion = 
  let initialState = ProgramState False False False
      allPaths = generateAllPaths initialState
      mutualExclusion = Globally (LTLNot (LTLAnd (LTLVar "process1") (LTLVar "process2")))
  in all (\path -> modelCheck mutualExclusion path) allPaths

-- 生成所有可能的执行路径
generateAllPaths :: ProgramState -> [Path]
generateAllPaths initialState = 
  let stateToValuation s = Map.fromList [
        ("process1", process1 s),
        ("process2", process2 s),
        ("lock", lock s)
      ]
  in map (map stateToValuation) (generatePaths initialState)
  where
    generatePaths :: ProgramState -> [[ProgramState]]
    generatePaths s = 
      let nextStates = nextState s
      in if null nextStates then [[]]
         else [s : path | nextS <- nextStates, path <- generatePaths nextS]
```

## 总结

本章节建立了完整的数学逻辑体系，包括：

1. **命题逻辑**：基本逻辑连接词和推理规则
2. **谓词逻辑**：量词和谓词的严格定义
3. **模态逻辑**：必然性和可能性的形式化
4. **时态逻辑**：程序执行的时间性质

所有理论都有严格的数学定义和Haskell实现，为程序验证和形式化方法提供了坚实的基础。

---

**参考文献**：

- Enderton, H. B. (2001). A Mathematical Introduction to Logic
- van Dalen, D. (2013). Logic and Structure
- Blackburn, P., de Rijke, M., & Venema, Y. (2001). Modal Logic
