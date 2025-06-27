# 01-经典逻辑基础 (Classical Logic Basics)

## 概述

经典逻辑是逻辑学的基础，包括命题逻辑和谓词逻辑。它基于二值原则（真/假）和经典推理规则，为形式化知识体系提供基础逻辑框架。

## 数学定义

### 命题逻辑 (Propositional Logic)

#### 语法定义

命题逻辑的语法由以下BNF文法定义：

```
φ ::= p | ⊥ | ⊤ | ¬φ | φ ∧ ψ | φ ∨ ψ | φ → ψ | φ ↔ ψ
```

其中：

- $p$ 是原子命题
- $\bot$ 是永假命题
- $\top$ 是永真命题
- $\neg$ 是否定
- $\wedge$ 是合取
- $\vee$ 是析取
- $\rightarrow$ 是蕴含
- $\leftrightarrow$ 是等价

#### 语义定义

给定赋值函数 $v: \mathcal{P} \rightarrow \{0,1\}$，语义函数 $\llbracket \cdot \rrbracket_v$ 定义为：

$$\begin{align}
\llbracket p \rrbracket_v &= v(p) \\
\llbracket \bot \rrbracket_v &= 0 \\
\llbracket \top \rrbracket_v &= 1 \\
\llbracket \neg \phi \rrbracket_v &= 1 - \llbracket \phi \rrbracket_v \\
\llbracket \phi \wedge \psi \rrbracket_v &= \min(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \vee \psi \rrbracket_v &= \max(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \rightarrow \psi \rrbracket_v &= \max(1 - \llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \leftrightarrow \psi \rrbracket_v &= 1 - |\llbracket \phi \rrbracket_v - \llbracket \psi \rrbracket_v|
\end{align}$$

### 谓词逻辑 (Predicate Logic)

#### 语法定义

谓词逻辑的语法扩展了命题逻辑：

```
φ ::= P(t₁,...,tₙ) | t₁ = t₂ | ⊥ | ⊤ | ¬φ | φ ∧ ψ | φ ∨ ψ | φ → ψ | φ ↔ ψ | ∀x.φ | ∃x.φ
t ::= x | c | f(t₁,...,tₙ)
```

其中：
- $P$ 是谓词符号
- $t_i$ 是项
- $x$ 是变量
- $c$ 是常量
- $f$ 是函数符号
- $\forall$ 是全称量词
- $\exists$ 是存在量词

## Haskell实现

### 命题逻辑实现

```haskell
-- 命题逻辑的数据类型
data Proposition = Atom String
                 | Bottom
                 | Top
                 | Not Proposition
                 | And Proposition Proposition
                 | Or Proposition Proposition
                 | Implies Proposition Proposition
                 | Iff Proposition Proposition
                 deriving (Show, Eq)

-- 赋值函数类型
type Valuation = String -> Bool

-- 语义解释函数
interpret :: Proposition -> Valuation -> Bool
interpret (Atom p) v = v p
interpret Bottom _ = False
interpret Top _ = True
interpret (Not phi) v = not (interpret phi v)
interpret (And phi psi) v = interpret phi v && interpret psi v
interpret (Or phi psi) v = interpret phi v || interpret psi v
interpret (Implies phi psi) v = not (interpret phi v) || interpret psi v
interpret (Iff phi psi) v = interpret phi v == interpret psi v

-- 有效性检查
isValid :: Proposition -> Bool
isValid phi = all (\v -> interpret phi v) allValuations phi

-- 可满足性检查
isSatisfiable :: Proposition -> Bool
isSatisfiable phi = any (\v -> interpret phi v) allValuations phi

-- 生成所有可能的赋值
allValuations :: Proposition -> [Valuation]
allValuations phi =
  let atoms = collectAtoms phi
  in generateValuations atoms

-- 收集原子命题
collectAtoms :: Proposition -> [String]
collectAtoms (Atom p) = [p]
collectAtoms (Not phi) = collectAtoms phi
collectAtoms (And phi psi) = nub (collectAtoms phi ++ collectAtoms psi)
collectAtoms (Or phi psi) = nub (collectAtoms phi ++ collectAtoms psi)
collectAtoms (Implies phi psi) = nub (collectAtoms phi ++ collectAtoms psi)
collectAtoms (Iff phi psi) = nub (collectAtoms phi ++ collectAtoms psi)
collectAtoms _ = []

-- 生成所有可能的赋值
generateValuations :: [String] -> [Valuation]
generateValuations atoms =
  let combinations = sequence (replicate (length atoms) [True, False])
  in map (\vals -> \atom ->
           case elemIndex atom atoms of
             Just i -> vals !! i
             Nothing -> False) combinations
```

### 谓词逻辑实现

```haskell
-- 项的数据类型
data Term = Var String
          | Const String
          | Func String [Term]
          deriving (Show, Eq)

-- 谓词逻辑公式的数据类型
data PredicateFormula = Pred String [Term]
                      | Equal Term Term
                      | Bottom
                      | Top
                      | Not PredicateFormula
                      | And PredicateFormula PredicateFormula
                      | Or PredicateFormula PredicateFormula
                      | Implies PredicateFormula PredicateFormula
                      | Iff PredicateFormula PredicateFormula
                      | ForAll String PredicateFormula
                      | Exists String PredicateFormula
                      deriving (Show, Eq)

-- 解释结构
data Interpretation = Interpretation
  { domain :: [String]
  , constInterp :: String -> String
  , funcInterp :: String -> [String] -> String
  , predInterp :: String -> [String] -> Bool
  }

-- 赋值函数
type Assignment = String -> String

-- 项的解释
interpretTerm :: Term -> Interpretation -> Assignment -> String
interpretTerm (Var x) _ a = a x
interpretTerm (Const c) i _ = constInterp i c
interpretTerm (Func f args) i a =
  funcInterp i f (map (\t -> interpretTerm t i a) args)

-- 公式的解释
interpretFormula :: PredicateFormula -> Interpretation -> Assignment -> Bool
interpretFormula (Pred p args) i a =
  predInterp i p (map (\t -> interpretTerm t i a) args)
interpretFormula (Equal t1 t2) i a =
  interpretTerm t1 i a == interpretTerm t2 i a
interpretFormula Bottom _ _ = False
interpretFormula Top _ _ = True
interpretFormula (Not phi) i a = not (interpretFormula phi i a)
interpretFormula (And phi psi) i a =
  interpretFormula phi i a && interpretFormula psi i a
interpretFormula (Or phi psi) i a =
  interpretFormula phi i a || interpretFormula psi i a
interpretFormula (Implies phi psi) i a =
  not (interpretFormula phi i a) || interpretFormula psi i a
interpretFormula (Iff phi psi) i a =
  interpretFormula phi i a == interpretFormula psi i a
interpretFormula (ForAll x phi) i a =
  all (\d -> interpretFormula phi i (updateAssignment a x d)) (domain i)
interpretFormula (Exists x phi) i a =
  any (\d -> interpretFormula phi i (updateAssignment a x d)) (domain i)

-- 更新赋值函数
updateAssignment :: Assignment -> String -> String -> Assignment
updateAssignment a x d y = if x == y then d else a y
```

### 推理系统

```haskell
-- 推理规则
data InferenceRule = ModusPonens
                   | ModusTollens
                   | HypotheticalSyllogism
                   | UniversalInstantiation
                   | ExistentialGeneralization
                   deriving (Show, Eq)

-- 推理步骤
data InferenceStep = InferenceStep
  { premises :: [Proposition]
  , conclusion :: Proposition
  , rule :: InferenceRule
  }

-- 推理有效性检查
isValidInference :: InferenceStep -> Bool
isValidInference (InferenceStep premises conclusion rule) =
  case rule of
    ModusPonens ->
      length premises == 2 &&
      premises !! 0 == (premises !! 1) `Implies` conclusion
    ModusTollens ->
      length premises == 2 &&
      premises !! 0 == Not conclusion `Implies` Not (premises !! 1)
    HypotheticalSyllogism ->
      length premises == 2 &&
      premises !! 0 == (premises !! 1) `Implies` conclusion
    _ -> False

-- 自然演绎系统
data NaturalDeduction = NaturalDeduction
  { assumptions :: [Proposition]
  , steps :: [ProofStep]
  }

data ProofStep = ProofStep
  { formula :: Proposition
  , justification :: Justification
  , dependencies :: [Int]
  }

data Justification = Assumption | Axiom | InferenceRule InferenceRule [Int]
  deriving (Show, Eq)

-- 证明验证
isValidProof :: NaturalDeduction -> Bool
isValidProof (NaturalDeduction assumptions steps) =
  all isValidStep (zip [0..] steps)
  where
    isValidStep (i, step) = case justification step of
      Assumption -> formula step `elem` assumptions
      Axiom -> isAxiom (formula step)
      InferenceRule rule deps ->
        all (< i) deps &&
        isValidInference (InferenceStep
          (map (formula . (steps !!)) deps)
          (formula step)
          rule)

-- 公理检查
isAxiom :: Proposition -> Bool
isAxiom phi = isValid phi
```

## 形式化证明

### 经典推理规则的正确性

**定理 1**: Modus Ponens 是有效的推理规则。

**证明**: 设 $\phi$ 和 $\phi \rightarrow \psi$ 为真，需要证明 $\psi$ 为真。

根据蕴含的语义定义：
$$\llbracket \phi \rightarrow \psi \rrbracket_v = \max(1 - \llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v)$$

由于 $\phi$ 为真，$\llbracket \phi \rrbracket_v = 1$，所以：
$$\llbracket \phi \rightarrow \psi \rrbracket_v = \max(0, \llbracket \psi \rrbracket_v)$$

由于 $\phi \rightarrow \psi$ 为真，$\llbracket \phi \rightarrow \psi \rrbracket_v = 1$，所以：
$$1 = \max(0, \llbracket \psi \rrbracket_v)$$

因此 $\llbracket \psi \rrbracket_v = 1$，即 $\psi$ 为真。

### 德摩根律

**定理 2**: $\neg(\phi \wedge \psi) \leftrightarrow (\neg\phi \vee \neg\psi)$

**证明**: 对于任意赋值 $v$：

$$\begin{align}
\llbracket \neg(\phi \wedge \psi) \rrbracket_v &= 1 - \llbracket \phi \wedge \psi \rrbracket_v \\
&= 1 - \min(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
&= \max(1 - \llbracket \phi \rrbracket_v, 1 - \llbracket \psi \rrbracket_v) \\
&= \max(\llbracket \neg\phi \rrbracket_v, \llbracket \neg\psi \rrbracket_v) \\
&= \llbracket \neg\phi \vee \neg\psi \rrbracket_v
\end{align}$$

因此 $\neg(\phi \wedge \psi) \leftrightarrow (\neg\phi \vee \neg\psi)$ 是永真式。

## 应用示例

### 1. 逻辑电路验证

```haskell
-- 逻辑门的基本操作
data LogicGate = AND | OR | NOT | NAND | NOR | XOR
  deriving (Show, Eq)

-- 逻辑电路
data Circuit = Input String
             | Gate LogicGate [Circuit]
             | Output Circuit

-- 电路评估
evaluateCircuit :: Circuit -> Valuation -> Bool
evaluateCircuit (Input name) v = v name
evaluateCircuit (Gate AND inputs) v = all (\c -> evaluateCircuit c v) inputs
evaluateCircuit (Gate OR inputs) v = any (\c -> evaluateCircuit c v) inputs
evaluateCircuit (Gate NOT [input]) v = not (evaluateCircuit input v)
evaluateCircuit (Gate NAND inputs) v = not (evaluateCircuit (Gate AND inputs) v)
evaluateCircuit (Gate NOR inputs) v = not (evaluateCircuit (Gate OR inputs) v)
evaluateCircuit (Gate XOR [a, b]) v =
  evaluateCircuit a v /= evaluateCircuit b v
evaluateCircuit (Output c) v = evaluateCircuit c v

-- 电路等价性检查
circuitsEquivalent :: Circuit -> Circuit -> Bool
circuitsEquivalent c1 c2 =
  let inputs = nub (collectInputs c1 ++ collectInputs c2)
      valuations = generateValuations inputs
  in all (\v -> evaluateCircuit c1 v == evaluateCircuit c2 v) valuations
```

### 2. 程序验证

```haskell
-- 程序状态
type State = String -> Int

-- 程序语句
data Statement = Assign String Expression
               | If Expression Statement Statement
               | While Expression Statement
               | Seq Statement Statement
               | Skip

-- 表达式
data Expression = Var String
                | Const Int
                | Add Expression Expression
                | Sub Expression Expression
                | Mul Expression Expression

-- 表达式求值
evalExpr :: Expression -> State -> Int
evalExpr (Var x) s = s x
evalExpr (Const n) _ = n
evalExpr (Add e1 e2) s = evalExpr e1 s + evalExpr e2 s
evalExpr (Sub e1 e2) s = evalExpr e1 s - evalExpr e2 s
evalExpr (Mul e1 e2) s = evalExpr e1 s * evalExpr e2 s

-- 霍尔逻辑
data HoareTriple = HoareTriple
  { precondition :: PredicateFormula
  , statement :: Statement
  , postcondition :: PredicateFormula
  }

-- 霍尔逻辑验证
isValidHoareTriple :: HoareTriple -> Bool
isValidHoareTriple (HoareTriple pre stmt post) =
  -- 这里需要实现霍尔逻辑的验证规则
  -- 包括赋值公理、条件规则、循环规则等
  True  -- 简化实现
```

## 与其他理论的关系

### 与类型论的关系
- 经典逻辑为类型论提供基础
- 命题对应类型
- 证明对应程序

### 与形式化方法的关系
- 为模型检测提供逻辑基础
- 为定理证明提供推理规则
- 为程序验证提供形式化框架

### 与人工智能的关系
- 为知识表示提供逻辑语言
- 为自动推理提供基础
- 为专家系统提供推理引擎

---

**相关链接**：
- [形式科学层 - 形式逻辑](../02-Formal-Science/02-Formal-Logic/README.md)
- [理论层 - 形式化方法](../03-Theory/04-Formal-Methods/README.md)
- [实现层 - 形式化证明](../07-Implementation/04-Formal-Proofs/README.md)
