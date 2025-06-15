# 命题逻辑 (Propositional Logic)

## 概述

命题逻辑是研究命题之间逻辑关系的形式系统。它是逻辑学的基础，为更复杂的逻辑系统提供基础。

## 语法

### 命题公式

```haskell
-- 命题逻辑的语法
data Proposition = 
  Atomic String                    -- 原子命题
  | Not Proposition               -- 否定
  | And Proposition Proposition   -- 合取
  | Or Proposition Proposition    -- 析取
  | Implies Proposition Proposition -- 蕴含
  | Iff Proposition Proposition   -- 等价

-- 命题公式的示例
example1 :: Proposition
example1 = And (Atomic "p") (Atomic "q")

example2 :: Proposition
example2 = Implies (Atomic "p") (Or (Atomic "q") (Atomic "r"))

example3 :: Proposition
example3 = Iff (Not (Atomic "p")) (Atomic "q")
```

### 公式的复杂度

```haskell
-- 公式的复杂度度量
class FormulaComplexity where
  depth :: Proposition -> Int
  size :: Proposition -> Int
  atomicCount :: Proposition -> Int
  
-- 复杂度计算
instance FormulaComplexity Proposition where
  depth (Atomic _) = 0
  depth (Not p) = 1 + depth p
  depth (And p q) = 1 + max (depth p) (depth q)
  depth (Or p q) = 1 + max (depth p) (depth q)
  depth (Implies p q) = 1 + max (depth p) (depth q)
  depth (Iff p q) = 1 + max (depth p) (depth q)
  
  size (Atomic _) = 1
  size (Not p) = 1 + size p
  size (And p q) = 1 + size p + size q
  size (Or p q) = 1 + size p + size q
  size (Implies p q) = 1 + size p + size q
  size (Iff p q) = 1 + size p + size q
  
  atomicCount (Atomic _) = 1
  atomicCount (Not p) = atomicCount p
  atomicCount (And p q) = atomicCount p + atomicCount q
  atomicCount (Or p q) = atomicCount p + atomicCount q
  atomicCount (Implies p q) = atomicCount p + atomicCount q
  atomicCount (Iff p q) = atomicCount p + atomicCount q
```

## 语义

### 真值赋值

```haskell
-- 真值赋值函数
type Valuation = String -> Bool

-- 命题的语义解释
class PropositionalSemantics where
  interpret :: Proposition -> Valuation -> Bool
  
-- 语义解释的实现
instance PropositionalSemantics Proposition where
  interpret (Atomic p) v = v p
  interpret (Not p) v = not (interpret p v)
  interpret (And p q) v = interpret p v && interpret q v
  interpret (Or p q) v = interpret p v || interpret q v
  interpret (Implies p q) v = not (interpret p v) || interpret q v
  interpret (Iff p q) v = interpret p v == interpret q v
```

### 真值表

```haskell
-- 真值表生成
class TruthTable where
  generateTruthTable :: Proposition -> [(Valuation, Bool)]
  allValuations :: [String] -> [Valuation]
  
-- 真值表实现
instance TruthTable Proposition where
  generateTruthTable prop = 
    let atoms = extractAtoms prop
        valuations = allValuations atoms
    in [(v, interpret prop v) | v <- valuations]
  
  allValuations atoms = 
    let n = length atoms
        bools = replicateM n [True, False]
    in [\atom -> bools !! (fromJust $ elemIndex atom atoms) | bools <- bools]
```

### 逻辑等价

```haskell
-- 逻辑等价
class LogicalEquivalence where
  isEquivalent :: Proposition -> Proposition -> Bool
  isTautology :: Proposition -> Bool
  isContradiction :: Proposition -> Bool
  isSatisfiable :: Proposition -> Bool
  
-- 逻辑等价实现
instance LogicalEquivalence Proposition where
  isEquivalent p q = 
    let atoms = extractAtoms p ++ extractAtoms q
        valuations = allValuations atoms
    in all (\v -> interpret p v == interpret q v) valuations
  
  isTautology p = 
    let atoms = extractAtoms p
        valuations = allValuations atoms
    in all (\v -> interpret p v) valuations
  
  isContradiction p = 
    let atoms = extractAtoms p
        valuations = allValuations atoms
    in all (\v -> not (interpret p v)) valuations
  
  isSatisfiable p = 
    let atoms = extractAtoms p
        valuations = allValuations atoms
    in any (\v -> interpret p v) valuations
```

## 证明系统

### 自然演绎

```haskell
-- 自然演绎系统
data NaturalDeductionRule = 
  AndIntro
  | AndElim1
  | AndElim2
  | OrIntro1
  | OrIntro2
  | OrElim
  | ImpliesIntro
  | ImpliesElim
  | NotIntro
  | NotElim
  | IffIntro
  | IffElim1
  | IffElim2

-- 自然演绎证明
data NaturalDeductionProof = 
  Assumption Proposition
  | ApplyRule NaturalDeductionRule [NaturalDeductionProof]
  | Discharge Int NaturalDeductionProof

-- 证明验证
verifyNaturalDeduction :: NaturalDeductionProof -> Bool
verifyNaturalDeduction (Assumption _) = True
verifyNaturalDeduction (ApplyRule rule proofs) = 
  all verifyNaturalDeduction proofs && isValidRule rule proofs
verifyNaturalDeduction (Discharge _ proof) = 
  verifyNaturalDeduction proof
```

### 公理化系统

```haskell
-- 命题逻辑公理
data PropositionalAxiom = 
  Axiom1  -- p -> (q -> p)
  | Axiom2  -- (p -> (q -> r)) -> ((p -> q) -> (p -> r))
  | Axiom3  -- (not p -> not q) -> (q -> p)

-- 推理规则
data ModusPonens = 
  ModusPonens Proposition Proposition

-- 公理化证明
data AxiomaticProof = 
  Axiom PropositionalAxiom
  | ModusPonensRule ModusPonens AxiomaticProof AxiomaticProof

-- 公理化证明验证
verifyAxiomaticProof :: AxiomaticProof -> Bool
verifyAxiomaticProof (Axiom _) = True
verifyAxiomaticProof (ModusPonensRule mp proof1 proof2) = 
  verifyAxiomaticProof proof1 && 
  verifyAxiomaticProof proof2 && 
  isValidModusPonens mp proof1 proof2
```

### 序列演算

```haskell
-- 序列
data Sequent = 
  Sequent {
    antecedents :: [Proposition],
    succedents :: [Proposition]
  }

-- 序列演算规则
data SequentRule = 
  LeftAnd Sequent
  | RightAnd Sequent
  | LeftOr Sequent
  | RightOr Sequent
  | LeftImplies Sequent
  | RightImplies Sequent
  | LeftNot Sequent
  | RightNot Sequent
  | Cut Sequent

-- 序列演算证明
data SequentProof = 
  Axiom Sequent
  | ApplySequentRule SequentRule [SequentProof]

-- 序列演算验证
verifySequentProof :: SequentProof -> Bool
verifySequentProof (Axiom sequent) = isValidAxiom sequent
verifySequentProof (ApplySequentRule rule proofs) = 
  all verifySequentProof proofs && isValidSequentRule rule proofs
```

## 重要定理

### 德摩根律

```haskell
-- 德摩根律
deMorganLaws :: Proposition -> Proposition
deMorganLaws (Not (And p q)) = Or (Not p) (Not q)
deMorganLaws (Not (Or p q)) = And (Not p) (Not q)

-- 德摩根律的证明
proveDeMorgan :: Proposition -> NaturalDeductionProof
proveDeMorgan (Not (And p q)) = 
  -- 证明 ¬(p ∧ q) ↔ (¬p ∨ ¬q)
  ApplyRule IffIntro [
    proveNotAndImpliesOr p q,
    proveOrImpliesNotAnd p q
  ]
```

### 分配律

```haskell
-- 分配律
distributiveLaws :: Proposition -> Proposition
distributiveLaws (And p (Or q r)) = Or (And p q) (And p r)
distributiveLaws (Or p (And q r)) = And (Or p q) (Or p r)

-- 分配律的证明
proveDistributive :: Proposition -> NaturalDeductionProof
proveDistributive (And p (Or q r)) = 
  -- 证明 p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
  ApplyRule IffIntro [
    proveAndOrImpliesOrAnd p q r,
    proveOrAndImpliesAndOr p q r
  ]
```

### 双重否定律

```haskell
-- 双重否定律
doubleNegation :: Proposition -> Proposition
doubleNegation (Not (Not p)) = p

-- 双重否定律的证明
proveDoubleNegation :: Proposition -> NaturalDeductionProof
proveDoubleNegation (Not (Not p)) = 
  -- 证明 ¬¬p ↔ p
  ApplyRule IffIntro [
    proveNotNotImplies p,
    proveImpliesNotNot p
  ]
```

## 范式

### 合取范式 (CNF)

```haskell
-- 合取范式
data CNF = 
  CNF {
    clauses :: [Clause]
  }

data Clause = 
  Clause {
    literals :: [Literal]
  }

data Literal = 
  Positive String
  | Negative String

-- 转换为合取范式
class CNFConversion where
  toCNF :: Proposition -> CNF
  fromCNF :: CNF -> Proposition
  
-- CNF转换实现
instance CNFConversion Proposition where
  toCNF prop = 
    let nnf = toNNF prop
        dnf = toDNF nnf
    in dnfToCNF dnf
  
  fromCNF (CNF clauses) = 
    foldr1 And (map fromClause clauses)
```

### 析取范式 (DNF)

```haskell
-- 析取范式
data DNF = 
  DNF {
    terms :: [Term]
  }

data Term = 
  Term {
    literals :: [Literal]
  }

-- 转换为析取范式
class DNFConversion where
  toDNF :: Proposition -> DNF
  fromDNF :: DNF -> Proposition
  
-- DNF转换实现
instance DNFConversion Proposition where
  toDNF prop = 
    let nnf = toNNF prop
    in nnfToDNF nnf
  
  fromDNF (DNF terms) = 
    foldr1 Or (map fromTerm terms)
```

## 可满足性问题

### SAT求解

```haskell
-- SAT求解器
class SATSolver where
  solve :: Proposition -> Maybe Valuation
  isSatisfiable :: Proposition -> Bool
  allModels :: Proposition -> [Valuation]
  
-- DPLL算法
dpll :: Proposition -> Maybe Valuation
dpll prop = 
  let cnf = toCNF prop
  in dpllCNF cnf

-- DPLL算法的CNF版本
dpllCNF :: CNF -> Maybe Valuation
dpllCNF cnf = 
  case simplifyCNF cnf of
    CNF [] -> Just emptyValuation
    CNF (Clause []:_) -> Nothing
    cnf' -> 
      let literal = chooseLiteral cnf'
          cnf1 = assignLiteral cnf' literal True
          cnf2 = assignLiteral cnf' literal False
      in case dpllCNF cnf1 of
           Just val -> Just (extendValuation val literal True)
           Nothing -> 
             case dpllCNF cnf2 of
               Just val -> Just (extendValuation val literal False)
               Nothing -> Nothing
```

### 3-SAT问题

```haskell
-- 3-SAT问题
data ThreeSAT = 
  ThreeSAT {
    clauses :: [ThreeClause]
  }

data ThreeClause = 
  ThreeClause {
    literals :: [Literal]  -- 最多3个文字
  }

-- 3-SAT求解
solve3SAT :: ThreeSAT -> Maybe Valuation
solve3SAT threeSAT = 
  let prop = fromThreeSAT threeSAT
  in solve prop
```

## 应用

### 电路设计

```haskell
-- 数字电路
data DigitalCircuit = 
  DigitalCircuit {
    inputs :: [String],
    outputs :: [String],
    gates :: [Gate]
  }

data Gate = 
  ANDGate String [String] String
  | ORGate String [String] String
  | NOTGate String String String

-- 电路到命题的转换
circuitToProposition :: DigitalCircuit -> Proposition
circuitToProposition circuit = 
  let outputProps = map (gateToProposition circuit) (outputs circuit)
  in foldr1 And outputProps

-- 门到命题的转换
gateToProposition :: DigitalCircuit -> String -> Proposition
gateToProposition circuit output = 
  case findGate circuit output of
    Just (ANDGate _ inputs _) -> 
      foldr1 And (map Atomic inputs)
    Just (ORGate _ inputs _) -> 
      foldr1 Or (map Atomic inputs)
    Just (NOTGate _ input _) -> 
      Not (Atomic input)
    Nothing -> Atomic output
```

### 程序验证

```haskell
-- 程序验证
class ProgramVerification where
  specify :: Program -> Proposition
  verify :: Program -> Proposition -> Bool
  generateProof :: Program -> Proposition -> Maybe NaturalDeductionProof
  
-- 程序规范
data ProgramSpec = 
  ProgramSpec {
    precondition :: Proposition,
    postcondition :: Proposition
  }

-- 程序验证
verifyProgram :: Program -> ProgramSpec -> Bool
verifyProgram program spec = 
  let prop = Implies (precondition spec) (postcondition spec)
  in isTautology prop
```

### 知识表示

```haskell
-- 知识库
data KnowledgeBase = 
  KnowledgeBase {
    facts :: [Proposition],
    rules :: [Proposition]
  }

-- 知识推理
class KnowledgeReasoning where
  query :: KnowledgeBase -> Proposition -> Bool
  infer :: KnowledgeBase -> Proposition -> Maybe NaturalDeductionProof
  
-- 知识查询
queryKnowledge :: KnowledgeBase -> Proposition -> Bool
queryKnowledge kb query = 
  let allFacts = facts kb ++ rules kb
      implication = Implies (foldr1 And allFacts) query
  in isTautology implication
```

## 总结

命题逻辑为计算机科学提供了：

1. **基础逻辑**：为更复杂的逻辑系统提供基础
2. **形式化方法**：严格的语法和语义定义
3. **证明系统**：多种证明方法（自然演绎、公理化、序列演算）
4. **实际应用**：电路设计、程序验证、知识表示

通过命题逻辑，我们可以：
- 严格地分析逻辑论证
- 设计可靠的数字电路
- 验证程序的正确性
- 构建智能的知识系统

命题逻辑是形式化方法和计算机科学的重要基础。 