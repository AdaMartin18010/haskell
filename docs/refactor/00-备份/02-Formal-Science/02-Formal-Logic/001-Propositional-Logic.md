# 命题逻辑基础 (Propositional Logic Foundation)

## 🎯 概述

命题逻辑是形式逻辑的基础，研究命题之间的逻辑关系。本文档系统性地介绍命题逻辑的基本概念、公理系统、推理规则和语义理论，为形式化知识体系提供逻辑基础。

## 📚 快速导航

### 相关理论

- [数学本体论](../../01-Philosophy/01-Metaphysics/001-Mathematical-Ontology.md)
- [集合论基础](../01-Mathematics/001-Set-Theory.md)
- [谓词逻辑基础](002-Predicate-Logic.md)

### 实现示例

- [Haskell逻辑实现](../../haskell/13-Formal-Verification/001-Logic-Implementation.md)
- [逻辑推理算法](../../haskell/07-Algorithms/001-Logic-Algorithms.md)

### 应用领域

- [编程语言理论](../../03-Theory/01-Programming-Language-Theory/001-Syntax-Theory.md)
- [形式化验证](../../07-Implementation/03-Formal-Verification/001-Theorem-Proving.md)

---

## 1. 命题逻辑基本概念

### 1.1 命题定义

**定义 1.1 (命题)**
命题是具有真假值的陈述句，用符号 $p, q, r, \ldots$ 表示。

**定义 1.2 (原子命题)**
原子命题是不可再分解的基本命题。

**定义 1.3 (复合命题)**
复合命题是由原子命题通过逻辑连接词构成的命题。

**数学表示**：
$$\mathcal{P} = \{p_1, p_2, p_3, \ldots\}$$

其中 $\mathcal{P}$ 是命题集合。

### 1.2 逻辑连接词

**定义 1.4 (逻辑连接词)**
命题逻辑的基本连接词：

1. **否定**：$\neg p$ (非 $p$)
2. **合取**：$p \land q$ ($p$ 且 $q$)
3. **析取**：$p \lor q$ ($p$ 或 $q$)
4. **蕴含**：$p \rightarrow q$ (如果 $p$ 则 $q$)
5. **等价**：$p \leftrightarrow q$ ($p$ 当且仅当 $q$)

**算法 1.1 (逻辑连接词实现)**:

```haskell
-- 命题类型
data Proposition = 
  | Atom String
  | Not Proposition
  | And Proposition Proposition
  | Or Proposition Proposition
  | Implies Proposition Proposition
  | Equiv Proposition Proposition
  deriving (Show, Eq)

-- 逻辑连接词函数
negation :: Proposition -> Proposition
negation p = Not p

conjunction :: Proposition -> Proposition -> Proposition
conjunction p q = And p q

disjunction :: Proposition -> Proposition -> Proposition
disjunction p q = Or p q

implication :: Proposition -> Proposition -> Proposition
implication p q = Implies p q

equivalence :: Proposition -> Proposition -> Proposition
equivalence p q = Equiv p q

-- 逻辑连接词验证
verifyLogicalConnectives :: Bool
verifyLogicalConnectives = 
  let p = Atom "p"
      q = Atom "q"
  in negation p == Not p &&
     conjunction p q == And p q &&
     disjunction p q == Or p q &&
     implication p q == Implies p q &&
     equivalence p q == Equiv p q
```

## 2. 命题逻辑语法

### 2.1 形式语法

**定义 2.1 (命题逻辑语法)**
命题逻辑的形式语法：

$$\begin{align}
\phi &::= p \mid \neg \phi \mid \phi \land \phi \mid \phi \lor \phi \mid \phi \rightarrow \phi \mid \phi \leftrightarrow \phi
\end{align}$$

其中 $p$ 是原子命题。

**算法 2.1 (语法解析)**

```haskell
-- 语法解析器
class Parser a where
  parse :: String -> Maybe a
  showFormula :: a -> String

-- 命题解析
instance Parser Proposition where
  parse "p" = Just (Atom "p")
  parse "q" = Just (Atom "q")
  parse "r" = Just (Atom "r")
  parse _ = Nothing  -- 简化实现
  
  showFormula (Atom name) = name
  showFormula (Not p) = "¬" ++ showFormula p
  showFormula (And p q) = "(" ++ showFormula p ++ " ∧ " ++ showFormula q ++ ")"
  showFormula (Or p q) = "(" ++ showFormula p ++ " ∨ " ++ showFormula q ++ ")"
  showFormula (Implies p q) = "(" ++ showFormula p ++ " → " ++ showFormula q ++ ")"
  showFormula (Equiv p q) = "(" ++ showFormula p ++ " ↔ " ++ showFormula q ++ ")"

-- 语法验证
verifySyntax :: Bool
verifySyntax =
  let p = Atom "p"
      q = Atom "q"
      formula = And (Not p) (Implies q p)
  in showFormula formula == "(¬p ∧ (q → p))"
```

### 2.2 语法树

**定义 2.2 (语法树)**
命题的语法树表示其结构：

```haskell
-- 语法树节点
data SyntaxTree =
  | Leaf String
  | UnaryNode String SyntaxTree
  | BinaryNode String SyntaxTree SyntaxTree
  deriving (Show, Eq)

-- 构建语法树
buildSyntaxTree :: Proposition -> SyntaxTree
buildSyntaxTree (Atom name) = Leaf name
buildSyntaxTree (Not p) = UnaryNode "¬" (buildSyntaxTree p)
buildSyntaxTree (And p q) = BinaryNode "∧" (buildSyntaxTree p) (buildSyntaxTree q)
buildSyntaxTree (Or p q) = BinaryNode "∨" (buildSyntaxTree p) (buildSyntaxTree q)
buildSyntaxTree (Implies p q) = BinaryNode "→" (buildSyntaxTree p) (buildSyntaxTree q)
buildSyntaxTree (Equiv p q) = BinaryNode "↔" (buildSyntaxTree p) (buildSyntaxTree q)

-- 语法树验证
verifySyntaxTree :: Bool
verifySyntaxTree =
  let p = Atom "p"
      q = Atom "q"
      tree = buildSyntaxTree (And p q)
  in tree == BinaryNode "∧" (Leaf "p") (Leaf "q")
```

## 3. 命题逻辑语义

### 3.1 真值表

**定义 3.1 (真值赋值)**
真值赋值是从原子命题到真值的函数：

$$\nu: \mathcal{P} \rightarrow \{T, F\}$$

**定义 3.2 (真值表)**
真值表显示所有可能赋值下的真值：

| $p$ | $q$ | $\neg p$ | $p \land q$ | $p \lor q$ | $p \rightarrow q$ | $p \leftrightarrow q$ |
|-----|-----|----------|-------------|------------|-------------------|----------------------|
| T   | T   | F        | T           | T          | T                 | T                    |
| T   | F   | F        | F           | T          | F                 | F                    |
| F   | T   | T        | F           | T          | T                 | F                    |
| F   | F   | T        | F           | F          | T                 | T                    |

**算法 3.1 (真值表实现)**

```haskell
-- 真值类型
data TruthValue = True | False deriving (Show, Eq, Enum, Bounded)

-- 真值赋值
type Valuation = String -> TruthValue

-- 语义解释
interpret :: Proposition -> Valuation -> TruthValue
interpret (Atom name) v = v name
interpret (Not p) v = case interpret p v of
  True -> False
  False -> True
interpret (And p q) v = case (interpret p v, interpret q v) of
  (True, True) -> True
  _ -> False
interpret (Or p q) v = case (interpret p v, interpret q v) of
  (False, False) -> False
  _ -> True
interpret (Implies p q) v = case (interpret p v, interpret q v) of
  (True, False) -> False
  _ -> True
interpret (Equiv p q) v = interpret p v == interpret q v

-- 真值表生成
truthTable :: [String] -> Proposition -> [[TruthValue]]
truthTable atoms formula =
  let valuations = generateValuations atoms
  in map (\v -> map (\atom -> v atom) atoms ++ [interpret formula v]) valuations

-- 生成所有可能赋值
generateValuations :: [String] -> [Valuation]
generateValuations [] = [const True]  -- 简化实现
generateValuations (atom:atoms) =
  let restValuations = generateValuations atoms
  in [\name -> if name == atom then True else v name | v <- restValuations] ++
     [\name -> if name == atom then False else v name | v <- restValuations]

-- 真值表验证
verifyTruthTable :: Bool
verifyTruthTable =
  let p = Atom "p"
      q = Atom "q"
      formula = And p q
      table = truthTable ["p", "q"] formula
  in length table == 4  -- 2^2 = 4 种可能赋值
```

### 3.2 语义性质

**定义 3.3 (重言式)**
命题 $\phi$ 是重言式，如果对所有赋值 $\nu$，都有 $\nu(\phi) = T$。

**定义 3.4 (矛盾式)**
命题 $\phi$ 是矛盾式，如果对所有赋值 $\nu$，都有 $\nu(\phi) = F$。

**定义 3.5 (可满足式)**
命题 $\phi$ 是可满足式，如果存在赋值 $\nu$，使得 $\nu(\phi) = T$。

**算法 3.2 (语义性质检查)**

```haskell
-- 语义性质检查
class SemanticProperties a where
  isTautology :: a -> Bool
  isContradiction :: a -> Bool
  isSatisfiable :: a -> Bool
  isContingent :: a -> Bool

-- 具体实现
instance SemanticProperties Proposition where
  isTautology formula =
    let atoms = extractAtoms formula
        valuations = generateValuations atoms
    in all (\v -> interpret formula v == True) valuations
  
  isContradiction formula =
    let atoms = extractAtoms formula
        valuations = generateValuations atoms
    in all (\v -> interpret formula v == False) valuations
  
  isSatisfiable formula =
    let atoms = extractAtoms formula
        valuations = generateValuations atoms
    in any (\v -> interpret formula v == True) valuations
  
  isContingent formula =
    isSatisfiable formula && not (isTautology formula)

-- 提取原子命题
extractAtoms :: Proposition -> [String]
extractAtoms (Atom name) = [name]
extractAtoms (Not p) = extractAtoms p
extractAtoms (And p q) = nub (extractAtoms p ++ extractAtoms q)
extractAtoms (Or p q) = nub (extractAtoms p ++ extractAtoms q)
extractAtoms (Implies p q) = nub (extractAtoms p ++ extractAtoms q)
extractAtoms (Equiv p q) = nub (extractAtoms p ++ extractAtoms q)

-- 语义性质验证
verifySemanticProperties :: Bool
verifySemanticProperties =
  let p = Atom "p"
      q = Atom "q"
      tautology = Or p (Not p)  -- p ∨ ¬p
      contradiction = And p (Not p)  -- p ∧ ¬p
      contingent = And p q  -- p ∧ q
  in isTautology tautology &&
     isContradiction contradiction &&
     isSatisfiable contingent &&
     isContingent contingent
```

## 4. 命题逻辑推理

### 4.1 推理规则

**定义 4.1 (推理规则)**
命题逻辑的基本推理规则：

1. **假言推理**：$\frac{p \rightarrow q \quad p}{q}$
2. **否定推理**：$\frac{p \rightarrow q \quad \neg q}{\neg p}$
3. **合取引入**：$\frac{p \quad q}{p \land q}$
4. **合取消除**：$\frac{p \land q}{p}$ 和 $\frac{p \land q}{q}$
5. **析取引入**：$\frac{p}{p \lor q}$ 和 $\frac{q}{p \lor q}$

**算法 4.1 (推理规则实现)**

```haskell
-- 推理规则类型
data InferenceRule =
  | ModusPonens Proposition Proposition
  | ModusTollens Proposition Proposition
  | ConjunctionIntro Proposition Proposition
  | ConjunctionElim1 Proposition Proposition
  | ConjunctionElim2 Proposition Proposition
  | DisjunctionIntro1 Proposition Proposition
  | DisjunctionIntro2 Proposition Proposition
  deriving (Show)

-- 推理规则应用
applyRule :: InferenceRule -> [Proposition] -> Maybe Proposition
applyRule (ModusPonens p q) premises =
  case premises of
    [Implies p' q', p''] | p' == p && q' == q && p'' == p -> Just q
    _ -> Nothing

applyRule (ModusTollens p q) premises =
  case premises of
    [Implies p' q', Not q'] | p' == p && q' == q -> Just (Not p)
    _ -> Nothing

applyRule (ConjunctionIntro p q) premises =
  case premises of
    [p', q'] | p' == p && q' == q -> Just (And p q)
    _ -> Nothing

applyRule (ConjunctionElim1 p q) premises =
  case premises of
    [And p' q'] | p' == p && q' == q -> Just p
    _ -> Nothing

applyRule (ConjunctionElim2 p q) premises =
  case premises of
    [And p' q'] | p' == p && q' == q -> Just q
    _ -> Nothing

applyRule (DisjunctionIntro1 p q) premises =
  case premises of
    [p'] | p' == p -> Just (Or p q)
    _ -> Nothing

applyRule (DisjunctionIntro2 p q) premises =
  case premises of
    [q'] | q' == q -> Just (Or p q)
    _ -> Nothing

-- 推理规则验证
verifyInferenceRules :: Bool
verifyInferenceRules =
  let p = Atom "p"
      q = Atom "q"
      imp = Implies p q
  in applyRule (ModusPonens p q) [imp, p] == Just q &&
     applyRule (ConjunctionIntro p q) [p, q] == Just (And p q)
```

### 4.2 证明系统

**定义 4.2 (证明)**
证明是从公理和假设到结论的推理序列。

**算法 4.2 (证明系统)**

```haskell
-- 证明步骤
data ProofStep =
  | Axiom Proposition
  | Assumption Proposition
  | Inference InferenceRule [Int]  -- 规则和前提步骤编号
  deriving (Show)

-- 证明
data Proof = Proof {
  steps :: [ProofStep],
  conclusion :: Proposition
} deriving (Show)

-- 验证证明
verifyProof :: Proof -> Bool
verifyProof (Proof steps conclusion) =
  let stepResults = map verifyStep (zip [0..] steps)
      lastStep = last stepResults
  in all isJust stepResults && lastStep == Just conclusion

-- 验证单个步骤
verifyStep :: (Int, ProofStep) -> Maybe Proposition
verifyStep (i, Axiom prop) = Just prop
verifyStep (i, Assumption prop) = Just prop
verifyStep (i, Inference rule premiseIndices) =
  let premiseProps = map (\idx -> stepResults !! idx) premiseIndices
      stepResults = map snd (take i steps)
  in applyRule rule premiseProps

-- 证明系统验证
verifyProofSystem :: Bool
verifyProofSystem =
  let p = Atom "p"
      q = Atom "q"
      proof = Proof [
        Assumption p,
        Assumption (Implies p q),
        Inference (ModusPonens p q) [1, 0]
      ] q
  in verifyProof proof
```

## 5. 命题逻辑等价

### 5.1 逻辑等价

**定义 5.1 (逻辑等价)**
命题 $\phi$ 和 $\psi$ 逻辑等价，记作 $\phi \equiv \psi$，如果对所有赋值 $\nu$，都有 $\nu(\phi) = \nu(\psi)$。

**定理 5.1 (基本等价律)**
1. **双重否定**：$\neg \neg p \equiv p$
2. **德摩根律**：$\neg(p \land q) \equiv \neg p \lor \neg q$
3. **分配律**：$p \land (q \lor r) \equiv (p \land q) \lor (p \land r)$
4. **结合律**：$(p \land q) \land r \equiv p \land (q \land r)$

**算法 5.1 (等价检查)**

```haskell
-- 逻辑等价检查
logicallyEquivalent :: Proposition -> Proposition -> Bool
logicallyEquivalent p q =
  let atoms = nub (extractAtoms p ++ extractAtoms q)
      valuations = generateValuations atoms
  in all (\v -> interpret p v == interpret q v) valuations

-- 等价变换
class EquivalenceTransform a where
  doubleNegation :: a -> a
  deMorgan :: a -> a
  distributivity :: a -> a
  associativity :: a -> a

-- 具体实现
instance EquivalenceTransform Proposition where
  doubleNegation (Not (Not p)) = p
  doubleNegation p = p
  
  deMorgan (Not (And p q)) = Or (Not p) (Not q)
  deMorgan (Not (Or p q)) = And (Not p) (Not q)
  deMorgan p = p
  
  distributivity (And p (Or q r)) = Or (And p q) (And p r)
  distributivity (Or p (And q r)) = And (Or p q) (Or p r)
  distributivity p = p
  
  associativity (And (And p q) r) = And p (And q r)
  associativity (Or (Or p q) r) = Or p (Or q r)
  associativity p = p

-- 等价验证
verifyEquivalence :: Bool
verifyEquivalence =
  let p = Atom "p"
      q = Atom "q"
      doubleNeg = Not (Not p)
      deMorganForm = Not (And p q)
  in logicallyEquivalent (doubleNegation doubleNeg) p &&
     logicallyEquivalent (deMorgan deMorganForm) (Or (Not p) (Not q))
```

### 5.2 范式

**定义 5.2 (析取范式)**
析取范式是形如 $(p_1 \land p_2 \land \ldots) \lor (q_1 \land q_2 \land \ldots) \lor \ldots$ 的公式。

**定义 5.3 (合取范式)**
合取范式是形如 $(p_1 \lor p_2 \lor \ldots) \land (q_1 \lor q_2 \lor \ldots) \land \ldots$ 的公式。

**算法 5.2 (范式转换)**

```haskell
-- 范式类型
data NormalForm =
  | DNF [[Proposition]]  -- 析取范式
  | CNF [[Proposition]]  -- 合取范式
  deriving (Show)

-- 转换为析取范式
toDNF :: Proposition -> NormalForm
toDNF formula =
  let atoms = extractAtoms formula
      valuations = generateValuations atoms
      trueValuations = filter (\v -> interpret formula v == True) valuations
      clauses = map (valuationToClause atoms) trueValuations
  in DNF clauses

-- 转换为合取范式
toCNF :: Proposition -> NormalForm
toCNF formula =
  let atoms = extractAtoms formula
      valuations = generateValuations atoms
      falseValuations = filter (\v -> interpret formula v == False) valuations
      clauses = map (valuationToClause atoms . negateValuation) falseValuations
  in CNF clauses

-- 赋值转换为子句
valuationToClause :: [String] -> Valuation -> [Proposition]
valuationToClause atoms v =
  map (\atom -> if v atom == True then Atom atom else Not (Atom atom)) atoms

-- 否定赋值
negateValuation :: Valuation -> Valuation
negateValuation v = \atom -> case v atom of
  True -> False
  False -> True

-- 范式验证
verifyNormalForms :: Bool
verifyNormalForms =
  let p = Atom "p"
      q = Atom "q"
      formula = Or (And p q) (And (Not p) q)
      dnf = toDNF formula
      cnf = toCNF formula
  in case dnf of
       DNF clauses -> length clauses > 0
       _ -> False
```

## 6. 命题逻辑应用

### 6.1 电路设计

**定理 6.1 (电路对应)**
每个布尔函数都可以用逻辑门电路实现。

**算法 6.1 (电路实现)**

```haskell
-- 逻辑门类型
data LogicGate =
  | NOT LogicGate
  | AND LogicGate LogicGate
  | OR LogicGate LogicGate
  | Input String
  deriving (Show)

-- 电路评估
evaluateCircuit :: LogicGate -> Valuation -> TruthValue
evaluateCircuit (Input name) v = v name
evaluateCircuit (NOT gate) v = case evaluateCircuit gate v of
  True -> False
  False -> True
evaluateCircuit (AND gate1 gate2) v =
  case (evaluateCircuit gate1 v, evaluateCircuit gate2 v) of
    (True, True) -> True
    _ -> False
evaluateCircuit (OR gate1 gate2) v =
  case (evaluateCircuit gate1 v, evaluateCircuit gate2 v) of
    (False, False) -> False
    _ -> True

-- 命题到电路的转换
propositionToCircuit :: Proposition -> LogicGate
propositionToCircuit (Atom name) = Input name
propositionToCircuit (Not p) = NOT (propositionToCircuit p)
propositionToCircuit (And p q) = AND (propositionToCircuit p) (propositionToCircuit q)
propositionToCircuit (Or p q) = OR (propositionToCircuit p) (propositionToCircuit q)
propositionToCircuit (Implies p q) = OR (NOT (propositionToCircuit p)) (propositionToCircuit q)
propositionToCircuit (Equiv p q) =
  AND (OR (NOT (propositionToCircuit p)) (propositionToCircuit q))
      (OR (NOT (propositionToCircuit q)) (propositionToCircuit p))

-- 电路验证
verifyCircuit :: Bool
verifyCircuit =
  let p = Atom "p"
      q = Atom "q"
      formula = And p q
      circuit = propositionToCircuit formula
      v = \name -> if name == "p" then True else False
  in evaluateCircuit circuit v == interpret formula v
```

### 6.2 程序验证

**定义 6.2 (程序验证)**
使用命题逻辑验证程序的性质。

**算法 6.2 (程序验证)**

```haskell
-- 程序状态
data ProgramState = ProgramState {
  variables :: [(String, Int)],
  condition :: Proposition
} deriving (Show)

-- 程序验证
verifyProgram :: ProgramState -> Proposition -> Bool
verifyProgram state invariant =
  let v = stateToValuation state
  in interpret invariant v == True

-- 状态到赋值
stateToValuation :: ProgramState -> Valuation
stateToValuation state = \name ->
  case lookup name (variables state) of
    Just 0 -> False
    Just _ -> True
    Nothing -> False

-- 程序验证示例
verifyProgramExample :: Bool
verifyProgramExample =
  let state = ProgramState [("x", 5), ("y", 3)] (Atom "x_positive")
      invariant = Atom "x_positive"  -- x > 0
  in verifyProgram state invariant
```

## 📊 总结

命题逻辑为形式化知识体系提供了坚实的逻辑基础。通过系统性地介绍命题逻辑的基本概念、语法、语义、推理和应用，我们建立了一个完整的命题逻辑框架。这个框架不仅支持传统的逻辑研究，还为计算机科学、程序验证和电路设计提供了理论基础。

### 关键成果

1. **基本概念**：严格定义了命题、逻辑连接词等基本概念
2. **形式语法**：建立了命题逻辑的形式语法和语法树
3. **语义理论**：发展了真值表语义和语义性质理论
4. **推理系统**：建立了完整的推理规则和证明系统
5. **等价理论**：发展了逻辑等价和范式理论
6. **实际应用**：展示了在电路设计和程序验证中的应用

### 未来发展方向

1. **高阶逻辑**：研究谓词逻辑和模态逻辑
2. **构造性逻辑**：发展直觉主义逻辑
3. **模糊逻辑**：探索不确定性逻辑
4. **量子逻辑**：研究量子计算中的逻辑

---

**文档版本**: 1.0  
**最后更新**: 2024年12月  
**维护状态**: 持续维护
