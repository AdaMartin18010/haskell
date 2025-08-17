# 逻辑系统理论 / Logical Systems Theory

## 📚 概述 / Overview

本文档建立逻辑系统的完整理论体系，使用Haskell实现命题逻辑、谓词逻辑、模态逻辑、直觉逻辑和类型论的形式化模型。逻辑系统为形式化推理、程序验证、人工智能等提供理论基础。

This document establishes a complete theoretical system of logical systems, using Haskell to implement formal models of propositional logic, predicate logic, modal logic, intuitionistic logic, and type theory. Logical systems provide theoretical foundations for formal reasoning, program verification, artificial intelligence, etc.

## 🎯 核心目标 / Core Objectives

1. **形式化逻辑系统 / Formalize Logical Systems**: 建立命题逻辑、谓词逻辑、模态逻辑的严格数学定义 / Establish rigorous mathematical definitions of propositional logic, predicate logic, and modal logic
2. **实现推理系统 / Implement Reasoning Systems**: 构建自然演绎、公理化、表列等推理方法 / Construct reasoning methods such as natural deduction, axiomatic systems, and tableau methods
3. **建立语义理论 / Establish Semantic Theory**: 实现真值语义、可能世界语义、代数语义 / Implement truth semantics, possible world semantics, and algebraic semantics
4. **发展类型论 / Develop Type Theory**: 建立直觉类型论、线性类型论等基础 / Establish foundations of intuitionistic type theory, linear type theory, etc.
5. **应用逻辑系统 / Apply Logical Systems**: 在程序验证、人工智能、知识表示中的应用 / Applications in program verification, artificial intelligence, and knowledge representation

## 🏗️ 理论框架 / Theoretical Framework

### 1. 命题逻辑 / Propositional Logic

**定义 1.1 (命题公式 / Propositional Formula)**
命题公式的归纳定义：

Inductive definition of propositional formulas:

$$
\begin{align}
\phi &::= p \mid \bot \mid \top \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \to \psi \mid \phi \leftrightarrow \psi
\end{align}
$$

其中 $p$ 是原子命题，$\bot$ 是假，$\top$ 是真。

Where $p$ is an atomic proposition, $\bot$ is false, and $\top$ is true.

**定义 1.2 (真值赋值 / Truth Valuation)**
真值赋值是函数 $v : \mathcal{P} \to \{0, 1\}$，其中 $\mathcal{P}$ 是原子命题集。

A truth valuation is a function $v : \mathcal{P} \to \{0, 1\}$, where $\mathcal{P}$ is the set of atomic propositions.

**定义 1.3 (语义解释 / Semantic Interpretation)**
公式 $\phi$ 在赋值 $v$ 下的真值 $\llbracket \phi \rrbracket_v$ 定义为：

The truth value $\llbracket \phi \rrbracket_v$ of formula $\phi$ under valuation $v$ is defined as:

$$
\begin{align}
\llbracket p \rrbracket_v &= v(p) \\
\llbracket \bot \rrbracket_v &= 0 \\
\llbracket \top \rrbracket_v &= 1 \\
\llbracket \neg \phi \rrbracket_v &= 1 - \llbracket \phi \rrbracket_v \\
\llbracket \phi \land \psi \rrbracket_v &= \min(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \lor \psi \rrbracket_v &= \max(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \to \psi \rrbracket_v &= \max(1 - \llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v) \\
\llbracket \phi \leftrightarrow \psi \rrbracket_v &= 1 - |\llbracket \phi \rrbracket_v - \llbracket \psi \rrbracket_v|
\end{align}
$$

```haskell
-- 命题公式定义 / Propositional Formula Definition
data Proposition = 
    Atom String |                    -- 原子命题 / Atomic proposition
    Bot |                           -- 假 / False
    Top |                           -- 真 / True
    Not Proposition |               -- 否定 / Negation
    And Proposition Proposition |   -- 合取 / Conjunction
    Or Proposition Proposition |    -- 析取 / Disjunction
    Implies Proposition Proposition | -- 蕴含 / Implication
    Iff Proposition Proposition     -- 等价 / Equivalence

-- 真值赋值 / Truth Valuation
type Valuation = String -> Bool

-- 语义解释 / Semantic Interpretation
interpret :: Proposition -> Valuation -> Bool
interpret (Atom p) v = v p
interpret Bot _ = False
interpret Top _ = True
interpret (Not p) v = not (interpret p v)
interpret (And p q) v = interpret p v && interpret q v
interpret (Or p q) v = interpret p v || interpret q v
interpret (Implies p q) v = not (interpret p v) || interpret q v
interpret (Iff p q) v = interpret p v == interpret q v

-- 真值表生成 / Truth Table Generation
truthTable :: Proposition -> [(Valuation, Bool)]
truthTable prop = 
    let atoms = collectAtoms prop
        valuations = generateValuations atoms
    in [(v, interpret prop v) | v <- valuations]

-- 收集原子命题 / Collect Atomic Propositions
collectAtoms :: Proposition -> [String]
collectAtoms (Atom p) = [p]
collectAtoms Bot = []
collectAtoms Top = []
collectAtoms (Not p) = collectAtoms p
collectAtoms (And p q) = nub (collectAtoms p ++ collectAtoms q)
collectAtoms (Or p q) = nub (collectAtoms p ++ collectAtoms q)
collectAtoms (Implies p q) = nub (collectAtoms p ++ collectAtoms q)
collectAtoms (Iff p q) = nub (collectAtoms p ++ collectAtoms q)

-- 生成所有可能的真值赋值 / Generate All Possible Truth Valuations
generateValuations :: [String] -> [Valuation]
generateValuations atoms = 
    let n = length atoms
        boolLists = replicateM n [True, False]
    in [\atom -> boolLists !! i !! j | 
        (i, atom) <- zip [0..] atoms, 
        j <- [0..1]]

-- 重言式检查 / Tautology Check
isTautology :: Proposition -> Bool
isTautology prop = all snd (truthTable prop)

-- 矛盾式检查 / Contradiction Check
isContradiction :: Proposition -> Bool
isContradiction prop = all (not . snd) (truthTable prop)

-- 可满足性检查 / Satisfiability Check
isSatisfiable :: Proposition -> Bool
isSatisfiable prop = any snd (truthTable prop)
```

### 2. 谓词逻辑 / Predicate Logic

**定义 2.1 (一阶语言 / First-order Language)**
一阶语言 $\mathcal{L}$ 包含：

A first-order language $\mathcal{L}$ contains:

1. **常量符号 / Constant Symbols**: $\mathcal{C}$
2. **函数符号 / Function Symbols**: $\mathcal{F}$
3. **谓词符号 / Predicate Symbols**: $\mathcal{P}$
4. **变量 / Variables**: $\mathcal{V}$

**定义 2.2 (项 / Term)**
项的归纳定义：

Inductive definition of terms:

$$
t ::= x \mid c \mid f(t_1, \ldots, t_n)
$$

其中 $x$ 是变量，$c$ 是常量，$f$ 是 $n$ 元函数符号。

Where $x$ is a variable, $c$ is a constant, and $f$ is an $n$-ary function symbol.

**定义 2.3 (公式 / Formula)**
公式的归纳定义：

Inductive definition of formulas:

$$
\phi ::= P(t_1, \ldots, t_n) \mid \bot \mid \top \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \to \psi \mid \forall x \phi \mid \exists x \phi
$$

其中 $P$ 是 $n$ 元谓词符号。

Where $P$ is an $n$-ary predicate symbol.

```haskell
-- 一阶语言 / First-order Language
data Term = 
    Var String |                    -- 变量 / Variable
    Const String |                  -- 常量 / Constant
    Func String [Term]              -- 函数 / Function

data Formula = 
    Pred String [Term] |            -- 谓词 / Predicate
    Bot |                          -- 假 / False
    Top |                          -- 真 / True
    Not Formula |                  -- 否定 / Negation
    And Formula Formula |          -- 合取 / Conjunction
    Or Formula Formula |           -- 析取 / Disjunction
    Implies Formula Formula |      -- 蕴含 / Implication
    Forall String Formula |        -- 全称量词 / Universal quantifier
    Exists String Formula          -- 存在量词 / Existential quantifier

-- 结构 / Structure
data Structure dom = Structure {
    domain :: [dom],               -- 论域 / Domain
    constants :: String -> dom,    -- 常量解释 / Constant interpretation
    functions :: String -> [dom] -> dom, -- 函数解释 / Function interpretation
    predicates :: String -> [dom] -> Bool -- 谓词解释 / Predicate interpretation
}

-- 赋值 / Assignment
type Assignment dom = String -> dom

-- 项解释 / Term Interpretation
interpretTerm :: Structure dom -> Assignment dom -> Term -> dom
interpretTerm struct assign (Var x) = assign x
interpretTerm struct assign (Const c) = constants struct c
interpretTerm struct assign (Func f args) = 
    functions struct f (map (interpretTerm struct assign) args)

-- 公式解释 / Formula Interpretation
interpretFormula :: Structure dom -> Assignment dom -> Formula -> Bool
interpretFormula struct assign (Pred p args) = 
    predicates struct p (map (interpretTerm struct assign) args)
interpretFormula struct assign Bot = False
interpretFormula struct assign Top = True
interpretFormula struct assign (Not phi) = not (interpretFormula struct assign phi)
interpretFormula struct assign (And phi psi) = 
    interpretFormula struct assign phi && interpretFormula struct assign psi
interpretFormula struct assign (Or phi psi) = 
    interpretFormula struct assign phi || interpretFormula struct assign psi
interpretFormula struct assign (Implies phi psi) = 
    not (interpretFormula struct assign phi) || interpretFormula struct assign psi
interpretFormula struct assign (Forall x phi) = 
    all (\d -> interpretFormula struct (updateAssign assign x d) phi) (domain struct)
interpretFormula struct assign (Exists x phi) = 
    any (\d -> interpretFormula struct (updateAssign assign x d) phi) (domain struct)

-- 更新赋值 / Update Assignment
updateAssign :: Assignment dom -> String -> dom -> Assignment dom
updateAssign assign x d y = if x == y then d else assign y
```

### 3. 模态逻辑 / Modal Logic

**定义 3.1 (模态语言 / Modal Language)**
模态语言在命题逻辑基础上增加模态算子：

Modal language adds modal operators to propositional logic:

$$
\phi ::= p \mid \bot \mid \top \mid \neg \phi \mid \phi \land \psi \mid \phi \lor \psi \mid \phi \to \psi \mid \Box \phi \mid \Diamond \phi
$$

其中 $\Box$ 是必然算子，$\Diamond$ 是可能算子。

Where $\Box$ is the necessity operator and $\Diamond$ is the possibility operator.

**定义 3.2 (克里普克模型 / Kripke Model)**
克里普克模型是三元组 $\mathcal{M} = \langle W, R, V \rangle$，其中：

A Kripke model is a triple $\mathcal{M} = \langle W, R, V \rangle$, where:

- $W$ 是可能世界集 / $W$ is the set of possible worlds
- $R \subseteq W \times W$ 是可达关系 / $R \subseteq W \times W$ is the accessibility relation
- $V : W \times \mathcal{P} \to \{0, 1\}$ 是赋值函数 / $V : W \times \mathcal{P} \to \{0, 1\}$ is the valuation function

**定义 3.3 (模态语义 / Modal Semantics)**
公式 $\phi$ 在世界 $w$ 中为真，记作 $\mathcal{M}, w \models \phi$：

Formula $\phi$ is true at world $w$, denoted $\mathcal{M}, w \models \phi$:

$$
\begin{align}
\mathcal{M}, w \models p &\iff V(w, p) = 1 \\
\mathcal{M}, w \models \Box \phi &\iff \forall v \in W, wRv \Rightarrow \mathcal{M}, v \models \phi \\
\mathcal{M}, w \models \Diamond \phi &\iff \exists v \in W, wRv \land \mathcal{M}, v \models \phi
\end{align}
$$

```haskell
-- 模态公式 / Modal Formula
data ModalFormula = 
    MAtom String |                 -- 原子命题 / Atomic proposition
    MBot |                         -- 假 / False
    MTop |                         -- 真 / True
    MNot ModalFormula |           -- 否定 / Negation
    MAnd ModalFormula ModalFormula | -- 合取 / Conjunction
    MOr ModalFormula ModalFormula |  -- 析取 / Disjunction
    MImplies ModalFormula ModalFormula | -- 蕴含 / Implication
    MBox ModalFormula |           -- 必然 / Necessity
    MDiamond ModalFormula         -- 可能 / Possibility

-- 克里普克模型 / Kripke Model
data KripkeModel world = KripkeModel {
    worlds :: [world],             -- 可能世界 / Possible worlds
    accessibility :: world -> world -> Bool, -- 可达关系 / Accessibility relation
    valuation :: world -> String -> Bool -- 赋值函数 / Valuation function
}

-- 模态语义 / Modal Semantics
interpretModal :: KripkeModel world -> world -> ModalFormula -> Bool
interpretModal model w (MAtom p) = valuation model w p
interpretModal model w MBot = False
interpretModal model w MTop = True
interpretModal model w (MNot phi) = not (interpretModal model w phi)
interpretModal model w (MAnd phi psi) = 
    interpretModal model w phi && interpretModal model w psi
interpretModal model w (MOr phi psi) = 
    interpretModal model w phi || interpretModal model w psi
interpretModal model w (MImplies phi psi) = 
    not (interpretModal model w phi) || interpretModal model w psi
interpretModal model w (MBox phi) = 
    all (\v -> accessibility model w v -> interpretModal model v phi) (worlds model)
interpretModal model w (MDiamond phi) = 
    any (\v -> accessibility model w v && interpretModal model v phi) (worlds model)
```

### 4. 直觉逻辑 / Intuitionistic Logic

**定义 4.1 (直觉逻辑 / Intuitionistic Logic)**
直觉逻辑拒绝排中律，强调构造性证明：

Intuitionistic logic rejects the law of excluded middle and emphasizes constructive proofs.

**定义 4.2 (海廷代数 / Heyting Algebra)**
海廷代数是格 $\langle H, \land, \lor, \to, 0, 1 \rangle$，满足：

A Heyting algebra is a lattice $\langle H, \land, \lor, \to, 0, 1 \rangle$ satisfying:

$$
x \land (x \to y) \leq y \\
x \to x = 1 \\
(x \to y) \land y = y \\
x \to (y \land z) = (x \to y) \land (x \to z)
$$

```haskell
-- 海廷代数 / Heyting Algebra
class HeytingAlgebra a where
    -- 格运算 / Lattice operations
    meet :: a -> a -> a
    join :: a -> a -> a
    
    -- 海廷蕴含 / Heyting implication
    implies :: a -> a -> a
    
    -- 常数 / Constants
    bottom :: a
    top :: a
    
    -- 海廷代数公理 / Heyting algebra axioms
    residuation :: a -> a -> a -> Bool
    identity :: a -> Bool
    absorption :: a -> a -> Bool
    distributivity :: a -> a -> a -> Bool

-- 直觉逻辑语义 / Intuitionistic Logic Semantics
interpretIntuitionistic :: HeytingAlgebra a => String -> a -> a
interpretIntuitionistic prop val = val

-- 直觉逻辑推理 / Intuitionistic Logic Reasoning
class IntuitionisticReasoning a where
    -- 构造性证明 / Constructive proof
    constructiveProof :: a -> Maybe Proof
    
    -- 反例构造 / Counterexample construction
    counterexample :: a -> Maybe Counterexample
    
    -- 直觉有效性 / Intuitionistic validity
    intuitionisticallyValid :: a -> Bool
```

### 5. 自然演绎系统 / Natural Deduction System

**定义 5.1 (推理规则 / Inference Rules)**
自然演绎系统的推理规则：

Inference rules of natural deduction system:

- **假设规则 / Assumption Rule**: $\frac{}{\phi \vdash \phi}$
- **蕴含引入 / Implication Introduction**: $\frac{\Gamma, \phi \vdash \psi}{\Gamma \vdash \phi \to \psi}$
- **蕴含消除 / Implication Elimination**: $\frac{\Gamma \vdash \phi \to \psi \quad \Gamma \vdash \phi}{\Gamma \vdash \psi}$
- **合取引入 / Conjunction Introduction**: $\frac{\Gamma \vdash \phi \quad \Gamma \vdash \psi}{\Gamma \vdash \phi \land \psi}$
- **合取消除 / Conjunction Elimination**: $\frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \phi} \quad \frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \psi}$

```haskell
-- 推理规则 / Inference Rules
data InferenceRule = 
    Assumption |                    -- 假设 / Assumption
    AndIntro |                     -- 合取引入 / Conjunction introduction
    AndElim1 |                     -- 合取消除1 / Conjunction elimination 1
    AndElim2 |                     -- 合取消除2 / Conjunction elimination 2
    OrIntro1 |                     -- 析取引入1 / Disjunction introduction 1
    OrIntro2 |                     -- 析取引入2 / Disjunction introduction 2
    OrElim |                       -- 析取消除 / Disjunction elimination
    ImpliesIntro |                 -- 蕴含引入 / Implication introduction
    ImpliesElim |                  -- 蕴含消除 / Implication elimination
    NotIntro |                     -- 否定引入 / Negation introduction
    NotElim |                      -- 否定消除 / Negation elimination
    IffIntro |                     -- 等价引入 / Equivalence introduction
    IffElim1 |                     -- 等价消除1 / Equivalence elimination 1
    IffElim2 |                     -- 等价消除2 / Equivalence elimination 2
    ForallIntro |                  -- 全称引入 / Universal introduction
    ForallElim |                   -- 全称消除 / Universal elimination
    ExistsIntro |                  -- 存在引入 / Existential introduction
    ExistsElim                     -- 存在消除 / Existential elimination

-- 证明步骤 / Proof Step
data ProofStep = ProofStep {
    stepNumber :: Int,
    formula :: Proposition,
    rule :: InferenceRule,
    premises :: [Int],
    discharged :: [Int]
}

-- 证明 / Proof
data Proof = Proof {
    steps :: [ProofStep],
    conclusion :: Proposition
}

-- 证明验证 / Proof Verification
verifyProof :: Proof -> Bool
verifyProof proof = all (verifyStep proof) (steps proof)

-- 步骤验证 / Step Verification
verifyStep :: Proof -> ProofStep -> Bool
verifyStep proof step = case rule step of
    Assumption -> True
    AndIntro -> length (premises step) == 2
    AndElim1 -> length (premises step) == 1
    AndElim2 -> length (premises step) == 1
    OrIntro1 -> length (premises step) == 1
    OrIntro2 -> length (premises step) == 1
    OrElim -> length (premises step) == 3
    ImpliesIntro -> length (premises step) == 1
    ImpliesElim -> length (premises step) == 2
    NotIntro -> length (premises step) == 1
    NotElim -> length (premises step) == 2
    IffIntro -> length (premises step) == 2
    IffElim1 -> length (premises step) == 1
    IffElim2 -> length (premises step) == 1
    ForallIntro -> length (premises step) == 1
    ForallElim -> length (premises step) == 1
    ExistsIntro -> length (premises step) == 1
    ExistsElim -> length (premises step) == 2
```

## 形式化证明 / Formal Proofs

### 定理 1 (命题逻辑基本定理 / Basic Propositional Logic Theorems)

**定理 1.1 (德摩根律 / De Morgan's Laws)**
对于任意命题 $\phi$ 和 $\psi$：

For any propositions $\phi$ and $\psi$:

$$
\neg(\phi \land \psi) \equiv \neg\phi \lor \neg\psi \\
\neg(\phi \lor \psi) \equiv \neg\phi \land \neg\psi
$$

**证明 / Proof**：
通过真值表或自然演绎系统证明 / Prove through truth tables or natural deduction system.

### 定理 2 (谓词逻辑基本定理 / Basic Predicate Logic Theorems)

**定理 2.1 (量词对偶律 / Quantifier Duality)**
对于任意公式 $\phi$：

For any formula $\phi$:

$$
\neg\forall x \phi \equiv \exists x \neg\phi \\
\neg\exists x \phi \equiv \forall x \neg\phi
$$

**证明 / Proof**：
通过语义定义证明 / Prove through semantic definitions.

### 定理 3 (模态逻辑基本定理 / Basic Modal Logic Theorems)

**定理 3.1 (模态对偶律 / Modal Duality)**
对于任意公式 $\phi$：

For any formula $\phi$:

$$
\Box \phi \equiv \neg\Diamond\neg\phi \\
\Diamond \phi \equiv \neg\Box\neg\phi
$$

**证明 / Proof**：
通过克里普克语义证明 / Prove through Kripke semantics.

## 应用领域 / Application Domains

### 1. 程序验证 / Program Verification

- **霍尔逻辑 / Hoare Logic**: 程序正确性证明 / Program correctness proof
- **模型检查 / Model Checking**: 系统性质验证 / System property verification
- **定理证明 / Theorem Proving**: 自动证明系统 / Automated proof systems

### 2. 人工智能 / Artificial Intelligence

- **知识表示 / Knowledge Representation**: 逻辑知识库 / Logical knowledge bases
- **自动推理 / Automated Reasoning**: 逻辑推理引擎 / Logical reasoning engines
- **专家系统 / Expert Systems**: 基于规则的推理 / Rule-based reasoning

### 3. 数据库理论 / Database Theory

- **关系代数 / Relational Algebra**: 数据库查询语言 / Database query languages
- **约束满足 / Constraint Satisfaction**: 数据完整性约束 / Data integrity constraints
- **查询优化 / Query Optimization**: 逻辑查询优化 / Logical query optimization

### 4. 语言学 / Linguistics

- **形式语义学 / Formal Semantics**: 自然语言语义 / Natural language semantics
- **语用学 / Pragmatics**: 语境依赖推理 / Context-dependent reasoning
- **计算语言学 / Computational Linguistics**: 自然语言处理 / Natural language processing

## 批判性分析 / Critical Analysis

### 1. 逻辑系统争议 / Logical System Controversies

**争议 1.1 (经典逻辑 vs 直觉逻辑 / Classical Logic vs Intuitionistic Logic)**:

- **排中律 / Law of Excluded Middle**: 经典逻辑接受，直觉逻辑拒绝 / Classical logic accepts, intuitionistic logic rejects
- **构造性 / Constructivity**: 直觉逻辑强调构造性证明 / Intuitionistic logic emphasizes constructive proofs

**争议 1.2 (模态逻辑解释 / Modal Logic Interpretation)**:

- **可能世界语义 / Possible World Semantics**: 克里普克语义的哲学基础 / Philosophical foundation of Kripke semantics
- **量化模态逻辑 / Quantified Modal Logic**: 跨世界同一性问题 / Cross-world identity problem

### 2. 理论局限性 / Theoretical Limitations

**局限性 2.1 (不完备性 / Incompleteness)**:

- **哥德尔不完备性定理 / Gödel's Incompleteness Theorems**: 形式系统的不完备性 / Incompleteness of formal systems
- **邱奇-图灵论题 / Church-Turing Thesis**: 可计算性的理论限制 / Theoretical limitations on computability

**局限性 2.2 (复杂性 / Complexity)**:

- **可满足性问题 / Satisfiability Problem**: SAT问题的NP完全性 / NP-completeness of SAT problem
- **模型检查复杂性 / Model Checking Complexity**: 状态爆炸问题 / State explosion problem

### 3. 前沿趋势 / Frontier Trends

**趋势 3.1 (高阶逻辑 / Higher-order Logic)**:

- **类型论 / Type Theory**: 高阶逻辑与类型论的结合 / Combination of higher-order logic and type theory
- **同伦类型论 / Homotopy Type Theory**: 拓扑与逻辑的结合 / Combination of topology and logic

**趋势 3.2 (非经典逻辑 / Non-classical Logics)**:

- **模糊逻辑 / Fuzzy Logic**: 不确定性推理 / Uncertain reasoning
- **时态逻辑 / Temporal Logic**: 时间相关推理 / Time-related reasoning
- **概率逻辑 / Probabilistic Logic**: 概率推理 / Probabilistic reasoning

## 交叉引用 / Cross References

- [数学基础 / Mathematical Foundations](./101-Mathematical-Foundations.md) - 数学理论基础 / Mathematical theoretical foundation
- [范畴论 / Category Theory](./106-Category-Theory.md) - 抽象代数结构 / Abstract algebraic structures
- [类型理论 / Type Theory](./104-Type-Theory.md) - 类型的形式化 / Formalization of types
- [自动机理论 / Automata Theory](./006-Automata-Theory.md) - 计算模型 / Computational models
- [信息论 / Information Theory](./110-Information-Theory.md) - 信息度量 / Information measurement
- [复杂性理论 / Complexity Theory](./112-Computational-Complexity-Theory.md) - 计算复杂性 / Computational complexity

## 参考文献 / References

1. Enderton, H.B. (2001). *A Mathematical Introduction to Logic*. Academic Press.
2. van Dalen, D. (2013). *Logic and Structure*. Springer.
3. Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
4. Troelstra, A.S., & Schwichtenberg, H. (2000). *Basic Proof Theory*. Cambridge University Press.
5. Girard, J.Y., Lafont, Y., & Taylor, P. (1989). *Proofs and Types*. Cambridge University Press.
6. Boolos, G.S., Burgess, J.P., & Jeffrey, R.C. (2007). *Computability and Logic*. Cambridge University Press.
7. Smullyan, R.M. (1995). *First-order Logic*. Dover Publications.
8. Fitting, M. (1996). *First-order Logic and Automated Theorem Proving*. Springer.

---

`#LogicalSystems #PropositionalLogic #PredicateLogic #ModalLogic #IntuitionisticLogic #NaturalDeduction #KripkeSemantics #HeytingAlgebra #ProgramVerification #ArtificialIntelligence #DatabaseTheory #Linguistics #HigherOrderLogic #NonClassicalLogics #Haskell #FormalMethods #MathematicalFoundations #CategoryTheory #TypeTheory #AutomataTheory #InformationTheory #ComplexityTheory`
