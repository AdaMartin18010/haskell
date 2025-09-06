# 04-Coq 定义与核心概念（Coq Definitions & Core Concepts）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1. 定义 Definition

### 1.1 核心定义 Core Definition

- **中文**：Coq 是基于构造演算（Calculus of Inductive Constructions, CIC）的交互式定理证明助手，支持依赖类型、归纳类型和形式化证明。Coq 提供了强大的类型系统，能够表达复杂的数学概念和程序规范。
- **English**: Coq is an interactive theorem prover based on the Calculus of Inductive Constructions (CIC), supporting dependent types, inductive types, and formal proofs. Coq provides a powerful type system capable of expressing complex mathematical concepts and program specifications.

## 2. 判断与语法 Judgements & Syntax

### 2.1 类型判断 Type Judgements

- **类型归属**: $\Gamma \vdash A : s$ (Type inhabitation)
- **项归属**: $\Gamma \vdash a : A$ (Term inhabitation)  
- **宇宙层级**: $s \in \{Prop, Set, Type_0, Type_1, ...\}$ (Universe levels)

### 2.2 核心类型构造器 Core Type Constructors

- **依赖函数类型**: $\Pi$-types (Dependent function types)
- **依赖对类型**: $\Sigma$-types (Dependent pair types, encodable via records/existentials)
- **恒等类型**: $eq$ (Identity types)

## 3. 宇宙与层级 Universes & Hierarchy

### 3.1 宇宙层级 Universe Hierarchy

- **层级避免悖论**: $Type_0 : Type_1 : Type_2 : ...$ (Hierarchy prevents paradoxes)
- **宇宙多态**: Universe Polymorphism (Universe polymorphism)

### 3.2 Prop 与 Set Prop vs Set

- **Prop 宇宙**: 面向命题/证明（可擦除）(Prop universe: for propositions/proofs, erasable)
- **Set/Type 宇宙**: 面向数据/计算 (Set/Type universes: for data/computation)

## 4. 归纳/协归纳类型 Inductive/Coinductive Types

### 4.1 归纳类型 Inductive Types

- **Inductive 定义**: 数据与归纳原理 (Inductive definitions: data and induction principles)
- **CoInductive 定义**: 无限对象与核递归 (CoInductive definitions: infinite objects and corecursion)

### 4.2 高级特性 Advanced Features

- **互递归**: Mutual recursion (mutual)
- **索引族**: Indexed families (indexed families)
- **依赖消解**: Dependent elimination (dependent elimination)
- **模式匹配**: Pattern matching (pattern matching)

## 5. 递归与守恒 Recursion & Guardedness

### 5.1 递归定义 Recursive Definitions

- **Fixpoint**: 结构递归 (Fixpoint: structural recursion)
- **Program Fixpoint**: 可证明终止性 (Program Fixpoint: provable termination)

### 5.2 协递归 Co-recursion

- **CoFixpoint**: 要求守恒（productivity）(CoFixpoint: requires productivity)

## 6. 证明引擎与策略 Proof Engine & Tactics

### 6.1 基础策略 Basic Tactics

- **基础 tactics**: `intro`/`induction`/`destruct`/`rewrite`/`reflexivity`
- **自动化**: `auto`/`eauto`; `lia`/`nia`; `ring`/`field`; `firstorder`

### 6.2 高级策略 Advanced Tactics

- **Ltac**: 策略语言 (Ltac: tactic language)
- **SSReflect**: 结构化反射 (SSReflect: structured reflection)
- **Elpi**: 扩展策略 (Elpi: extended tactics)
- **Hint 数据库**: Hint databases (Hint databases)
- **规范结构**: Canonical structures (MathComp) (canonical structures)

## 7. 抽取与计算 Extraction & Computation

### 7.1 程序抽取 Program Extraction

- **Extraction**: 到 OCaml/Haskell/Scheme (`Extraction` to OCaml/Haskell/Scheme)
- **证据擦除**: 保证运行时纯净 (Evidence erasure: ensures runtime purity)

### 7.2 计算规则 Computation Rules

- **归约规则**: $\beta$/$\delta$/$\iota$/$\zeta$ 归约 (Reduction rules: β/δ/ι/ζ reduction)
- **计算策略**: `cbv`/`cbn`/`lazy` 策略 (Computation strategies: `cbv`/`cbn`/`lazy` tactics)

## 8. 模块化与依赖管理 Modularization & Dependency Management

### 8.1 模块系统 Module System

- **Modules/Functors**: 模块和函子 (Modules/Functors)
- **Sections**: 上下文管理 (Sections: context management)

### 8.2 依赖管理 Dependency Management

- **OPAM**: 包管理器 (OPAM: package manager)
- **Coq Platform**: 平台管理 (Coq Platform: platform management)

## 9. 同伦类型论关系 Relations to HoTT/Univalence

### 9.1 HoTT 扩展 HoTT Extensions

- **HoTT/Univalence 扩展**: 可加载扩展 (Loadable HoTT/Univalence extensions)
- **Cubical**: 立方类型论 (Cubical: cubical type theory)

### 9.2 等价语义 Equivalence Semantics

- **等价即相等**: 可选语义 (Equivalence as equality: optional semantics)

## 10. 交叉引用 Cross References

- [Coq 形式系统 Coq Formal System](./01-Coq-Formal-System.md)
- [Coq 自动化 Coq Automation](./02-Coq-Automation.md)
- [Coq 策略 Coq Tactics](./03-Coq-Tactics.md)
- [Coq 示例 Coq Examples](./05-Coq-Examples.md)

## 11. 参考文献 References

### 11.1 核心文档 Core Documentation

- **Coq Reference Manual**: 官方参考手册 (Official reference manual)
- **Software Foundations**: 软件基础教程 (Software Foundations tutorial)
- **Mathematical Components**: 数学组件库 (Mathematical Components library)
- **Certified Programming with Dependent Types**: 依赖类型认证编程 (Certified Programming with Dependent Types)

### 11.2 在线资源 Online Resources

- [Coq Documentation](https://coq.inria.fr/documentation)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Mathematical Components](https://math-comp.github.io/)

---

`# Coq #Definitions #CIC #DependentTypes #FormalVerification #TypeTheory`
