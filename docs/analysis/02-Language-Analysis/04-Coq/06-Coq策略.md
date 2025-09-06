# 04-Coq 战术与策略（Coq Tactics & Strategies）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1. 定义 Definition

### 1.1 核心定义 Core Definition

- **中文**：Coq 战术是用于构建证明的基本工具，包括基础战术、自动化战术和结构化战术。策略是指使用这些战术的方法和技巧，包括 Ltac 策略语言和 SSReflect 证明风格。
- **English**: Coq tactics are basic tools for constructing proofs, including basic tactics, automation tactics, and structured tactics. Strategies refer to methods and techniques for using these tactics, including the Ltac strategy language and SSReflect proof style.

## 2. 战术综览 Tactics Overview

### 2.1 基础战术 Basic Tactics

- **intro/intros**: 引入假设 (Introduce hypotheses)
- **apply**: 应用引理 (Apply lemmas)
- **exact**: 精确匹配 (Exact matching)
- **refine**: 细化证明 (Refine proofs)
- **destruct**: 案例分析 (Case analysis)
- **inversion**: 反演分析 (Inversion analysis)
- **induction**: 归纳证明 (Inductive proofs)
- **rewrite**: 重写 (Rewriting)
- **subst**: 替换 (Substitution)
- **simpl**: 简化 (Simplification)
- **reflexivity**: 自反性 (Reflexivity)

### 2.2 自动化战术 Automation Tactics

- **auto/eauto**: 自动搜索 (Automatic search)
- **firstorder**: 一阶逻辑 (First-order logic)
- **lia/nia**: 线性/非线性算术 (Linear/non-linear arithmetic)
- **ring/field**: 环/域理论 (Ring/field theory)
- **congruence**: 同余 (Congruence)
- **cbn/cbv**: 计算策略 (Computation strategies)

### 2.3 结构化战术 Structured Tactics

- **assert**: 断言 (Assertion)
- **pose proof**: 证明定位 (Proof positioning)
- **specialize**: 特化 (Specialization)
- **generalize dependent**: 依赖泛化 (Dependent generalization)
- **remember**: 记忆 (Remembering)

## 3. Ltac 与策略语言 Ltac & Strategy Language

### 3.1 Ltac 基础 Ltac Basics

- **自定义复合战术**: 创建可重用的战术组合 (Custom composite tactics: create reusable tactic combinations)
- **模式匹配**: `match goal with ... end` (Pattern matching: `match goal with ... end`)

```coq
(* Ltac 示例 *)
Ltac solve_trivial :=
  match goal with
  | |- ?P => exact I
  | |- _ => auto
  end.
```

### 3.2 Hint 数据库 Hint Databases

- **Hint Resolve**: 解决目标的 Hint (Hints for resolving goals)
- **Hint Rewrite**: 重写 Hint (Rewrite hints)

```coq
(* Hint 数据库示例 *)
#[global] Hint Resolve addn0 : core.
#[global] Hint Rewrite addn0 : core.
```

### 3.3 结构化证明 Structured Proofs

- **复合战术**: `;` 复合多个战术 (Composite tactics: `;` combines multiple tactics)
- **重复战术**: `repeat` 重复执行 (Repeat tactics: `repeat` executes repeatedly)
- **宽松战术**: `try` 允许失败 (Loose tactics: `try` allows failure)

```coq
(* 结构化证明示例 *)
Lemma structured_proof (P Q R : Prop) : P -> Q -> R -> P /\ Q /\ R.
Proof.
  intros H1 H2 H3.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.
```

## 4. SSReflect 风格 SSReflect Style

### 4.1 SSReflect 记号 SSReflect Notation

- **move=>**: 移动和引入 (Move and introduce)
- **case**: 案例分析 (Case analysis)
- **elim**: 消除 (Elimination)
- **rewrite**: 重写 (Rewriting)
- **have**: 拥有 (Have)
- **suff**: 充分 (Sufficient)

### 4.2 高级特性 Advanced Features

- **Canonical Structures**: 规范结构 (Canonical structures)
- **小战术库**: 数学组件战术库 (Small tactic libraries: Mathematical Components tactic libraries)
- **MathComp 生态**: 数学组件生态系统 (MathComp ecosystem)

## 5. 代码示例 Code Examples

### 5.1 基础战术示例 Basic Tactics Examples

```coq
(* 基础证明 *)
Lemma basic_proof (P Q : Prop) : P -> Q -> P /\ Q.
Proof.
  intros H1 H2.
  split.
  - exact H1.
  - exact H2.
Qed.

(* 归纳证明 *)
Lemma induction_example (n : nat) : n + 0 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
```

### 5.2 SSReflect 示例 SSReflect Examples

```coq
From mathcomp Require Import all_ssreflect.

(* SSReflect 风格证明 *)
Lemma addn0_ssr n : n + 0 = n.
Proof.
  by elim: n => // n IH; rewrite addSn IH.
Qed.

(* 更复杂的 SSReflect 证明 *)
Lemma list_length_cons (A : Type) (x : A) (l : list A) :
  length (x :: l) = S (length l).
Proof.
  by rewrite /=.
Qed.
```

### 5.3 Ltac 高级示例 Advanced Ltac Examples

```coq
(* 复杂的 Ltac 战术 *)
Ltac solve_arithmetic :=
  match goal with
  | |- ?x + 0 = ?x => reflexivity
  | |- ?x * 1 = ?x => reflexivity
  | |- ?x <= ?x => apply le_refl
  | |- _ => lia
  end.

(* 使用自定义战术 *)
Lemma arithmetic_example (x : nat) : x + 0 = x.
Proof.
  solve_arithmetic.
Qed.
```

## 6. 对比分析 Comparison

### 6.1 战术风格对比

| 风格 | 优点 | 缺点 | 适用场景 |
|------|------|------|----------|
| 基础战术 | 直观易懂 | 冗长 | 简单证明 |
| SSReflect | 简洁高效 | 学习曲线陡峭 | 复杂证明 |
| Ltac | 灵活强大 | 复杂难懂 | 重复性任务 |

## 7. 争议与批判 Controversies & Critique

### 7.1 战术复杂性

- **中文**：某些战术过于复杂，难以理解和维护
- **English**: Some tactics are too complex and difficult to understand and maintain

### 7.2 风格统一性

- **中文**：不同证明风格之间的转换可能造成混乱
- **English**: Transitions between different proof styles may cause confusion

## 8. 前沿趋势 Frontier Trends

### 8.1 战术自动化

- **中文**：发展更智能的战术自动化系统
- **English**: Developing more intelligent tactic automation systems

### 8.2 证明风格融合

- **中文**：融合不同证明风格的优势
- **English**: Combining advantages of different proof styles

## 9. 交叉引用 Cross References

- [Coq 形式系统 Coq Formal System](./01-Coq-Formal-System.md)
- [Coq 自动化 Coq Automation](./02-Coq-Automation.md)
- [Coq 生态 Coq Ecosystem](./03-Coq-Ecosystem.md)
- [Coq 定义 Coq Definitions](./04-Coq-Definitions.md)

## 10. 参考文献 References

### 10.1 核心文档 Core Documentation

- **Coq Reference Manual**: 官方参考手册 (Official reference manual)
- **SSReflect manual**: SSReflect 手册 (SSReflect manual)
- **Software Foundations**: 软件基础教程 (Software Foundations tutorial)
- **MathComp book**: 数学组件书籍 (Mathematical Components book)

### 10.2 在线资源 Online Resources

- [Coq Tactics Documentation](https://coq.inria.fr/refman/proof-engine/tactics.html)
- [SSReflect Manual](https://math-comp.github.io/htmldoc/mathcomp.ssreflect.ssreflect.html)

---

## 总结 Summary

Coq 战术与策略是构建形式化证明的核心工具，通过合理使用基础战术、自动化战术和结构化战术，可以高效地完成复杂的证明任务。SSReflect 风格和 Ltac 策略语言为证明提供了更高级的抽象，但需要平衡简洁性和可读性。

---

`# Coq #Tactics #Strategies #SSReflect #Ltac #FormalVerification #ProofEngineering`
