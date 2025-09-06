# 02-Coq 自动化与决策过程（Coq Automation & Decision Procedures）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1. 定义 Definition

### 1.1 核心定义 Core Definition

- **中文**：Coq 自动化是指通过内置的决策过程和 Hint 数据库来自动完成证明的技术。包括 auto/eauto 自动搜索、lia/nia 算术决策、ring/field 代数归约等，能够显著提高证明效率。
- **English**: Coq automation refers to techniques for automatically completing proofs through built-in decision procedures and Hint databases. This includes auto/eauto automatic search, lia/nia arithmetic decision, ring/field algebraic reduction, etc., which can significantly improve proof efficiency.

## 2. 自动化战术 Automation Tactics

### 2.1 基础自动化 Basic Automation

- **auto/eauto**: 基于 Hint 的自动搜索 (Hint-based automatic search)
  - `auto`: 基础自动搜索 (Basic automatic search)
  - `eauto`: 扩展自动搜索，`eauto 8` 控制深度 (Extended automatic search with depth control)

### 2.2 专用决策过程 Specialized Decision Procedures

- **firstorder**: 一阶逻辑自动化 (First-order logic automation)
- **congruence**: 等式闭包 (Equality closure)
- **ring/field**: 环/域上的多项式归约 (Polynomial reduction over rings/fields)
- **lia/nia**: 线性/非线性整数算术 (Linear/non-linear integer arithmetic)

## 3. Hint 与数据库 Hints & Databases

### 3.1 Hint 类型 Hint Types

- **Hint Resolve**: 解决目标的 Hint (Hints for resolving goals)
- **Hint Constructors**: 构造器 Hint (Constructor hints)
- **Hint Rewrite**: 重写 Hint (Rewrite hints)
- **自定义数据库**: `:core :db` 等 (Custom databases: `:core :db` etc.)

### 3.2 工程化建议 Engineering Guidelines

- **最小必要 Hint**: 在库中导出最小必要 Hint，避免全局性能退化 (Export minimal necessary hints in libraries to avoid global performance degradation)
- **精准开放**: 利用 `#[global] Hint` 精准开放；避免污染全局搜索 (Precise opening using `#[global] Hint`; avoid polluting global search)
- **关键引理**: 为关键引理提供 `Hint Rewrite`（左右方向谨慎）(Provide `Hint Rewrite` for key lemmas, being careful about left/right directions)

## 4. 工程策略 Engineering Strategies

### 4.1 战术选择策略 Tactic Selection Strategy

- **简单目标**: 将"简单目标"交给 auto/eauto/lia (Delegate "simple goals" to auto/eauto/lia)
- **结构性目标**: 把"结构性目标"留给专用战术 (Leave "structural goals" to specialized tactics)

### 4.2 性能优化 Performance Optimization

```coq
(* 性能优化的 Hint 使用 *)
#[global] Hint Resolve addn0 : core.
#[global] Hint Rewrite addn0 : core.

(* 避免过度使用 *)
(* 不要为每个引理都添加 Hint *)
```

## 5. 代码示例 Code Examples

### 5.1 基础自动化示例 Basic Automation Examples

```coq
Require Import Lia.

(* 线性算术自动化 *)
Lemma ex_ineq (x y : Z) : x <= y -> x <= y + 2.
Proof. lia. Qed.

(* 自动搜索示例 *)
Lemma auto_example (P Q : Prop) : P -> Q -> P /\ Q.
Proof.
  auto.
Qed.

(* 扩展自动搜索 *)
Lemma eauto_example (P Q R : Prop) : 
  P -> (P -> Q) -> (Q -> R) -> R.
Proof.
  eauto 3.
Qed.
```

### 5.2 高级自动化示例 Advanced Automation Examples

```coq
(* 一阶逻辑自动化 *)
Lemma firstorder_example (P Q R : Prop) :
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  firstorder.
Qed.

(* 环理论自动化 *)
Require Import Ring.
Lemma ring_example (x y : Z) : (x + y) * (x - y) = x * x - y * y.
Proof.
  ring.
Qed.
```

## 6. 对比分析 Comparison

### 6.1 自动化战术对比

| 战术 | 适用场景 | 性能 | 可靠性 |
|------|----------|------|--------|
| auto | 简单目标 | 快 | 高 |
| eauto | 复杂目标 | 中等 | 中等 |
| lia | 线性算术 | 快 | 高 |
| firstorder | 一阶逻辑 | 中等 | 高 |
| ring | 环理论 | 快 | 高 |

## 7. 争议与批判 Controversies & Critique

### 7.1 自动化依赖问题

- **中文**：过度依赖自动化可能导致证明不可读，难以维护
- **English**: Over-reliance on automation may lead to unreadable proofs that are difficult to maintain

### 7.2 性能问题

- **中文**：某些自动化战术可能消耗大量时间和内存
- **English**: Some automation tactics may consume significant time and memory

## 8. 前沿趋势 Frontier Trends

### 8.1 机器学习辅助

- **中文**：使用机器学习技术改进自动化战术
- **English**: Using machine learning techniques to improve automation tactics

### 8.2 并行化

- **中文**：并行化自动化搜索过程
- **English**: Parallelizing automation search processes

## 9. 交叉引用 Cross References

- [Coq 形式系统 Coq Formal System](./01-Coq-Formal-System.md)
- [Coq 定义 Coq Definitions](./04-Coq-Definitions.md)
- [Coq 策略 Coq Tactics](./03-Coq-Tactics.md)
- [Coq 示例 Coq Examples](./05-Coq-Examples.md)

## 10. 参考文献 References

### 10.1 核心文档 Core Documentation

- **Coq Reference Manual**: 官方参考手册 (Official reference manual)
- **coq/hammer 文档**: Hammer 自动化工具 (Hammer automation tool)
- **MathComp/SSReflect 自动化实践**: 数学组件自动化实践 (Mathematical Components automation practices)

### 10.2 在线资源 Online Resources

- [Coq Automation Documentation](https://coq.inria.fr/refman/proof-engine/automation.html)
- [SSReflect Manual](https://math-comp.github.io/htmldoc/mathcomp.ssreflect.ssreflect.html)

---

## 总结 Summary

Coq 自动化是提高证明效率的重要工具，通过合理使用各种自动化战术和 Hint 数据库，可以显著减少手动证明的工作量。然而，需要平衡自动化程度和证明的可读性，避免过度依赖自动化导致的问题。

---

`# Coq #Automation #DecisionProcedures #Tactics #Hints #FormalVerification`
