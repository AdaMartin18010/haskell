# 6.10 形式化证明与论证 Formal Proofs & Arguments #HOTT-6.10

## 核心定理 Core Theorems

- **中文**：等价类型结构、单值性公理、归纳原理等。
- **English**: Equivalence type structures, univalence axiom, induction principle, etc.

## 典型证明 Typical Proofs

```lean
-- Lean: 单值性公理与等价类型证明（伪代码）
theorem univalence_axiom (A B : Type) : (A ≃ B) ≃ (A = B) := ...
```

## 工程实现 Engineering Implementation

- **中文**：Lean、Coq等可形式化HOTT的等价类型、单值性公理等。
- **English**: Lean, Coq, etc., can formalize equivalence types, univalence axiom, and other HOTT theorems.

## 交叉引用 Cross References

- [类型理论 Type Theory](../TypeTheory/README.md)
- [定理与证明 Theorems & Proofs](../Theorems_Proofs/README.md)
