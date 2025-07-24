# 同伦类型论 Homotopy Type Theory (HOTT)

## 定义 Definition

- **中文**：同伦类型论是将同伦论与类型论结合的理论，强调等价、路径和高阶结构，推动了数学基础和形式化证明的发展。
- **English**: Homotopy type theory (HOTT) is a theory combining homotopy theory and type theory, emphasizing equivalence, paths, and higher structures, advancing the foundations of mathematics and formal proofs.

## 历史与发展 History & Development

- **中文**：HOTT于2010年前后兴起，受到Voevodsky等人的推动，成为Univalent Foundations计划的核心。
- **English**: HOTT emerged around 2010, driven by Voevodsky and others, becoming the core of the Univalent Foundations program.

## 哲科视角的特性分析 Philosophical-Scientific Feature Analysis

- HOTT体现了等价本体论和结构主义，强调“路径”等价的哲学意义。
- HOTT embodies equivalence ontology and structuralism, emphasizing the philosophical significance of "path" equivalence.

## 应用 Applications

- 数学基础、定理证明、形式化验证、高阶结构建模等。
- Foundations of mathematics, theorem proving, formal verification, higher structure modeling, etc.

## 例子 Examples

```lean
-- Lean中的等价类型
structure Equiv (A B : Type) :=
  (to_fun    : A → B)
  (inv_fun   : B → A)
  (left_inv  : ∀ x, inv_fun (to_fun x) = x)
  (right_inv : ∀ y, to_fun (inv_fun y) = y)
```

## 相关理论 Related Theories

- 类型理论、范畴论、等价理论、模型论等。
- Type theory, category theory, equivalence theory, model theory, etc.

## 参考文献 References

- [Wikipedia: Homotopy Type Theory](https://en.wikipedia.org/wiki/Homotopy_type_theory)
- [The Univalent Foundations Program, IAS]
- [Lean Theorem Prover Documentation](https://leanprover.github.io/)

## 哲学批判与争议 Philosophical Critique & Controversies

- **中文**：HOTT在哲学上引发了关于等价本体论和结构主义的争论，部分学者质疑其在传统数学基础中的地位。
- **English**: HOTT has sparked debates about equivalence ontology and structuralism, with some scholars questioning its place in traditional mathematical foundations.

## 国际对比与标准 International Comparison & Standards

- **中文**：Lean、Coq等证明助手支持HOTT，Haskell和Rust相关支持有限。Wiki和Univalent Foundations计划为HOTT提供国际标准。
- **English**: Proof assistants like Lean and Coq support HOTT, while Haskell and Rust have limited support. Wiki and the Univalent Foundations program provide international standards for HOTT.

## 形式化证明与论证 Formal Proofs & Arguments

- **中文**：HOTT的等价类型、单值性公理等可在Lean中形式化证明，推动了可验证数学的发展。
- **English**: HOTT's equivalence types and univalence axiom can be formally proved in Lean, advancing verifiable mathematics.

## 经典人物与思想 Key Figures & Ideas

- **中文**：Vladimir Voevodsky推动了HOTT和Univalent Foundations的发展。
- **English**: Vladimir Voevodsky advanced the development of HOTT and the Univalent Foundations.

## 批判性小结 Critical Summary

- **中文**：HOTT为数学基础和形式化证明带来创新，但其复杂性和接受度仍有待提升。
- **English**: HOTT brings innovation to mathematical foundations and formal proofs, but its complexity and acceptance still need improvement.
