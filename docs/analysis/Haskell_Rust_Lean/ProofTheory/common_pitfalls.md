# 7.12 常见误区 Common Pitfalls #ProofTheory-7.12

## 7.12.1 理论误区 Theoretical Pitfalls #ProofTheory-7.12.1

- 误解证明论仅为“形式推理”，忽视其与类型论、模型论的深度联系。
- 忽略证明系统（如自然演绎、序列演算）之间的本质差异。
- 误将“证明”与“计算”混为一谈，未区分证明对象与计算过程。
- 忽视一致性、完备性、可判定性等核心定理的工程意义。

## 7.12.2 工程陷阱 Engineering Pitfalls #ProofTheory-7.12.2

- 工程实现中，证明系统与实际需求脱节，导致自动化证明难以落地。
- 忽视证明的可读性与可维护性，影响工程协作。
- 在形式化验证中，未正确建模证明对象与推理规则，导致验证失效。

## 7.12.3 三语言相关注意事项 Language-specific Notes #ProofTheory-7.12.3

- Haskell：类型级证明需关注类型推断与证明对象的映射。
- Rust：安全属性证明需结合所有权、生命周期与类型系统。
- Lean：形式化证明需关注证明对象、推理规则与一致性。

## 7.12.4 相关Tag

`# ProofTheory #ProofTheory-7 #ProofTheory-7.12 #ProofTheory-7.12.1 #ProofTheory-7.12.2 #ProofTheory-7.12.3`
