# 1.6 三语言对比 Comparison (Haskell/Rust/Lean)

Tag: #SemanticModels-1.6

## 总览 Overview

- 语义范式：操作/指称/公理/范畴/抽象解释/逻辑关系
- 组合性、可验证性、工程适配度

## 对比表 Comparison Table

| 维度 Dimension | Haskell | Rust | Lean |
|---|---|---|---|
| 语义承载 Semantic Carrier | Monad/Arrow/Category，惰性 | 所有权/借用 + MIR/内存模型 | 依赖类型/归纳家族/核心规约 |
| 组合性 Compositionality | 强（指称/范畴） | 中（操作/类型导向） | 强（证明/公理/范畴） |
| 等价与证明 Equivalence & Proofs | 逻辑关系/自由定理 | 运行时/内存模型等价 | 机器检验证明/语义充足性 |
| 工具 Tooling | GHC/Core/Coq/Agda 接入 | RustBelt/Prusti/Miri | 内核/Mathlib/Elab |
