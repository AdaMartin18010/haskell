# 1.6 三语言对比 Comparison (Haskell/Rust/Lean)

Tag: #MappingTheoryLanguage-1.6

## 总览 Overview

- 从理论构造到语言机制的对应
- 表达力/可判定性/可验证性/工程复杂度的权衡

## 对比表 Comparison Table

| 维度 Dimension | Haskell | Rust | Lean |
|---|---|---|---|
| 理论承载 Theoretical Carrier | Category/Type Theory/Effects | Linear/Affine ideas, Type Theory | Dependent Type Theory/Proof Theory |
| 落地机制 Realization | Monad/TypeFamilies/LinearTypes | Ownership/Borrowing/Traits/Lifetimes | Inductive families/Type classes |
| 验证 Verification | QuickCheck/Coq/Agda bridges | RustBelt/Prusti/Miri | Kernel-checked proofs |
| 复杂度 Complexity | 中（抽象高、工具成熟） | 中-高（系统工程） | 高（证明负担） |
