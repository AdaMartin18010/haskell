# 1.6 三语言对比 Comparison (Haskell/Rust/Lean)

Tag: #SyntaxSemantics-1.6

## 总览 Overview

- 语法层：表达能力、正交性、扩展机制
- 语义层：操作/指称/公理/范畴语义的可接入性
- 可验证性：类型系统强度与证明生态

## 对比表 Comparison Table

| 维度 Dimension | Haskell | Rust | Lean |
|---|---|---|---|
| 语法扩展 Syntax Extensions | GHC 扩展、模板Haskell | 宏、声明宏、属性 | 签名/战术、notation |
| 语义建模 Semantics | 惰性、纯函数、Monad/Arrow | 所有权/借用/生命周期、unsafe 边界 | 依赖类型、规约即证明 |
| 可验证性 Verifiability | 强类型 + QuickCheck/Verifiers | 编译期内存/并发安全 | 证明助手、内核校验 |
