# 12.1 递归-可计算理论的定义 Definition of Recursion & Computability Theory #RecursionComputabilityTheory-12.1

## 中文定义

递归-可计算理论是数理逻辑和理论计算机科学的分支，研究可计算函数、递归过程、算法的本质与极限。它关注于可计算性、可判定性、图灵机、λ演算、递归函数、不可判定问题等核心概念。

## English Definition

Recursion & Computability Theory is a branch of mathematical logic and theoretical computer science that studies computable functions, recursive processes, and the nature and limits of algorithms. It focuses on computability, decidability, Turing machines, lambda calculus, recursive functions, and undecidable problems.

## 12.1.1 理论体系结构 Theoretical Framework #RecursionComputabilityTheory-12.1.1

- 可计算函数（Computable Functions）：原始递归、μ递归、λ演算。
- 计算模型（Computation Models）：图灵机、λ演算、递归函数、自动机。
- 可判定性（Decidability）：判定问题、不可判定问题。
- 不可计算性（Uncomputability）：停机问题、哥德尔不完备性。

## 12.1.2 形式化定义 Formalization #RecursionComputabilityTheory-12.1.2

- 一个函数f是可计算的，当且仅当存在图灵机/λ项/递归过程能在有限步内输出f(x)。
- 在Haskell/Rust/Lean中，可计算性可通过递归函数、类型系统、归纳定义等表达。

## 12.1.3 三语言对比 Haskell/Rust/Lean Comparison #RecursionComputabilityTheory-12.1.3

| 语言 | 递归表达 | 可计算性建模 | 不可判定性 | 工程应用 |
|------|----------|--------------|------------|----------|
| Haskell | 递归函数/类型 | λ演算/类型级递归 | 可表达不可终止 | 抽象算法建模 |
| Rust    | 递归函数/trait | trait递归/宏 | 需手动防止死循环 | 系统级递归实现 |
| Lean    | 归纳/递归定义 | 依赖类型/归纳 | 可形式化不可判定性 | 形式化证明与可计算性分析 |

## 12.1.4 相关Tag

`# RecursionComputabilityTheory #RecursionComputabilityTheory-12 #RecursionComputabilityTheory-12.1 #RecursionComputabilityTheory-12.1.1 #RecursionComputabilityTheory-12.1.2 #RecursionComputabilityTheory-12.1.3`
