# 12.12 常见误区 Common Pitfalls #RecursionComputabilityTheory-12.12

## 12.12.1 理论误区 Theoretical Pitfalls #RecursionComputabilityTheory-12.12.1

- 混淆递归与可计算性的边界，未区分递归函数与可判定问题。
- 忽视图灵完备性与实际可实现性的差异。
- 误解Church-Turing论题的适用范围。
- 忽略不可判定性与不可计算性的工程影响。

## 12.12.2 工程陷阱 Engineering Pitfalls #RecursionComputabilityTheory-12.12.2

- 在工程实现中，递归深度未受控，导致栈溢出。
- 忽视尾递归优化与编译器支持。
- 误用递归导致性能瓶颈或不可终止。

## 12.12.3 三语言相关注意事项 Language-specific Notes #RecursionComputabilityTheory-12.12.3

- Haskell：惰性求值下递归与无限结构需关注空间泄漏。
- Rust：递归实现需关注栈空间与生命周期，尾递归优化有限。
- Lean：形式化递归定义需关注可终止性证明与归纳原理。

## 12.12.4 相关Tag

`# RecursionComputabilityTheory #RecursionComputabilityTheory-12 #RecursionComputabilityTheory-12.12 #RecursionComputabilityTheory-12.12.1 #RecursionComputabilityTheory-12.12.2 #RecursionComputabilityTheory-12.12.3`
