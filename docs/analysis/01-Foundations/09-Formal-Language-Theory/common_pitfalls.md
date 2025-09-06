# 9.12 常见误区 Common Pitfalls #FormalLanguageTheory-9.12

## 目录 Table of Contents

- 9.12.1 理论误区 Theoretical Pitfalls
- 9.12.2 工程陷阱 Engineering Pitfalls
- 9.12.3 三语言相关注意事项 Language-specific Notes

## 9.12.1 理论误区 Theoretical Pitfalls #FormalLanguageTheory-9.12.1

- 误解形式语言仅为“编程语言”，忽视其在计算理论、自动机理论中的基础地位。
- 忽略语法、语义、语用三层次的区分。
- 误将正则语言、上下文无关语言等价，未区分其表达能力与限制。
- 忽视泵引理、不可判定性等核心定理的工程意义。

## 9.12.2 工程陷阱 Engineering Pitfalls #FormalLanguageTheory-9.12.2

- 工程实现中，语法分析器与语义分析器分离不当，导致错误难以定位。
- 忽视边界条件与异常输入，导致解析器不健壮。
- 在多语言系统中，未充分建模语法与语义的映射，影响系统一致性。

## 9.12.3 三语言相关注意事项 Language-specific Notes #FormalLanguageTheory-9.12.3

- Haskell：解析器组合子需关注类型安全与表达能力。
- Rust：高性能语法分析需关注内存安全与并发。
- Lean：形式化语言定义需关注语法、语义与证明的完备性。

## 9.12.4 相关Tag

`# FormalLanguageTheory #FormalLanguageTheory-9 #FormalLanguageTheory-9.12 #FormalLanguageTheory-9.12.1 #FormalLanguageTheory-9.12.2 #FormalLanguageTheory-9.12.3`
