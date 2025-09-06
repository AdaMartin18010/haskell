# 6.12 常见误区 Common Pitfalls #HOTT-6.12

## 6.12.1 理论误区 Theoretical Pitfalls #HOTT-6.12.1

- 误解同伦等价与类型等价，未区分“路径”等价与“结构”等价。
- 忽视高阶路径（higher path）与高阶等价的复杂性。
- 误将HOTT视为传统类型论的简单扩展，忽略其范畴论与拓扑学基础。
- 忽略Univalence公理的哲学与工程含义。

## 6.12.2 工程陷阱 Engineering Pitfalls #HOTT-6.12.2

- 在工程实现中，未正确处理高阶等价与归纳原理，导致证明不完备。
- 忽视HOTT在实际编程语言中的类型推断与自动化证明难题。
- 形式化系统中，未充分利用HOTT的同伦结构，导致表达力受限。

## 6.12.3 三语言相关注意事项 Language-specific Notes #HOTT-6.12.3

- Haskell：缺乏原生HOTT支持，需依赖外部库或扩展，表达力有限。
- Rust：类型系统不支持高阶同伦结构，工程实现需关注安全与表达能力。
- Lean：Lean 3/4对HOTT有一定支持，但需关注Univalence等公理的实现与证明。

## 6.12.4 相关Tag

`# HOTT #HOTT-6 #HOTT-6.12 #HOTT-6.12.1 #HOTT-6.12.2 #HOTT-6.12.3`
