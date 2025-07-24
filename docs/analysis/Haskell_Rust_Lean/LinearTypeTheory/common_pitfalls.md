# 3.12 常见误区 Common Pitfalls #LinearTypeTheory-3.12

## 3.12.1 理论误区 Theoretical Pitfalls #LinearTypeTheory-3.12.1

- 误将线性类型等同于普通类型，忽视资源唯一性与消耗性。
- 忽略线性逻辑与类型系统的严格约束。

## 3.12.2 工程陷阱 Engineering Pitfalls #LinearTypeTheory-3.12.2

- 资源管理不当，导致内存泄漏或资源竞争。
- 线性类型与所有权模型混用，易引发语义混淆。

## 3.12.3 三语言相关注意事项 Language-specific Notes #LinearTypeTheory-3.12.3

- Haskell：线性类型扩展需关注类型推断与兼容性。
- Rust：所有权与借用机制实现复杂，需关注生命周期。
- Lean：形式化线性证明需关注资源流动的完备性。

## 3.12.4 相关Tag

`# LinearTypeTheory #LinearTypeTheory-3 #LinearTypeTheory-3.12 #LinearTypeTheory-3.12.1 #LinearTypeTheory-3.12.2 #LinearTypeTheory-3.12.3`
