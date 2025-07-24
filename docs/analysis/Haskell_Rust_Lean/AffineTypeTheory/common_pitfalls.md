# 4.12 常见误区 Common Pitfalls #AffineTypeTheory-4.12

## 4.12.1 理论误区 Theoretical Pitfalls #AffineTypeTheory-4.12.1

- 误将仿射类型等同于线性类型，忽视资源可丢弃性。
- 忽略仿射逻辑与类型系统的区别与联系。
- 误解仿射类型的“弱唯一性”，未区分“必须用一次”与“最多用一次”。
- 忽视仿射类型在并发、分布式系统中的资源释放语义。

## 4.12.2 工程陷阱 Engineering Pitfalls #AffineTypeTheory-4.12.2

- 资源释放不当，导致内存泄漏或资源悬挂。
- 仿射类型与所有权模型混用，易引发语义混淆。
- 在Rust等语言中，仿射类型与生命周期管理结合不当，导致悬垂指针。
- 忽视仿射类型与垃圾回收机制的协同。

## 4.12.3 三语言相关注意事项 Language-specific Notes #AffineTypeTheory-4.12.3

- Haskell：仿射类型扩展需关注类型推断与兼容性。
- Rust：所有权与借用机制实现复杂，需关注资源释放。
- Lean：形式化仿射证明需关注资源丢弃的完备性。

## 4.12.4 相关Tag

`# AffineTypeTheory #AffineTypeTheory-4 #AffineTypeTheory-4.12 #AffineTypeTheory-4.12.1 #AffineTypeTheory-4.12.2 #AffineTypeTheory-4.12.3`
