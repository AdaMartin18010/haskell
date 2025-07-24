# 3.12 常见误区 Common Pitfalls #LinearTypeTheory-3.12

## 3.12.1 理论误区 Theoretical Pitfalls #LinearTypeTheory-3.12.1

- 误解线性类型仅为“资源唯一性”，忽视其在逻辑、并发与安全中的理论基础。
- 忽略线性类型与仿射类型、依赖类型的本质区别。
- 误将线性逻辑与线性类型等价，未区分推理规则与类型系统实现。
- 忽视线性类型与范畴论、控制论的交叉影响。

## 3.12.2 工程陷阱 Engineering Pitfalls #LinearTypeTheory-3.12.2

- 工程实现中，线性类型系统设计不当导致资源泄漏或死锁。
- 忽视线性类型与垃圾回收、生命周期管理的协同。
- 在并发/分布式系统中，未充分建模资源转移与同步，影响系统一致性。

## 3.12.3 三语言相关注意事项 Language-specific Notes #LinearTypeTheory-3.12.3

- Haskell：线性类型扩展需关注类型推断与资源追踪。
- Rust：所有权与借用机制实现需关注线性资源的安全释放。
- Lean：形式化线性证明需关注资源消耗与归纳原理。

## 3.12.4 相关Tag

`# LinearTypeTheory #LinearTypeTheory-3 #LinearTypeTheory-3.12 #LinearTypeTheory-3.12.1 #LinearTypeTheory-3.12.2 #LinearTypeTheory-3.12.3`
