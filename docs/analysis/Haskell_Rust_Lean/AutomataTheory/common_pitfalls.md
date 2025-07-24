# 10.12 常见误区 Common Pitfalls #AutomataTheory-10.12

## 10.12.1 理论误区 Theoretical Pitfalls #AutomataTheory-10.12.1

- 误解自动机仅为“有限状态机”，忽视其在计算理论中的广泛类型（如PDA、Turing机等）。
- 忽略自动机与形式语言、可计算性理论的深度联系。
- 误将正则自动机与上下文无关自动机等价，未区分其表达能力。
- 忽视不可判定性、泵引理等核心定理的工程意义。

## 10.12.2 工程陷阱 Engineering Pitfalls #AutomataTheory-10.12.2

- 工程实现中，状态爆炸与不可扩展性问题被低估。
- 忽视边界条件与异常输入，导致自动机失效。
- 在多线程/并发系统中，未充分建模状态同步与转移，影响系统一致性。

## 10.12.3 三语言相关注意事项 Language-specific Notes #AutomataTheory-10.12.3

- Haskell：自动机建模需关注类型安全与递归定义。
- Rust：高性能自动机实现需关注内存安全与并发。
- Lean：形式化自动机证明需关注状态空间、转移函数与可判定性。

## 10.12.4 相关Tag

`# AutomataTheory #AutomataTheory-10 #AutomataTheory-10.12 #AutomataTheory-10.12.1 #AutomataTheory-10.12.2 #AutomataTheory-10.12.3`
