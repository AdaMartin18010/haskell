# 10.12 常见误区 Common Pitfalls #AutomataTheory-10.12

## 10.12.1 理论误区 Theoretical Pitfalls #AutomataTheory-10.12.1

- 误将有限自动机能力等同于所有语言识别，忽视自动机模型的层级。
- 忽略自动机与文法的等价条件。

## 10.12.2 工程陷阱 Engineering Pitfalls #AutomataTheory-10.12.2

- 状态机设计不当，导致状态爆炸或死循环。
- 忽视输入边界与异常处理，易引发安全漏洞。

## 10.12.3 三语言相关注意事项 Language-specific Notes #AutomataTheory-10.12.3

- Haskell：递归实现自动机时需关注堆栈溢出与性能。
- Rust：状态机实现需关注内存与并发安全。
- Lean：形式化自动机证明需关注归纳假设的完备性。

## 10.12.4 相关Tag

`# AutomataTheory #AutomataTheory-10 #AutomataTheory-10.12 #AutomataTheory-10.12.1 #AutomataTheory-10.12.2 #AutomataTheory-10.12.3`
