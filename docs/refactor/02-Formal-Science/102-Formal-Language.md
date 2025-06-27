# 形式语言 (Formal Language)

## 📚 目录

- [形式语言 (Formal Language)](#形式语言-formal-language)
  - [📚 目录](#-目录)
  - [概述](#概述)
  - [主要分支](#主要分支)
  - [理论体系](#理论体系)
  - [Haskell实现](#haskell实现)
  - [理论证明](#理论证明)
  - [应用领域](#应用领域)
  - [相关理论](#相关理论)
  - [参考文献](#参考文献)

## 概述

形式语言是研究符号系统、语法规则和语言结构的理论体系，是计算机科学、语言学和逻辑学的基础。

## 主要分支

- 正则语言（Regular Languages）
- 无上下文语言（Context-Free Languages）
- 上下文相关语言（Context-Sensitive Languages）
- 递归可枚举语言（Recursively Enumerable Languages）
- 形式文法与自动机理论

## 理论体系

- 形式文法（Chomsky Hierarchy）
- 有限自动机（Finite Automata）
- 推理系统与归纳法
- 语言的生成与识别
- 语法分析与语义解释

## Haskell实现

```haskell
-- 有限自动机的基本定义（示例）
data State = Q0 | Q1 | Q2 deriving (Eq, Show)
data Symbol = A | B deriving (Eq, Show)
type Transition = (State, Symbol, State)

type DFA = ([State], [Symbol], [Transition], State, [State])

accepts :: DFA -> [Symbol] -> Bool
accepts (states, alphabet, transitions, start, finals) input =
  let step s [] = s
      step s (x:xs) = case [t | t@(from, sym, to) <- transitions, from == s, sym == x] of
        ((_, _, to):_) -> step to xs
        _ -> s
      finalState = step start input
  in finalState `elem` finals
```

## 理论证明

- 正则语言的封闭性证明
- 泵引理（Pumping Lemma）
- 语言等价性判定

## 应用领域

- 编译原理与语法分析
- 计算机语言设计
- 形式化验证与模型检测
- 自然语言处理

## 相关理论

- [数学基础](./101-Mathematical-Foundations.md)
- [逻辑系统](./103-Logical-Systems.md)
- [哲学基础](../01-Philosophy/README.md)

## 参考文献

1. Chomsky, N. (1956). *Three Models for the Description of Language*.
2. Hopcroft, J.E., Motwani, R., Ullman, J.D. (2006). *Introduction to Automata Theory, Languages, and Computation*.
3. Sipser, M. (2012). *Introduction to the Theory of Computation*.
4. Kozen, D. (1997). *Automata and Computability*.

---

**上一章**: [数学基础](./101-Mathematical-Foundations.md)  
**下一章**: [逻辑系统](./103-Logical-Systems.md)
