# 9.1 形式语言理论的定义 Definition of Formal Language Theory #FormalLanguageTheory-9.1

## 中文定义

形式语言理论是理论计算机科学和数理逻辑的分支，研究符号串的集合（语言）、文法、自动机及其相互关系。它关注于语言的生成、识别、分类、语法结构、正则性、上下文无关性等核心概念。

## English Definition

Formal language theory is a branch of theoretical computer science and mathematical logic that studies sets of symbol strings (languages), grammars, automata, and their interrelations. It focuses on language generation, recognition, classification, syntactic structure, regularity, and context-freeness.

## 9.1.1 理论体系结构 Theoretical Framework #FormalLanguageTheory-9.1.1

- 语言（Languages）：符号串的集合。
- 文法（Grammars）：生成语言的规则系统（如正则文法、上下文无关文法）。
- 自动机（Automata）：识别语言的计算模型（如有限自动机、推理自动机）。
- 语言分类（Language Classes）：正则语言、上下文无关语言等。

## 9.1.2 形式化定义 Formalization #FormalLanguageTheory-9.1.2

- 形式语言L是某个字母表Σ上的符号串集合。
- 文法G = (N, Σ, P, S)，N为非终结符，Σ为终结符，P为产生式，S为开始符号。
- Haskell/Rust/Lean中，语言可用数据结构、类型、归纳定义等表达。

## 9.1.3 三语言对比 Haskell/Rust/Lean Comparison #FormalLanguageTheory-9.1.3

| 语言 | 语言建模 | 文法表达 | 自动机实现 | 工程应用 |
|------|----------|----------|------------|----------|
| Haskell | 数据类型/ADT | 代数数据类型/解析器组合子 | 有限自动机/解析器库 | 语法分析、DSL |
| Rust    | struct/enum   | trait/宏/解析器库 | 状态机/trait实现 | 语法分析、编译器 |
| Lean    | 归纳类型      | 归纳定义/递归 | 形式化自动机 | 形式化语言证明 |

## 9.1.4 相关Tag

`# FormalLanguageTheory #FormalLanguageTheory-9 #FormalLanguageTheory-9.1 #FormalLanguageTheory-9.1.1 #FormalLanguageTheory-9.1.2 #FormalLanguageTheory-9.1.3`
