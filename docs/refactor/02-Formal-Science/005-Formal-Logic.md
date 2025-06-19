# 形式逻辑基础 (Formal Logic Foundations)

## 📚 概述

形式逻辑是数学和计算机科学的基础，研究命题、谓词、证明、推理等。本文档建立形式逻辑的完整理论体系，并提供 Haskell 实现。

## 🎯 核心概念

### 1. 命题逻辑

**定义 1.1.1** 命题逻辑的语法：

- 命题变元 $p, q, r$
- 连接词 $\neg, \wedge, \vee, \rightarrow, \leftrightarrow$

**定义 1.1.2** 语义赋值 $v: \text{Var} \to \{\text{True}, \text{False}\}$

```haskell
data Prop = Var String | Not Prop | And Prop Prop | Or Prop Prop | Implies Prop Prop | Iff Prop Prop

-- 语义赋值
evalProp :: Prop -> (String -> Bool) -> Bool
evalProp p env = ...
```

### 2. 谓词逻辑

**定义 2.1.1** 谓词逻辑的语法：

- 变元、常量、函数、谓词、量词 $\forall, \exists$

```haskell
data Term = TVar String | TConst String | TFunc String [Term]
data Formula = Atom String [Term] | NotF Formula | AndF Formula Formula | OrF Formula Formula | ImpliesF Formula Formula | Forall String Formula | Exists String Formula

-- 语义赋值
evalFormula :: Formula -> (String -> Domain) -> (String -> Domain -> Bool) -> Bool
evalFormula f env pred = ...
```

### 3. 证明系统

- **自然演绎**、**公理系统**、**序列演算**

### 4. 可判定性与复杂性

- **可判定性**：有算法判定真值
- **复杂性**：SAT 问题 NP 完全

### 5. 逻辑与类型

- Curry-Howard 对应
- 依赖类型、证明助理

## 🔗 交叉引用

- [[002-Mathematical-Foundations]]
- [[001-Formal-Language-Theory]]
- [[007-Axiomatic-Semantics]]

## 📚 参考文献

1. Enderton, H. B. (2001). A Mathematical Introduction to Logic.
2. Pierce, B. C. (2002). Types and Programming Languages.

---

**最后更新**: 2024年12月19日
