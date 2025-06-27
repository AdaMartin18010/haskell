# 逻辑学 (Logic)

## 📚 目录

- [逻辑学 (Logic)](#逻辑学-logic)
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

逻辑学是研究推理、论证和真理的哲学与数学分支。它为科学、数学、计算机科学等领域提供了形式化的推理工具和理论基础。

## 主要分支

- 形式逻辑（Formal Logic）
- 数理逻辑（Mathematical Logic）
- 模态逻辑（Modal Logic）
- 非经典逻辑（Non-classical Logic）
- 归纳逻辑与概率逻辑（Inductive & Probabilistic Logic）

## 理论体系

- 命题逻辑（Propositional Logic）
- 谓词逻辑（Predicate Logic）
- 模态逻辑（Modal Logic）
- 时态逻辑（Temporal Logic）
- 直觉主义逻辑（Intuitionistic Logic）
- 归纳逻辑（Inductive Logic）

## Haskell实现

```haskell
-- 逻辑表达式类型定义（示例）
data Prop = Var String | Not Prop | And Prop Prop | Or Prop Prop | Implies Prop Prop deriving (Eq, Show)

eval :: [(String, Bool)] -> Prop -> Bool
eval env (Var x) = maybe False id (lookup x env)
eval env (Not p) = not (eval env p)
eval env (And p q) = eval env p && eval env q
eval env (Or p q) = eval env p || eval env q
eval env (Implies p q) = not (eval env p) || eval env q
```

## 理论证明

- 命题逻辑的完备性与一致性
- 谓词逻辑的可判定性
- 模态逻辑的可满足性

## 应用领域

- 数学证明
- 程序验证
- 人工智能推理
- 形式化规范与建模

## 相关理论

- [形而上学](./004-Metaphysics.md)
- [本体论](./003-Ontology.md)
- [认识论](./002-Epistemology.md)

## 参考文献

1. Church, A. (1940). *A Formulation of the Simple Theory of Types*.
2. Gentzen, G. (1935). *Investigations into Logical Deduction*.
3. Smullyan, R. (1995). *First-Order Logic*.
4. Enderton, H.B. (2001). *A Mathematical Introduction to Logic*.

---

**上一章**: [形而上学](./004-Metaphysics.md)  
**下一章**: [伦理学](./006-Ethics.md)
