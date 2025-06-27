# 范畴论基础 (Category Theory Foundations)

## 📚 概述

范畴论是现代数学和计算机科学的基础理论，研究对象与态射及其结构。本文档建立范畴论的完整数学基础，并提供 Haskell 实现。

## 🎯 核心概念

### 1. 范畴定义

**定义 1.1.1** 范畴 $\mathcal{C}$ 包含：

- 对象集 $\text{Ob}(\mathcal{C})$
- 态射集 $\text{Hom}(A, B)$
- 复合运算 $\circ$
- 单位态射 $\text{id}_A$

满足：

1. 结合律：$(f \circ g) \circ h = f \circ (g \circ h)$
2. 单位律：$\text{id}_B \circ f = f = f \circ \text{id}_A$

```haskell
-- 范畴类型
data Category obj morph = Category
  { objects :: Set obj
  , morphisms :: obj -> obj -> Set morph
  , compose :: morph -> morph -> Maybe morph
  , identity :: obj -> morph
  }

-- 范畴性质检查
isCategory :: (Ord obj, Ord morph, Eq morph) => Category obj morph -> Bool
isCategory cat = ... -- 见数学基础文档
```

### 2. 态射与函子

**定义 2.1.1** 态射是对象之间的结构保持映射。

**定义 2.2.1** 函子 $F: \mathcal{C} \to \mathcal{D}$ 包含：

- 对象映射 $F: \text{Ob}(\mathcal{C}) \to \text{Ob}(\mathcal{D})$
- 态射映射 $F: \text{Hom}_\mathcal{C}(A, B) \to \text{Hom}_\mathcal{D}(F(A), F(B))$

满足：

- $F(\text{id}_A) = \text{id}_{F(A)}$
- $F(g \circ f) = F(g) \circ F(f)$

```haskell
-- 函子类型
data Functor obj1 morph1 obj2 morph2 = Functor
  { objectMap :: obj1 -> obj2
  , morphismMap :: morph1 -> morph2
  }
```

### 3. 自然变换

**定义 3.1.1** 自然变换 $\eta: F \Rightarrow G$ 是对每个对象 $A$，有 $\eta_A: F(A) \to G(A)$，使得对任意 $f: A \to B$，有 $G(f) \circ \eta_A = \eta_B \circ F(f)$。

```haskell
-- 自然变换类型
data NaturalTransformation obj1 morph1 obj2 morph2 = NaturalTransformation
  { sourceFunctor :: Functor obj1 morph1 obj2 morph2
  , targetFunctor :: Functor obj1 morph1 obj2 morph2
  , components :: obj1 -> morph2
  }
```

### 4. 重要范畴

- **集合范畴** ($\mathbf{Set}$)：对象为集合，态射为函数
- **预序集范畴** ($\mathbf{Pos}$)：对象为偏序集，态射为单调函数
- **单子范畴** ($\mathbf{Mon}$)：对象为单子，态射为单子态射

### 5. 单子与应用

**定义 5.1.1** 单子 $(T, \eta, \mu)$ 包含函子 $T$ 及自然变换 $\eta, \mu$，满足结合律和单位律。

```haskell
-- 单子类型类
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- 单子定律
-- 见 Haskell Prelude 文档
```

### 6. 范畴论与计算机科学

- **类型系统**：类型范畴
- **函数式编程**：函子、单子
- **语义学**：指称语义范畴化

## 🔗 交叉引用

- [[002-Mathematical-Foundations]]
- [[005-Denotational-Semantics]]
- [[008-Category-Semantics]]

## 📚 参考文献

1. Mac Lane, S. (1998). Categories for the Working Mathematician.
2. Awodey, S. (2010). Category Theory.

---

**最后更新**: 2024年12月19日
