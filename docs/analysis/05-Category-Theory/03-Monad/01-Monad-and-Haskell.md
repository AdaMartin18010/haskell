# 01. 单子与Haskell类型系统（Monad and Haskell Type System）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1.1 单子简介（Introduction to Monad）

- **定义（Definition）**：
  - **中文**：在范畴论中，单子是一种在范畴上定义的三元组 $(T, \eta, \mu)$，用于描述带有上下文的计算和效应。Haskell中的Monad是对带有副作用的计算的抽象，支持顺序组合和上下文传递。
  - **English**: In category theory, a monad is a triple $(T, \eta, \mu)$ defined on a category, used to describe computations with context and effects. In Haskell, a Monad abstracts computations with effects, supporting sequential composition and context propagation.

- **Wiki风格国际化解释（Wiki-style Explanation）**：
  - 单子是Haskell类型系统中处理副作用、顺序计算和上下文传递的核心抽象。
  - Monad is the core abstraction in Haskell's type system for handling effects, sequential computation, and context propagation.

## 1.2 Haskell中的Monad类型类（Monad Typeclass in Haskell）

- **类型类定义（Typeclass Definition）**

```haskell
class Applicative m => Monad m where
  (>>=)  :: m a -> (a -> m b) -> m b
  return :: a -> m a
```

- **Kleisli范畴建模（Kleisli Category Modeling）**
  - 对象：类型 $a$
  - 态射：$a \to M b$
  - 单位：$return :: a \to M a$
  - 结合律：$(m >>= f) >>= g = m >>= (\x -> f x >>= g)$

- **Haskell代码示例**

```haskell
instance Monad Maybe where
  Nothing  >>= _ = Nothing
  (Just x) >>= f = f x
  return = Just

instance Monad [] where
  xs >>= f = concat (map f xs)
  return x = [x]
```

## 1.3 范畴论结构与类型系统的映射（Mapping Category Structure to Monad）

- **映射关系表（Mapping Table）**

| 范畴论概念 | Haskell概念 | 代码示例 | 中文解释 |
|---------|-------------|----------|----------|
| 对象    | 类型        | `Int`, `Maybe a` | 类型 |
| 态射    | `a -> m b`  | `\x -> Just (x+1)` | 带上下文的函数 |
| 单位    | `return`    | `return 3 :: Maybe Int` | 单位操作 |
| 结合    | `(>>=)`     | `Just 2 >>= (\x -> Just (x+1))` | 顺序组合 |

## 1.4 形式化证明与论证（Formal Proofs & Reasoning）

- **单子公理在Haskell中的体现**
  - **左单位律（Left Identity）**：
    - $return\ a >>= f = f\ a$
    - Haskell中：`return 3 >>= f == f 3`
  - **右单位律（Right Identity）**：
    - $m >>= return = m$
    - Haskell中：`m >>= return == m`
  - **结合律（Associativity）**：
    - $(m >>= f) >>= g = m >>= (\x -> f x >>= g)$
    - Haskell中：`((m >>= f) >>= g) == (m >>= (\x -> f x >>= g))`

- **证明示例（Proof Example）**

```haskell
-- 左单位律证明
let f x = Just (x + 1)
return 3 >>= f == f 3  -- True

-- 右单位律证明
Just 3 >>= return == Just 3  -- True

-- 结合律证明
let m = Just 2
let f x = Just (x + 1)
let g x = Just (x * 2)
((m >>= f) >>= g) == (m >>= (\x -> f x >>= g))  -- True
```

## 1.5 多表征与本地跳转（Multi-representation & Local Reference）

- **单子结构图（Monad Structure Diagram）**

```mermaid
graph TD
  A[类型 Type] --> B[带上下文的函数 a -> m b]
  B --> C[return 单位]
  B --> D[>>= 结合]
```

- **相关主题跳转**：
  - [范畴论与Haskell类型系统 Category Theory and Haskell Type System](../01-Category-Theory-and-Haskell-Type-System.md)
  - [函子 Functor](../02-Functor/01-Functor-and-Haskell.md)
  - [自然变换 Natural Transformation](../04-Natural-Transformation/01-Natural-Transformation-and-Haskell.md)

---

> 本文档为单子与Haskell类型系统的中英双语、Haskell语义模型与形式化证明规范化输出，适合学术研究与工程实践参考。
