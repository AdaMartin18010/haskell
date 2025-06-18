# 模式匹配 (Pattern Matching)

## 概述

模式匹配是Haskell的核心特性之一，用于数据解构、条件分支和函数定义。它提供了简洁、类型安全的方式来处理代数数据类型和递归结构。本文档系统性介绍Haskell模式匹配的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [模式类型](#模式类型)
3. [模式匹配语法](#模式匹配语法)
4. [模式匹配的数学模型](#模式匹配的数学模型)
5. [Haskell实现](#haskell实现)
6. [高级用法](#高级用法)
7. [最佳实践](#最佳实践)

## 基本概念

### 定义 3.1: 模式 (Pattern)

模式是用于匹配数据结构的结构化表达式。形式化地，模式 $p$ 可以是：

- 常量模式 $c$
- 变量模式 $x$
- 构造器模式 $C\ p_1\ ...\ p_n$
- 通配符模式 $_$

### 定义 3.2: 匹配 (Matching)

给定值 $v$ 和模式 $p$，匹配关系 $p \sim v$ 表示 $v$ 能被 $p$ 匹配，并产生绑定环境 $\theta$。

### 定义 3.3: 绑定环境 (Binding Environment)

绑定环境 $\theta$ 是变量到值的映射：
$$\theta : \text{Var} \rightarrow \text{Value}$$

## 模式类型

### 常见模式类型

- **常量模式**：匹配具体值，如 `0`, `True`
- **变量模式**：绑定任意值，如 `x`, `y`
- **构造器模式**：匹配代数数据类型的结构，如 `Just x`, `Left a`
- **元组/列表模式**：如 `(x, y)`, `[a, b, c]`
- **通配符模式**：`_`，忽略具体值
- **嵌套模式**：模式中嵌套其他模式，如 `Just (x:xs)`
- **as-模式**：`xs@(x:_)`，同时绑定整体和部分
- **守卫模式**：带条件判断的模式，如 `x | x > 0`

## 模式匹配语法

### 基本语法

```haskell
-- 函数定义中的模式匹配
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- case表达式
case expr of
  pattern1 -> result1
  pattern2 -> result2
  _        -> defaultResult

-- let绑定
let (x, y) = (1, 2) in x + y
```

### 复杂模式

```haskell
-- 列表模式
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- as-模式
firstAndRest xs@(x:_) = (x, xs)

-- 守卫模式
grade x
  | x >= 90 = "A"
  | x >= 80 = "B"
  | otherwise = "C"
```

## 模式匹配的数学模型

### 归纳定义

#### 定义 3.4: 匹配归纳规则

- $c \sim c \Rightarrow \{\}$
- $x \sim v \Rightarrow \{x \mapsto v\}$
- $C\ p_1\ ...\ p_n \sim C\ v_1\ ...\ v_n \Rightarrow \theta_1 \cup ... \cup \theta_n$
- $_ \sim v \Rightarrow \{\}$

### 定理 3.1: 匹配唯一性

对于无重叠的模式集，任意值 $v$ 最多被一个模式匹配。

### 证明

归纳法：

- 基础：常量、变量、通配符模式显然唯一
- 步骤：构造器模式递归唯一

### 语义模型

模式匹配可视为从值到结果的分段函数：
$$f(v) = \begin{cases}
  e_1 & \text{if } p_1 \sim v \\
  e_2 & \text{if } p_2 \sim v \\
  ... \\
  e_n & \text{if } p_n \sim v
\end{cases}$$

## Haskell实现

### 代数数据类型与模式匹配
```haskell
-- 代数数据类型
data List a = Nil | Cons a (List a)

data Tree a = Leaf | Node a (Tree a) (Tree a)

-- 列表长度
listLength :: List a -> Int
listLength Nil = 0
listLength (Cons _ xs) = 1 + listLength xs

-- 树深度
treeDepth :: Tree a -> Int
treeDepth Leaf = 0
treeDepth (Node _ l r) = 1 + max (treeDepth l) (treeDepth r)
```

### case表达式与嵌套模式
```haskell
-- case表达式
safeHead :: [a] -> Maybe a
safeHead xs = case xs of
  [] -> Nothing
  (x:_) -> Just x

-- 嵌套模式
sumTree :: Tree Int -> Int
sumTree Leaf = 0
sumTree (Node x l r) = x + sumTree l + sumTree r
```

### as-模式与守卫
```haskell
-- as-模式
describeList :: [a] -> String
describeList xs@[] = "Empty"
describeList xs@(x:_) = "Non-empty, first element: " ++ show x

-- 守卫
absVal :: Int -> Int
absVal x | x >= 0 = x
         | otherwise = -x
```

### 模式匹配失败与不可达分支
```haskell
-- 不可达分支
head' :: [a] -> a
head' (x:_) = x
head' [] = error "Empty list!"

-- 模式匹配失败处理
maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (x:_) = Just x
```

## 高级用法

### GADT与类型级模式匹配
```haskell
-- GADT示例
data Expr a where
  I :: Int -> Expr Int
  B :: Bool -> Expr Bool
  Add :: Expr Int -> Expr Int -> Expr Int
  Eq :: Expr Int -> Expr Int -> Expr Bool

-- 类型级模式匹配
eval :: Expr a -> a
eval (I n) = n
eval (B b) = b
eval (Add e1 e2) = eval e1 + eval e2
eval (Eq e1 e2) = eval e1 == eval e2
```

### View Patterns
```haskell
-- View Pattern扩展
{-# LANGUAGE ViewPatterns #-}

factorialView :: (Eq a, Num a) => a -> a
factorialView (\x -> x == 0 -> True) = 1
factorialView n = n * factorialView (n - 1)
```

### Pattern Synonyms
```haskell
-- Pattern Synonyms扩展
{-# LANGUAGE PatternSynonyms #-}

pattern Single x <- [x] where
  Single x = [x]

isSingle :: [a] -> Bool
isSingle (Single _) = True
isSingle _ = False
```

## 最佳实践

1. **穷尽性检查**：确保所有可能分支都被覆盖，避免运行时错误。
2. **避免重叠模式**：优先使用无重叠、无歧义的模式。
3. **使用as-模式和嵌套模式**：提高代码可读性和表达力。
4. **结合类型系统**：利用GADT和类型族实现类型安全的模式匹配。
5. **合理使用View Pattern和Pattern Synonyms**：增强模式表达能力。

## 总结

Haskell的模式匹配为函数式编程提供了强大、类型安全的数据解构能力。通过合理设计模式和类型，可以实现高效、健壮的程序。

## 相关链接

- [类型系统](./01-Type-System.md)
- [单子和效应](./02-Monads-and-Effects.md)
- [函数式编程基础](../01-Basic-Concepts/01-Functional-Programming.md)
- [语法理论](../../03-Theory/01-Programming-Language-Theory/02-Syntax-Theory.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
