# 条件表达式 (Conditional Expressions)

## 概述

条件表达式是Haskell控制流的基础，支持if-then-else、guards和case表达式等多种形式。本文档系统性介绍Haskell条件表达式的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [if-then-else表达式](#if-then-else表达式)
3. [守卫 (Guards)](#守卫-guards)
4. [case表达式](#case表达式)
5. [数学模型](#数学模型)
6. [Haskell实现](#haskell实现)
7. [最佳实践](#最佳实践)

## 基本概念

### 定义 1.1: 条件表达式 (Conditional Expression)

条件表达式根据布尔条件选择不同的分支进行求值。

### 语法

```haskell
if condition then expr1 else expr2
```

## if-then-else表达式

### 形式定义

$$
\text{if } b \text{ then } e_1 \text{ else } e_2 =
\begin{cases}
  e_1 & \text{if } b = \text{True} \\
  e_2 & \text{if } b = \text{False}
\end{cases}
$$

### Haskell示例

```haskell
max' :: Int -> Int -> Int
max' x y = if x > y then x else y
```

## 守卫 (Guards)

### 形式定义

守卫是带条件的函数分支：

```haskell
f x
  | p1 = e1
  | p2 = e2
  | otherwise = e3
```

### Haskell示例

```haskell
grade :: Int -> String
grade x
  | x >= 90 = "A"
  | x >= 80 = "B"
  | otherwise = "C"
```

## case表达式

### 形式定义

case表达式根据模式匹配选择分支：

```haskell
case expr of
  pattern1 -> result1
  pattern2 -> result2
  _        -> defaultResult
```

### Haskell示例

```haskell
safeHead :: [a] -> Maybe a
safeHead xs = case xs of
  [] -> Nothing
  (x:_) -> Just x
```

## 数学模型

### 条件表达式的语义

$$
\llbracket \text{if } b \text{ then } e_1 \text{ else } e_2 \rrbracket =
\begin{cases}
  \llbracket e_1 \rrbracket & \text{if } \llbracket b \rrbracket = \text{True} \\
  \llbracket e_2 \rrbracket & \text{if } \llbracket b \rrbracket = \text{False}
\end{cases}
$$

### case表达式的语义

$$
\llbracket \text{case } e \text{ of } p_i \rightarrow e_i \rrbracket =
\llbracket e_j \rrbracket \text{ where } p_j \sim \llbracket e \rrbracket
$$

## Haskell实现

### 综合示例

```haskell
absVal :: Int -> Int
absVal x = if x >= 0 then x else -x

sign :: Int -> String
sign x
  | x > 0 = "positive"
  | x < 0 = "negative"
  | otherwise = "zero"

safeTail :: [a] -> [a]
safeTail xs = case xs of
  [] -> []
  (_:ts) -> ts
```

## 最佳实践

1. **优先使用guards和case表达式**：提高代码可读性和模式匹配能力。
2. **避免嵌套if-then-else**：多分支时优先用guards或case。
3. **穷尽性检查**：确保所有可能分支都被覆盖。
4. **结合类型系统**：利用类型安全避免运行时错误。

## 相关链接

- [基础概念](../01-Basic-Concepts/README.md)
- [模式匹配](../02-Language-Features/03-Pattern-Matching.md)
- [类型系统](../02-Language-Features/01-Type-System.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
