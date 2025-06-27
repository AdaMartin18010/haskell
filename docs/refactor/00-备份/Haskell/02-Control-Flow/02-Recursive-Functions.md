# 递归函数 (Recursive Functions)

## 概述

递归是Haskell函数式编程的核心机制之一，用于定义自引用的计算过程。递归函数通过自身调用实现循环、结构遍历和分治算法。本文档系统性介绍Haskell递归函数的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [递归函数的数学定义](#递归函数的数学定义)
3. [基本递归模式](#基本递归模式)
4. [尾递归与优化](#尾递归与优化)
5. [结构递归与模式匹配](#结构递归与模式匹配)
6. [Haskell实现](#haskell实现)
7. [最佳实践](#最佳实践)

## 基本概念

### 定义 2.1: 递归函数 (Recursive Function)

递归函数是直接或间接调用自身的函数。

### 递归的基本结构

```haskell
f x = if p(x) then base(x) else step(x, f (next(x)))
```

## 递归函数的数学定义

### 归纳定义

递归函数 $f$ 满足：

- 基础情况 (Base Case): $f(x_0) = a$
- 递归情况 (Recursive Case): $f(x) = g(x, f(h(x)))$

### 递归方程示例

- 阶乘: $f(0) = 1$, $f(n) = n \times f(n-1)$
- 斐波那契: $f(0) = 0$, $f(1) = 1$, $f(n) = f(n-1) + f(n-2)$

## 基本递归模式

### 线性递归

```haskell
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)
```

### 树形递归

```haskell
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)
```

### 结构递归

```haskell
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs
```

## 尾递归与优化

### 定义 2.2: 尾递归 (Tail Recursion)

尾递归是指递归调用是函数的最后一步。

### 尾递归优化

Haskell编译器可将尾递归优化为迭代，减少栈空间消耗。

### 尾递归示例

```haskell
factorialTR :: Int -> Int
factorialTR n = go n 1
  where
    go 0 acc = acc
    go k acc = go (k - 1) (k * acc)
```

## 结构递归与模式匹配

### 递归遍历代数数据类型

```haskell
treeSum :: Tree Int -> Int
treeSum Leaf = 0
treeSum (Node x l r) = x + treeSum l + treeSum r
```

## Haskell实现

### 综合示例

```haskell
-- 阶乘
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 尾递归阶乘
factorialTR :: Int -> Int
factorialTR n = go n 1
  where
    go 0 acc = acc
    go k acc = go (k - 1) (k * acc)

-- 斐波那契
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

-- 列表求和
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs

-- 树结构
data Tree a = Leaf | Node a (Tree a) (Tree a)

treeSum :: Tree Int -> Int
treeSum Leaf = 0
treeSum (Node x l r) = x + treeSum l + treeSum r
```

## 最佳实践

1. **优先使用尾递归**：提高性能，避免栈溢出。
2. **结合模式匹配**：简化递归结构，提升可读性。
3. **利用高阶函数**：如foldr、foldl等替代显式递归。
4. **递归终止条件明确**：确保每次递归都趋向于终止。
5. **避免重复计算**：如斐波那契数列可用记忆化优化。

## 相关链接

- [条件表达式](./01-Conditional-Expressions.md)
- [高阶函数](./03-Higher-Order-Functions.md)
- [基础概念](../01-Basic-Concepts/README.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
