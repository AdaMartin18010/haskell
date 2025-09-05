# 高阶函数 (Higher-Order Functions)

## 概述

高阶函数是Haskell函数式编程的核心特性之一，指接受函数作为参数或返回函数作为结果的函数。高阶函数极大提升了代码的抽象能力和复用性。本文档系统性介绍Haskell高阶函数的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [高阶函数的数学定义](#高阶函数的数学定义)
3. [常见高阶函数](#常见高阶函数)
4. [组合与管道](#组合与管道)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 3.1: 高阶函数 (Higher-Order Function)

高阶函数是指：

- 接受一个或多个函数作为参数，或
- 返回一个函数作为结果的函数。

### 形式类型

$$
f : (A \rightarrow B) \rightarrow C
$$
或
$$
f : A \rightarrow (B \rightarrow C)
$$

## 高阶函数的数学定义

### Lambda演算

高阶函数可用lambda演算表达：
$$
\lambda f. f\ x
$$

### 组合子

- 恒等组合子：$I = \lambda x. x$
- 组合组合子：$B = \lambda f\ g\ x. f (g x)$
- 翻转组合子：$C = \lambda f\ x\ y. f y x$

## 常见高阶函数

### map

```haskell
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
```

### filter

```haskell
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs
```

### foldr / foldl

```haskell
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ z [] = z
foldl f z (x:xs) = foldl f (f z x) xs
```

### compose

```haskell
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)
```

## 组合与管道

### 函数组合

```haskell
-- 组合两个函数
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- 多函数组合
compose3 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
compose3 f g h x = f (g (h x))
```

### 管道操作

```haskell
-- 管道风格
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 示例
result = [1,2,3] |> map (+1) |> filter even
```

## Haskell实现

### 综合示例

```haskell
-- map
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- filter
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs

-- foldr
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

-- 函数组合
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- 匿名函数
addOne = \x -> x + 1

-- 高阶函数应用
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

-- 示例
example = applyTwice (+1) 3  -- 结果: 5
```

## 最佳实践

1. **优先使用高阶函数**：如map、filter、fold等，减少显式递归。
2. **组合小函数**：通过函数组合提升代码复用性。
3. **利用匿名函数**：简化一次性操作。
4. **管道风格**：提升代码可读性。
5. **类型注解**：为高阶函数添加类型签名，增强类型安全。

## 相关链接

- [递归函数](./02-Recursive-Functions.md)
- [条件表达式](./01-Conditional-Expressions.md)
- [基础概念](../01-Basic-Concepts/README.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
