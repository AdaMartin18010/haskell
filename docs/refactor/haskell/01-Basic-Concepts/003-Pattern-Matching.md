# 模式匹配

## 📋 概述

模式匹配是Haskell的核心特性之一，它允许根据数据结构的形式进行分支处理。模式匹配不仅提供了强大的控制流能力，还确保了类型安全和代码的可读性。

## 🎯 基本概念

### 定义 1.1 (模式匹配)

模式匹配是一种控制结构，它根据数据构造器的形式将值分解并绑定到变量。在Haskell中，模式匹配是函数定义的主要方式。

```haskell
-- 基本模式匹配
factorial :: Integer -> Integer
factorial 0 = 1
factorial n = n * factorial (n - 1)

-- 列表模式匹配
sumList :: [Int] -> Int
sumList [] = 0
sumList (x:xs) = x + sumList xs
```

## 🔧 模式类型

### 1. 常量模式

**定义 1.2 (常量模式)**
常量模式匹配特定的值。

```haskell
-- 数字常量
isZero :: Int -> Bool
isZero 0 = True
isZero _ = False

-- 字符常量
isVowel :: Char -> Bool
isVowel 'a' = True
isVowel 'e' = True
isVowel 'i' = True
isVowel 'o' = True
isVowel 'u' = True
isVowel _ = False

-- 布尔常量
not :: Bool -> Bool
not True = False
not False = True
```

### 2. 变量模式

**定义 1.3 (变量模式)**
变量模式匹配任何值并将其绑定到变量。

```haskell
-- 简单变量绑定
identity :: a -> a
identity x = x

-- 忽略值（通配符）
const :: a -> b -> a
const x _ = x

-- 多个变量
swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
```

### 3. 构造器模式

**定义 1.4 (构造器模式)**
构造器模式匹配代数数据类型的构造器。

```haskell
-- 代数数据类型
data Color = Red | Green | Blue | RGB Int Int Int

-- 构造器模式匹配
colorName :: Color -> String
colorName Red = "Red"
colorName Green = "Green"
colorName Blue = "Blue"
colorName (RGB r g b) = "RGB(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ ")"

-- 列表构造器
data List a = Nil | Cons a (List a)

-- 列表模式匹配
listLength :: List a -> Int
listLength Nil = 0
listLength (Cons _ xs) = 1 + listLength xs
```

### 4. 元组模式

**定义 1.5 (元组模式)**
元组模式匹配元组结构。

```haskell
-- 二元组
fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

-- 三元组
third :: (a, b, c) -> c
third (_, _, z) = z

-- 嵌套元组
nestedTuple :: ((a, b), c) -> (a, c)
nestedTuple ((x, _), z) = (x, z)
```

### 5. 记录模式

**定义 1.6 (记录模式)**
记录模式匹配记录类型的字段。

```haskell
-- 记录类型
data Person = Person 
    { name :: String
    , age :: Int
    , city :: String
    }

-- 记录模式匹配
isAdult :: Person -> Bool
isAdult (Person _ age _) = age >= 18

getName :: Person -> String
getName (Person name _ _) = name

-- 部分记录匹配
updateAge :: Person -> Int -> Person
updateAge (Person name _ city) newAge = Person name newAge city
```

## 🔍 高级模式匹配

### 1. 嵌套模式

**定义 1.7 (嵌套模式)**
嵌套模式允许在模式内部使用模式。

```haskell
-- 嵌套列表模式
deepSum :: [[Int]] -> Int
deepSum [] = 0
deepSum ([]:xss) = deepSum xss
deepSum ((x:xs):xss) = x + deepSum (xs:xss)

-- 嵌套元组模式
complexPattern :: ((Int, String), Bool) -> String
complexPattern ((n, s), True) = s ++ " is " ++ show n
complexPattern ((n, s), False) = s ++ " is not " ++ show n
```

### 2. 模式守卫

**定义 1.8 (模式守卫)**
模式守卫允许在模式匹配中使用条件表达式。

```haskell
-- 使用模式守卫
absolute :: Int -> Int
absolute x
    | x < 0 = -x
    | otherwise = x

-- 复杂条件
grade :: Int -> String
grade score
    | score >= 90 = "A"
    | score >= 80 = "B"
    | score >= 70 = "C"
    | score >= 60 = "D"
    | otherwise = "F"
```

### 3. 视图模式

**定义 1.9 (视图模式)**
视图模式允许在模式匹配中使用函数。

```haskell
-- 视图模式（需要扩展）
{-# LANGUAGE ViewPatterns #-}

-- 使用视图模式
isEven :: Int -> Bool
isEven n = n `mod` 2 == 0

processEven :: Int -> String
processEven (isEven -> True) = "Even number"
processEven (isEven -> False) = "Odd number"
```

## 📊 模式匹配的数学基础

### 代数数据类型

**定义 1.10 (代数数据类型)**
代数数据类型是Haskell中定义数据结构的方式，它对应于数学中的和类型（sum types）和积类型（product types）。

```haskell
-- 和类型（枚举）
data Bool = True | False

-- 积类型（记录）
data Point = Point Double Double

-- 递归类型
data Tree a = Empty | Node a (Tree a) (Tree a)
```

### 模式匹配的形式语义

**定理 1.1 (模式匹配的完备性)**
对于任何代数数据类型，模式匹配可以覆盖所有可能的构造器。

**证明**：
设 $T$ 是一个代数数据类型，其构造器为 $C_1, C_2, \ldots, C_n$。
对于函数 $f: T \rightarrow A$，我们可以定义：
```haskell
f :: T -> A
f (C1 x1 ... xk1) = e1
f (C2 x1 ... xk2) = e2
...
f (Cn x1 ... xkn) = en
```

这确保了所有可能的构造器都被处理。

## 🔧 实际应用

### 1. 解析器

```haskell
-- 简单表达式解析器
data Expr = 
    Lit Int
    | Add Expr Expr
    | Mul Expr Expr

-- 模式匹配求值
eval :: Expr -> Int
eval (Lit n) = n
eval (Add e1 e2) = eval e1 + eval e2
eval (Mul e1 e2) = eval e1 * eval e2

-- 使用示例
expr = Add (Lit 3) (Mul (Lit 4) (Lit 5))
result = eval expr  -- 23
```

### 2. 状态机

```haskell
-- 状态机定义
data State = Idle | Running | Paused | Stopped
data Event = Start | Pause | Resume | Stop

-- 状态转换
transition :: State -> Event -> State
transition Idle Start = Running
transition Running Pause = Paused
transition Running Stop = Stopped
transition Paused Resume = Running
transition Paused Stop = Stopped
transition _ _ = error "Invalid transition"
```

### 3. 错误处理

```haskell
-- 错误类型
data Result a = Success a | Error String

-- 模式匹配处理
handleResult :: Result Int -> String
handleResult (Success value) = "Success: " ++ show value
handleResult (Error message) = "Error: " ++ message

-- 安全操作
safeDivide :: Int -> Int -> Result Int
safeDivide _ 0 = Error "Division by zero"
safeDivide x y = Success (x `div` y)
```

## 🎯 最佳实践

### 1. 穷尽性检查

```haskell
-- 好的做法：覆盖所有情况
data Direction = North | South | East | West

directionToString :: Direction -> String
directionToString North = "North"
directionToString South = "South"
directionToString East = "East"
directionToString West = "West"

-- 编译器会检查是否覆盖了所有情况
```

### 2. 模式顺序

```haskell
-- 好的做法：具体模式在前
processList :: [Int] -> String
processList [] = "Empty"
processList [x] = "Single: " ++ show x
processList (x:y:xs) = "Multiple: " ++ show x ++ ", " ++ show y

-- 避免重叠模式
```

### 3. 使用通配符

```haskell
-- 好的做法：使用通配符忽略不需要的值
getFirst :: (a, b, c) -> a
getFirst (x, _, _) = x

-- 避免绑定未使用的变量
```

## 🔗 相关链接

### 理论基础
- [代数数据类型](../04-Type-System/002-Algebraic-Data-Types.md)
- [类型系统理论](../03-Theory/01-Programming-Language-Theory/004-Type-System-Theory.md)
- [函数式编程理论](../03-Theory/01-Programming-Language-Theory/002-Functional-Programming-Theory.md)

### 实际应用
- [控制流](./02-Control-Flow/001-Control-Structures.md)
- [数据流](./03-Data-Flow/001-Data-Transformation.md)
- [类型系统](./04-Type-System/001-Type-Definitions.md)

### 高级特性
- [设计模式](./05-Design-Patterns/001-Functional-Patterns.md)
- [并发编程](./08-Concurrency/001-Concurrent-Programming.md)
- [性能优化](./09-Performance/001-Algorithm-Optimization.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队 